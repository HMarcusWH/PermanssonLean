"""Exact 45-case plus 11-claim theorem inventory and pinned-Lean exporter.

The canonical 45-case ledger holds 290 historical declaration references
(typically short names); the 11-claim inventory holds fully qualified
supporting names. This module resolves them in their ACTUAL source files
before querying Lean's Environment for authoritative elaborated types and
transitive axioms. Lexical discovery can only propose a qualified name.
Compiler output is authoritative; any ambiguous/missing original declaration
is a BLOCKER, never silently dropped.

Evidence remains detached, unreviewed and WITHOUT a fabricated CI check ID.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from closure_elaborated_type import (
    lean_probe, compiled_type_record, elaborated_type_sha256, TypeEvidenceError,
)
from final_closure_case_receipts import parse_target_axioms, EvidenceError
from final_closure_lean_evidence import run_probe, parse_axioms

ROOT = Path(__file__).resolve().parents[2]
SNAP = ROOT / "research/paper_closures/post_merge_112"
SHA40 = re.compile(r"^[0-9a-f]{40}$")


class CompleteCompilerError(ValueError):
    pass


def require(ok, message):
    if not ok:
        raise CompleteCompilerError(message)


def sha(raw: bytes):
    return hashlib.sha256(raw).hexdigest()


def load(path: Path):
    obj = json.loads(path.read_bytes())
    require(isinstance(obj, dict), "invalid source obligation JSON")
    return obj



LEAN_NAME = r"[A-Za-z_][A-Za-z0-9_']*"
# A declaration may be a public structure member written as
# "theorem Structure.member". Truncating the dotted name to "Structure"
# manufactures duplicate public names and drops the actual theorem owner.
QUALIFIED_LEAN_NAME = LEAN_NAME + r"(?:\." + LEAN_NAME + r")*"
DECLARATION = re.compile(
    r"^[ \t]*(?:(?:protected|private|noncomputable|unsafe|partial|opaque)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
    r"(" + QUALIFIED_LEAN_NAME + r")(?![A-Za-z0-9_'.])"
)
PREFIX = re.compile(
    r"^[ \t]*(?P<flags>(?:(?:protected|private|noncomputable|unsafe|partial|opaque)\s+)*)"
    r"(?:theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+"
)
OPEN_NAMESPACE = re.compile(r"^[ \t]*namespace[ \t]+([A-Za-z0-9_.']+)(?:\s|$)")
CLOSE_SCOPE = re.compile(r"^[ \t]*end(?:[ \t]+([A-Za-z0-9_.']+))?(?:\s|$)")


def addressable_declarations(source: str):
    """Find only ordinary qualified Lean owner candidates.

    Other modules may legitimately have private local lemmas, anonymous
    instances or proof-local helpers. These must NOT invalidate an unrelated
    pinned public declaration. Private names are excluded because Lean mangles
    their exported identifiers; requests for such a source pin fail closed.
    Comments are hidden before interpreting scope or theorem declarations.
    Compiler elaboration, not this index, remains authoritative.
    """
    if not isinstance(source, str):
        raise CompleteCompilerError("invalid original source text")
    stack = []
    found = []
    block_depth = 0
    for original in source.splitlines():
        # Lean permits nested block comments. Mask comments, preserving
        # all noncomment text only when outside comment blocks.
        line = []
        pos = 0
        while pos < len(original):
            ahead = original[pos:pos+2]
            if ahead == "/-":
                block_depth += 1
                pos += 2
            elif block_depth and ahead == "-/":
                block_depth -= 1
                pos += 2
            elif block_depth:
                pos += 1
            elif ahead == "--":
                break
            else:
                line.append(original[pos])
                pos += 1
        clean = "".join(line).strip()
        if not clean:
            continue
        opened = OPEN_NAMESPACE.match(clean)
        if opened:
            stack.append(opened.group(1))
            continue
        closed = CLOSE_SCOPE.match(clean)
        if closed:
            name = closed.group(1)
            if stack and (
                name == stack[-1] or
                name == stack[-1].split(".")[-1] or
                name == ".".join(stack)
            ):
                if name == ".".join(stack):
                    stack.clear()
                else:
                    stack.pop()
            continue
        declaration = DECLARATION.match(clean)
        if declaration:
            prefix = PREFIX.match(clean)
            if prefix is not None and "private" in prefix.group("flags").split():
                continue
            local = declaration.group(1)
            found.append(".".join(stack + [local]) if stack else local)
    if block_depth != 0:
        raise CompleteCompilerError("unterminated Lean source comment")
    if len(found) != len(set(found)):
        repeated = sorted(name for name in set(found) if found.count(name) > 1)
        raise CompleteCompilerError("duplicate public declaration source name: " +
                                    repr(repeated))
    return found


def source_declarations(root: Path, relative: str, cache: dict):
    if relative not in cache:
        require(isinstance(relative, str) and
                relative.startswith("PermanssonResearch/") and
                relative.endswith(".lean") and
                "\\" not in relative and
                ".." not in Path(relative).parts,
                "untrusted historical theorem path")
        src = (root / relative).resolve()
        require(src.is_relative_to(root.resolve()) and
                src.is_file() and not src.is_symlink(),
                "missing/hijacked original Lean module: " + relative)
        try:
            fqns = addressable_declarations(src.read_text(encoding="utf-8"))
        except CompleteCompilerError as exc:
            raise CompleteCompilerError(relative + ": " + str(exc)) from exc
        cache[relative] = (src, fqns)
    return cache[relative]


def resolved_name(root: Path, relative: str, short_name: str, cache: dict):
    require(isinstance(short_name, str) and short_name and
            not any(c.isspace() for c in short_name),
            "invalid original declaration name")
    _, known = source_declarations(root, relative, cache)
    if short_name in known:
        return short_name
    options = [fqn for fqn in known if fqn.endswith("." + short_name)]
    require(len(options) == 1,
            "unresolved/ambiguous original Lean declaration: " +
            relative + ":" + short_name + " -> " + repr(options))
    return options[0]


def required_inventory(*, root=ROOT, case_map=None, claim_map=None):
    """Deterministic union of every original and supporting declaration."""
    case_map = load(SNAP / "acceptance_case_source_map.json") if case_map is None else case_map
    claim_map = load(SNAP / "claim_declaration_map.json") if claim_map is None else claim_map
    cases = case_map.get("cases")
    claims = claim_map.get("claims")
    require(isinstance(cases, list) and len(cases) == 45 and
            isinstance(claims, list) and len(claims) == 11,
            "original 45/11 inventory incomplete")
    all_cases, all_claims = set(), set()
    ownership = {}
    cache = {}
    def add(path, name, *, case=None, claim=None):
        fqn = resolved_name(root, path, name, cache)
        key = (path, fqn)
        if key not in ownership:
            ownership[key] = {"path": path, "declaration": fqn,
                              "case_ids": set(), "claim_ids": set()}
        if case is not None:
            ownership[key]["case_ids"].add(case)
        if claim is not None:
            ownership[key]["claim_ids"].add(claim)
    for case in cases:
        require(isinstance(case, dict), "malformed case obligation")
        cid = case.get("case_id")
        require(isinstance(cid, str) and cid not in all_cases,
                "duplicate/invalid original case ID")
        all_cases.add(cid)
        entries = case.get("historical_proof_declarations")
        require(isinstance(entries, list) and entries,
                "case missing mandatory original theorems: " + cid)
        for entry in entries:
            require(isinstance(entry, dict), "malformed case theorem obligation")
            add(entry.get("path"), entry.get("name"), case=cid)
    claim_expected = {"Q1", "Q2", "Q3", "M1", "M2", "M3", "N1", "N2", "N3", "D8", "D9"}
    for claim in claims:
        require(isinstance(claim, dict), "malformed claim obligation")
        cid = claim.get("claim_id")
        require(isinstance(cid, str) and cid not in all_claims,
                "invalid/duplicate claim identifier")
        all_claims.add(cid)
        entries = claim.get("declarations")
        require(isinstance(entries, list) and entries,
                "claim missing supporting theorem: " + str(cid))
        for entry in entries:
            require(isinstance(entry, dict), "malformed claim theorem")
            add(entry.get("path"), entry.get("declaration"), claim=cid)
    require(all_claims == claim_expected and len(all_cases) == 45,
            "exact 45/11 source-owner identities required")
    return [
        {**entry, "case_ids": sorted(entry["case_ids"]),
         "claim_ids": sorted(entry["claim_ids"])}
        for key, entry in sorted(ownership.items())
    ]


def git_head():
    try:
        return subprocess.check_output(["git", "rev-parse", "HEAD"],
                                       cwd=ROOT, text=True,
                                       stderr=subprocess.DEVNULL,
                                       timeout=30).strip()
    except (OSError, subprocess.CalledProcessError, subprocess.TimeoutExpired) as exc:
        raise CompleteCompilerError("untrusted Git HEAD") from exc


def inventory_digest(entries: list[dict]) -> str:
    """Bind all shards to exactly the same sorted source-owner map."""
    raw = json.dumps(entries, ensure_ascii=False, sort_keys=True,
                     separators=(",", ":")).encode("utf-8")
    return sha(raw)


def shard_indices(total: int, shard_index: int, shard_count: int):
    if (type(total) is not int or total < 1 or
        type(shard_index) is not int or
        type(shard_count) is not int or
        not 1 <= shard_count <= 16 or
        not 0 <= shard_index < shard_count or shard_count > total):
        raise CompleteCompilerError("invalid compiler shard configuration")
    return [idx for idx in range(total) if idx % shard_count == shard_index]


def export_all(head: str, output: Path, *,
               shard_index: int = 0, shard_count: int = 1):
    require(isinstance(head, str) and SHA40.fullmatch(head) and
            git_head() == head, "compiler checkout differs from requested H")
    output = output.resolve()
    require(not output.is_relative_to(ROOT.resolve()),
            "compiler logs must be detached from the reviewed checkout")
    manifest = required_inventory()
    require(len(manifest) > 11, "original proof dependency graph is missing")
    selected_indices = shard_indices(len(manifest), shard_index, shard_count)
    manifest_digest = inventory_digest(manifest)
    output.mkdir(parents=True, exist_ok=False)
    (output / "axiom_logs").mkdir()
    receipts = []
    for idx in selected_indices:
        required = manifest[idx]
        src = (ROOT / required["path"]).resolve()
        module = required["path"][:-5].replace("/", ".")
        declaration = required["declaration"]
        code = lean_probe(module, declaration)
        with tempfile.TemporaryDirectory(prefix="perm-case-compiler-",
                                         dir=ROOT / ".lake") as td:
            probe = Path(td) / "Proof.lean"
            probe.write_text(code, encoding="utf-8")
            result = run_probe(probe)
        data = (result.stdout + "\n" + result.stderr).encode("utf-8")
        require(result.returncode == 0, "compiler rejected mandatory source theorem: " +
                declaration + "\n" + data[-500:].decode("utf-8", "replace"))
        require(len(data) <= 4*1024*1024, "compiler theorem log too large")
        text = data.decode("utf-8")
        try:
            elaborated = compiled_type_record(text, declaration)
            axioms = parse_axioms(text, declaration)
        except (TypeEvidenceError, EvidenceError, RuntimeError) as exc:
            raise CompleteCompilerError(
                "unverifiable compiler declaration: " + declaration) from exc
        member = f"axiom_logs/all_{idx:04}.log"
        (output / member).write_bytes(data)
        receipts.append({
            "id": f"all:{idx:04}", "inventory_index": idx,
            "head_sha": head,
            "path": required["path"],
            "declaration": declaration,
            "case_ids": required["case_ids"],
            "claim_ids": required["claim_ids"],
            "source_sha256": sha(src.read_bytes()),
            "elaborated_type_sha256": elaborated_type_sha256(elaborated),
            "declaration_kind": elaborated["declaration_kind"],
            "universe_params_repr": elaborated["universe_params_repr"],
            "transitive_axioms": axioms,
            "compiler_result": "PASS", "compiler_check": "research",
            "axiom_log_member": member, "axiom_log_sha256": sha(data),
            "check_run_id": None,
        })
    report = {
        "format": "Permansson.AllCaseCompilerCandidate.v1",
        "status": "COMPILER_ONLY_UNREVIEWED",
        "head_sha": head,
        "proof_count": len(receipts),
        "inventory_count": len(manifest),
        "inventory_sha256": manifest_digest,
        "shard_index": shard_index, "shard_count": shard_count,
        "case_count": 45, "claim_count": 11,
        "compiler_axiom_receipts": receipts,
        "independent_review": False,
        "authentic_ci_job_bound": False,
        "merged_main_sha": None,
    }
    (output / "complete_compiler_candidate.json").write_text(
        json.dumps(report, sort_keys=True, indent=2) + "\n")
    return report


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--head", required=True)
    ap.add_argument("--output", required=True, type=Path)
    ap.add_argument("--inventory-only", action="store_true")
    ap.add_argument("--shard-index", type=int, default=0)
    ap.add_argument("--shard-count", type=int, default=1)
    args = ap.parse_args(argv)
    try:
        if args.inventory_only:
            plan = required_inventory()
            output = {
                "status": "SOURCE_CANDIDATE_UNREVIEWED",
                "proof_targets": len(plan),
                "cases": len({cid for row in plan for cid in row["case_ids"]}),
                "claims": len({cid for row in plan for cid in row["claim_ids"]}),
                "declarations": plan,
                "inventory_sha256": inventory_digest(plan),
            }
            print(json.dumps(output, indent=2, sort_keys=True))
        else:
            out = export_all(args.head, args.output,
                             shard_index=args.shard_index,
                             shard_count=args.shard_count)
            print(json.dumps({"head": out["head_sha"],
                              "proof_targets": out["proof_count"],
                              "status": out["status"]}))
    except (OSError, ValueError, RuntimeError) as exc:
        print("ALL CASE LEAN EVIDENCE BLOCKED:", exc, file=sys.stderr)
        return 2
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
