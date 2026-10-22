"""Detached exact-H case, claim, and compiler-evidence verification.

Source-candidate decisions do not represent independent acceptance.
Only an overlay bound to live non-author exact-H GitHub review scopes, genuine
head-bound check runs and immutable off-repo evidence may yield effective
decisions. This module never mutates the historical 45-case ledger.
"""
from __future__ import annotations

import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import re
import stat
import zipfile

ROOT = Path(__file__).resolve().parents[2]
FORMAT = "Permansson.FinalClosureDetachedReceipts.v2"
TRUSTED_AXIOMS = frozenset({"Classical.choice", "Quot.sound", "propext"})
DECISIONS = frozenset({"VERIFIED_SELECTED_SCOPE", "VERIFIED_NEGATIVE"})
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
SHA40_RE = re.compile(r"^[0-9a-f]{40}$")
DECL_RE = re.compile(
    r"(?m)^\s*(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def)\s+([A-Za-z0-9_']+)(?=\W)")
INVALID_DIAGNOSTICS = (
    "unknown module", "unknown identifier", "unknown constant",
    "unknown tactic", "failed to import", "parser error", "syntax error",
    "out of memory", "timed out", "timeout", "maximum number of heartbeats",
    "failed to synthesize", "object file", "sorryax",
    "declaration uses " + chr(96) + "sorry" + chr(96),
)
SEMANTIC_DIAGNOSTICS = (
    "type mismatch", "unsolved goals", "application type mismatch",
)
MAX_BUNDLE_BYTES = 32 * 1024 * 1024
MAX_MEMBER_BYTES = 4 * 1024 * 1024
MAX_EXPANDED_BYTES = 64 * 1024 * 1024
MAX_MEMBERS = 512
MAX_EXPANSION_RATIO = 1000


class EvidenceError(ValueError):
    pass


def demand(ok: bool, message: str):
    if not ok:
        raise EvidenceError(message)


def digest(raw: bytes) -> str:
    return hashlib.sha256(raw).hexdigest()


def exact_source(path: str) -> Path:
    demand(isinstance(path, str) and path and "\\" not in path, "invalid source path")
    rel = PurePosixPath(path)
    demand(not rel.is_absolute() and ".." not in rel.parts and
           rel.as_posix() == path, "unsafe source path")
    p = (ROOT / path).resolve()
    demand(p.is_relative_to(ROOT.resolve()) and p.is_file() and
           not (ROOT / path).is_symlink(), "source missing or escaped: " + path)
    return p


def statement_header(source: str, qualified: str) -> str:
    """Bind the actual nested Lean namespace, not merely a matching local name.

    This lexical calculation is not a substitute for compiler #check of the FQN.
    """
    demand(isinstance(qualified, str) and "." in qualified and
           re.fullmatch(r"[A-Za-z0-9_'.]+", qualified) is not None,
           "declaration must be fully qualified")
    name = qualified.rsplit(".", 1)[-1]
    lines = source.splitlines(keepends=True)
    stack = []
    offset = 0
    namespaces = []
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("namespace "):
            ns = stripped[len("namespace "):].strip()
            demand(re.fullmatch(r"[A-Za-z0-9_.]+", ns) is not None,
                   "invalid Lean namespace")
            stack.append(ns)
        elif stripped.startswith("end "):
            end = stripped[4:].strip()
            if stack and (stack[-1] == end or
                          stack[-1].split(".")[-1] == end):
                stack.pop()
            elif stack and ".".join(stack) == end:
                stack.clear()
        if DECL_RE.match(line):
            m = DECL_RE.match(line)
            if m and m.group(1) == name:
                prefix = ".".join(stack)
                candidate = prefix + "." + name if prefix else name
                namespaces.append((candidate, offset + m.start()))
        offset += len(line)
    chosen = [start for candidate, start in namespaces if candidate == qualified]
    demand(len(chosen) == 1, "missing/ambiguous fully qualified declaration: " + qualified)
    start = chosen[0]
    match = DECL_RE.match(source, start)
    demand(match is not None, "declaration scan inconsistent")
    following = DECL_RE.search(source, match.end())
    limit = following.start() if following else len(source)
    stop = source.find(":=", match.end(), limit)
    demand(stop >def parse_target_axioms(log: str, declaration: str) -> list[str]:
    """Parse one target-qualified compiler record, never an unrelated last list."""
    demand(isinstance(log, str) and isinstance(declaration, str) and
           re.fullmatch(r"[A-Za-z0-9_'.]+", declaration) is not None,
           "invalid target axiom record")
    list_pat = re.compile(
        r"([A-Za-z0-9_'.]+) depends on axioms:\s*\[([^\]]*)\]")
    zero_pat = re.compile(
        r"([A-Za-z0-9_'.]+) does not depend on any axioms")
    records = [(m.group(1), m.group(2)) for m in list_pat.finditer(log)]
    records += [(m.group(1), "") for m in zero_pat.finditer(log)]
    demand(len(records) == 1 and records[0][0] == declaration,
           "missing, ambiguous or wrong-target compiler axiom output")
    names = [x.strip() for x in records[0][1].split(",") if x.strip()]
    demand(len(set(names)) == len(names) and set(names) <= TRUSTED_AXIOMS,
           "untrusted or duplicate transitive axiom")
    return names

def load_detached_bundle(path: str | Path, expected_sha256: str):
    """Verify and parse the exact hashed ZIP bytes with aggregate resource bounds.

    All metadata are checked before decompression. Never reopen the potentially
    mutable source path after verifying its digest; never extract members to disk.
    """
    location = Path(path)
    demand(location.is_file() and not location.is_symlink() and
           not location.resolve().is_relative_to(ROOT.resolve()),
           "evidence must be an external regular file")
    demand(isinstance(expected_sha256, str) and SHA256_RE.fullmatch(expected_sha256),
           "missing bundle SHA256")
    demand(location.stat().st_size <= MAX_BUNDLE_BYTES, "evidence bundle too large")
    raw = location.read_bytes()
    demand(len(raw) <= MAX_BUNDLE_BYTES and digest(raw) == expected_sha256,
           "detached evidence digest mismatch")
    members = {}
    try:
        with zipfile.ZipFile(io.BytesIO(raw)) as archive:
            entries = archive.infolist()
            demand(len(entries) <= MAX_MEMBERS, "too many evidence members")
            normalized = set()
            expanded = 0
            for member in entries:
                name = member.filename
                rel = PurePosixPath(name)
                demand(name and not member.is_dir() and
                       chr(92) not in name and not rel.is_absolute() and
                       ".." not in rel.parts and rel.as_posix() == name and
                       not any(part in ("", ".") for part in name.split("/")),
                       "unsafe evidence member")
                folded = name.casefold()
                demand(folded not in normalized, "duplicate evidence member")
                normalized.add(folded)
                mode = (member.external_attr >> 16) & 0o170000
                demand(mode in (0, stat.S_IFREG), "nonregular evidence member")
                demand(member.file_size <= MAX_MEMBER_BYTES, "oversized evidence member")
                expanded += member.file_size
                demand(expanded <= MAX_EXPANDED_BYTES,
                       "expanded evidence bundle too large")
                demand(member.compress_size >= 0 and
                       (member.file_size <= 1024 * 1024 or
                        member.file_size <= MAX_EXPANSION_RATIO *
                        max(1, member.compress_size)),
                       "suspicious evidence compression ratio")
            for name in normalized:
                parts = name.split("/")
                demand(not any("/".join(parts[:i]) in normalized
                               for i in range(1, len(parts))),
                       "evidence member shadows a path ancestor")
            for member in entries:
                payload = archive.read(member)
                demand(len(payload) == member.file_size,
                       "evidence member size mismatch")
                members[member.filename] = payload
    except (OSError, zipfile.BadZipFile, RuntimeError, EOFError) as exc:
        raise EvidenceError("unreadable evidence archive") from exc
    return members

exc:
        raise EvidenceError("unreadable evidence archive") from exc
    return members


def member_bytes(members: dict[str, bytes], name: str, expected_hash: str) -> bytes:
    demand(isinstance(name, str) and name in members,
           "evidence log member absent")
    demand(isinstance(expected_hash, str) and SHA256_RE.fullmatch(expected_hash) and
           digest(members[name]) == expected_hash, "evidence log digest mismatch")
    return members[name]


def validate_compiler_receipt(row: dict, head: str, members: dict[str, bytes],
                              accepted_checks: dict):
    demand(isinstance(row, dict) and row.get("head_sha") == head,
           "stale/malformed compiler receipt")
    path = row.get("path")
    source = exact_source(path)
    demand(source.suffix == ".lean" and
           digest(source.read_bytes()) == row.get("source_sha256"),
           "compiler receipt does not bind source bytes")
    declaration = row.get("declaration")
    header = statement_header(source.read_text(encoding="utf-8"), declaration)
    demand(digest(header.encode("utf-8")) == row.get("statement_sha256"),
           "compiler receipt binds wrong theorem statement")
    axioms = row.get("transitive_axioms")
    demand(isinstance(axioms, list) and len(axioms) == len(set(axioms)) and
           set(axioms) <= TRUSTED_AXIOMS, "bad or unreviewed transitive axiom")
    demand(row.get("compiler_check") == "research" and
           row.get("compiler_result") == "PASS", "compiler success not established")
    check = accepted_checks.get("research")
    demand(check and row.get("check_run_id") == check["id"] and
           check["head_sha"] == head, "compiler check does not bind exact H")
    data = member_bytes(members, row.get("axiom_log_member"),
                        row.get("axiom_log_sha256"))
    stdout = data.decode("utf-8", errors="replace")
    demand(declaration in stdout and "sorryAx" not in stdout and
           "error:" not in stdout.lower(), "invalid axiom source diagnostic")
    observed = parse_target_axioms(stdout, declaration)
    demand(observed == axioms, "target axioms do not match retained log")
    cases = row.get("case_ids")
    claims = row.get("claim_ids")
    demand(isinstance(cases, list) and isinstance(claims, list) and
           (cases or claims), "theorem has no acceptance owner")
    return row["id"]


def validate_test_receipt(row: dict, head: str, members: dict[str, bytes],
                          accepted_checks: dict, *, negative: bool):
    demand(isinstance(row, dict) and row.get("head_sha") == head,
           "stale/malformed test receipt")
    p = exact_source(row.get("test_path"))
    demand(p.suffix == ".py" and p.name.startswith("test_") and
           digest(p.read_bytes()) == row.get("source_sha256"),
           "test source identity not proven")
    test_name = row.get("test_name")
    demand(isinstance(test_name, str) and test_name.startswith("test_") and
           re.search(r"(?m)^\s*def\s+" + re.escape(test_name) + r"\(",
                     p.read_text(encoding="utf-8")) is not None,
           "named test does not exist")
    check = accepted_checks.get("research")
    demand(check and row.get("check_run_id") == check["id"] and
           check["head_sha"] == head, "test CI check not bound to H")
    pos = row.get("positive_control")
    demand(isinstance(pos, dict) and pos.get("compiled") is True and
           pos.get("exit_code") == 0 and pos.get("lean_toolchain") == "4.34.0",
           "positive control missing or failed")
    positive = member_bytes(members, pos.get("log_member"), pos.get("log_sha256"))
    demand("error:" not in positive.decode("utf-8", errors="replace").lower(),
           "positive test log contains compiler error")
    log = member_bytes(members, row.get("log_member"), row.get("log_sha256"))
    s = log.decode("utf-8", errors="replace").lower()
    demand(isinstance(row.get("case_ids"), list) and row["case_ids"],
           "test is not linked to an original case")
    if negative:
        demand(row.get("outcome") == "REJECTED_SEMANTIC" and
               row.get("compiler_exit_code") not in (None, 0) and
               isinstance(row.get("mutant_source_sha256"), str) and
               SHA256_RE.fullmatch(row["mutant_source_sha256"]),
               "nonsemantic or missing false mutant")
        mutated = member_bytes(members, row.get("mutant_source_member"),
                               row["mutant_source_sha256"])
        original_file = exact_source(row.get("original_lean_source_path"))
        original = original_file.read_bytes()
        demand(digest(original) == row.get("original_lean_source_sha256") and
               digest(mutated) != digest(original) and
               [line for line in mutated.decode("utf-8").splitlines()
                if line.startswith("import ")] ==
               [line for line in original.decode("utf-8").splitlines()
                if line.startswith("import ")],
               "mutant bytes not a source-bound semantic variation")
        demand(any(fragment in s for fragment in SEMANTIC_DIAGNOSTICS) and
               "error:" in s and
               not any(fragment in s for fragment in INVALID_DIAGNOSTICS),
               "false theorem was not rejected semantically")
    else:
        demand(row.get("outcome") == "PASS" and
               row.get("compiler_exit_code") == 0 and
               not any(fragment in s for fragment in INVALID_DIAGNOSTICS) and
               "error:" not in s, "positive test failed")
    return row["id"]


def effective_acceptance(overlay: dict, *, head: str, case_ledger: dict,
                         claims: list[dict], members: dict[str, bytes],
                         accepted_checks: dict, approved_review_scopes: dict):
    """Produce read-only decisions. All reviewer scopes come from live GitHub.

    approved_review_scopes is populated ONLY by authentication of non-author
    GitHub APPROVED review bodies at the identical frozen H and bundle SHA.
    """
    demand(isinstance(overlay, dict) and overlay.get("format") == FORMAT and
           overlay.get("head_sha") == head and SHA40_RE.fullmatch(head),
           "unsupported or stale detached overlay")
    originals = {c["case_id"]: c for c in case_ledger["cases"]}
    demand(len(originals) == len(case_ledger["cases"]) == 45,
           "original 45-case identity mismatch")
    inventory = {c["id"] for c in claims}
    demand(len(inventory) == 11, "claim inventory mismatch")
    def keyed(name):
        rows = overlay.get(name, [])
        demand(isinstance(rows, list), "invalid evidence collection: " + name)
        records = {}
        for row in rows:
            demand(isinstance(row, dict) and
                   isinstance(row.get("id"), str) and
                   row["id"] and row["id"] not in records,
                   "duplicate or missing evidence identifier: " + name)
            records[row["id"]] = row
        return records
    proof_rows = keyed("compiler_axiom_receipts")
    pos_rows = keyed("positive_test_receipts")
    neg_rows = keyed("semantic_negative_receipts")
    case_rows = keyed("case_decisions")
    claim_rows = keyed("claim_decisions")
    proofs = {key: validate_compiler_receipt(row, head, members, accepted_checks)
              for key, row in proof_rows.items()}
    positives = {key: validate_test_receipt(row, head, members, accepted_checks,
                                         negative=False)
                 for key, row in pos_rows.items()}
    negatives = {key: validate_test_receipt(row, head, members, accepted_checks,
                                         negative=True)
                 for key, row in neg_rows.items()}
    effective_cases = {}
    for row in case_rows.values():
        cid = row.get("case_id")
        demand(cid in originals and cid not in effective_cases,
               "unknown/duplicate accepted original case")
        baseline = originals[cid]
        demand(row.get("decision") in DECISIONS and
               row.get("required_expected_result_sha256") ==
               digest(baseline["required_expected_result"].encode("utf-8")),
               "altered original case expectation")
        ids = row.get("proof_ids", [])
        plus = row.get("positive_ids", [])
        minus = row.get("negative_ids", [])
        demand(all(isinstance(x, list) and bool(x) for x in (ids, plus, minus)),
               "accepted case lacks individual positive/negative/proof evidence")
        demand(all(i in proofs and cid in proof_rows[i]["case_ids"] for i in ids) and
               all(i in positives and cid in pos_rows[i]["case_ids"] for i in plus) and
               all(i in negatives and cid in neg_rows[i]["case_ids"] for i in minus),
               "evidence borrowed from another case")
        rid = row.get("review_id")
        scope = approved_review_scopes.get(rid, {})
        demand(scope.get("cases", {}).get(cid) == row["decision"],
               "no exact-H non-author reviewer approval for this case")
        effective_cases[cid] = row["decision"]
    effective_claims = set()
    for row in claim_rows.values():
        cid = row.get("claim_id")
        demand(cid in inventory and cid not in effective_claims,
               "unknown or duplicate accepted claim")
        ids = row.get("proof_ids", [])
        demand(isinstance(ids, list) and bool(ids) and
               all(i in proofs and cid in proof_rows[i]["claim_ids"] for i in ids),
               "claim declaration not source bound")
        rid = row.get("review_id")
        demand(cid in approved_review_scopes.get(rid, {}).get("claims", ()),
               "claim lacks independent exact-H scope review")
        effective_claims.add(cid)
    return {
        "effective_cases": effective_cases,
        "effective_claims": sorted(effective_claims),
        "accepted_case_count": len(effective_cases),
        "pending_case_count": 45 - len(effective_cases),
        "accepted_claim_count": len(effective_claims),
        "status": "REVIEWED_SCOPE_ONLY_NOT_EMPIRICAL_CERTIFICATION",
    }
