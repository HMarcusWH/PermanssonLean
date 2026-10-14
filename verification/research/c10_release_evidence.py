"""Generate a source-bound C10 six-state proof-evidence bundle.

Release-grade provenance is available ONLY when source head/base/merge are
checked against an independently supplied GitHub PR event and actual Git
commit object. JSON status fields, hashes, and a captured transcript are
never substitutes for kernel checking or an original Exact-GR proof.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import subprocess

from c10_emit_golden_bridge import emit_golden_bridge
from c10_exact_execution import canonical_bytes, check_input
from c10_golden import create_golden
from c10_verify_receipt import strict_object, verify_receipt

ROOT = Path(__file__).resolve().parents[2]
SPEC_PATH = "docs/PR61_C10_Exact_Constitutive_Execution_Spec_v1.1_AUDITED.md"
FORMAT = "Permansson.C10.release-evidence.v1"
TYPE_ID = "D0.Unit-Fin-n.actionSelection.six-state"
THEOREMS = (
    "reifiedReceipt_valid",
    "reifiedReceipt_conditions",
    "reifiedGolden_data_contract",
    "reifiedGolden_original_margins",
    "reifiedGolden_selection",
    "reifiedGolden_original_global_max",
    "PermanssonResearch.ReverseSolver.C10.six_original_baseline_exactGR",
)
ALLOW_AX = frozenset({"propext", "Classical.choice", "Quot.sound"})
ARTIFACTS = (
    "input.json", "normalized_input.json", "receipt.json",
    "C10ReifiedGolden.lean", "lean_check.stdout.txt",
    "lean_check.stderr.txt",
)


class EvidenceError(ValueError):
    pass


def require(cond: bool, reason: str) -> None:
    if not cond:
        raise EvidenceError(reason)


def strict_json(path: Path):
    with path.open(encoding="utf-8") as stream:
        return json.load(
            stream,
            parse_float=lambda _: (_ for _ in ()).throw(EvidenceError("JSON floating point forbidden")),
            object_pairs_hook=strict_object,
        )


def stable_json(value) -> bytes:
    return (json.dumps(value, ensure_ascii=False, sort_keys=True, indent=2) + "\n").encode("utf-8")


def digest(data: bytes) -> str:
    return sha256(data).hexdigest()


def git_output(root: Path, *args: str) -> str:
    result = subprocess.run(
        ["git", *args], cwd=root, capture_output=True, text=True, timeout=30, check=False
    )
    require(result.returncode == 0, "unable to verify Git object: " + result.stderr)
    return result.stdout.strip()


def parse_pr_checkout(event: dict, commit_object: str,
                      checkout_sha: str, repository: str,
                      claimed_ci_sha: str) -> dict:
    """Validate the raw synthetic-merge object against the PR event.

    Works with shallow Actions checkout: uses git cat-file -p HEAD, not
    parent object dereferences that require a deeper fetch.
    The caller must establish the event and commit came from trusted CI.
    """
    require(re.fullmatch(r"[0-9a-f]{40}", checkout_sha) is not None, "bad checkout SHA")
    require(checkout_sha == claimed_ci_sha, "GITHUB_SHA does not match checkout")
    require(event.get("repository", {}).get("full_name") == repository, "wrong event repository")
    pull = event.get("pull_request")
    require(isinstance(pull, dict), "trusted PR event required")
    base = pull.get("base", {}).get("sha")
    head = pull.get("head", {}).get("sha")
    number = pull.get("number", event.get("number"))
    require(isinstance(number, int) and number > 0, "missing PR number")
    require(all(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{40}", value)
                for value in (base, head)), "invalid PR base/head SHA")
    require(pull.get("base", {}).get("repo", {}).get("full_name") == repository,
            "PR base repository mismatch")
    parents = re.findall(r"^parent ([0-9a-f]{40})$", commit_object, re.MULTILINE)
    require(len(parents) == 2, "checkout is not an ordinary two-parent PR merge")
    require(parents == [base, head], "synthetic merge parents differ from PR event")
    return {
        "repository": repository,
        "pr_number": number,
        "base_sha": base,
        "head_sha": head,
        "synthetic_merge_sha": checkout_sha,
    }


def trusted_ci_context(event_path: Path, repository: str,
                       root: Path = ROOT, expected_ci_sha: str | None = None) -> dict:
    # The event path and environment values are CI trust roots, NOT receipt fields.
    event = strict_json(event_path)
    actual_sha = git_output(root, "rev-parse", "HEAD")
    expected_sha = expected_ci_sha or os.environ.get("GITHUB_SHA", "")
    return parse_pr_checkout(
        event, git_output(root, "cat-file", "-p", "HEAD"),
        actual_sha, repository, expected_sha,
    )


def axiom_reports(stdout: str) -> dict[str, list[str]]:
    result = {}
    for name in THEOREMS:
        escaped = re.escape(name)
        matches = re.findall(
            rf"'{escaped}' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])",
            stdout,
        )
        require(len(matches) == 1, "absent or ambiguous Lean axiom report: " + name)
        label, members = matches[0]
        found = [] if label == "does not depend on any axioms" else [
            value.strip() for value in members.split(",") if value.strip()
        ]
        require(set(found) <= ALLOW_AX, "unexpected Lean axiom in " + name)
        result[name] = found
    return result


def make_manifest(directory: Path, source: dict, root: Path = ROOT) -> dict:
    spec = root / SPEC_PATH
    require(spec.is_file(), "missing frozen audited specification")
    require(set(source) == {
        "repository", "pr_number", "head_sha", "base_sha", "synthetic_merge_sha"
    }, "bad source context")
    file_hashes = {}
    for name in ARTIFACTS:
        file = directory / name
        require(file.is_file(), "missing release artifact: " + name)
        file_hashes[name] = digest(file.read_bytes())
    return {
        "format": FORMAT,
        "source": source,
        "specification": {"path": SPEC_PATH, "sha256": digest(spec.read_bytes())},
        "typed_realization": {
            "id": TYPE_ID,
            "scope": "CONSTRUCTED_D0_SIX_STATE_ONLY",
            "binding_theorem": "reifiedGolden_data_contract",
            "original_margin_theorem": "reifiedGolden_original_margins",
        },
        "artifacts": file_hashes,
        "proof": {
            "tool": "lake env lean",
            "status": "GENERATED_LITERAL_KERNEL_CHECKED",
            "transitive_axioms_allowlist": sorted(ALLOW_AX),
            "theorems": list(THEOREMS),
        },
        "claim_boundary": (
            "Metadata is provenance, not mathematical proof. Generic JSON decoding "
            "and external-model identification are unverified; original positive "
            "relative PR requires an input-bound Exact GR theorem."
        ),
    }


def generate_release(directory: Path, context: dict, root: Path = ROOT) -> dict:
    """Run the real Lean compiler; fail closed on every nonzero/unknown result."""
    directory.mkdir(parents=True, exist_ok=True)
    require(not any(directory.iterdir()), "release output directory must be empty")
    receipt = create_golden(directory)
    verify_receipt(receipt)
    (directory / "normalized_input.json").write_bytes(stable_json(receipt["normalized_input"]))
    source = emit_golden_bridge(receipt)
    lean_path = directory / "C10ReifiedGolden.lean"
    lean_path.write_text(source, encoding="utf-8")
    try:
        completed = subprocess.run(
            ["lake", "env", "lean", str(lean_path.resolve())],
            cwd=root, capture_output=True, text=True, timeout=600, check=False,
        )
    except (FileNotFoundError, subprocess.TimeoutExpired) as exc:
        raise EvidenceError("Lean compiler missing or timed out") from exc
    (directory / "lean_check.stdout.txt").write_text(completed.stdout, encoding="utf-8")
    (directory / "lean_check.stderr.txt").write_text(completed.stderr, encoding="utf-8")
    require(completed.returncode == 0,
            "generated six-state Lean source did not compile:\n" +
            (completed.stdout + completed.stderr)[-5000:])
    axiom_reports(completed.stdout)
    manifest = make_manifest(directory, context, root)
    (directory / "evidence_manifest.json").write_bytes(stable_json(manifest))
    (directory / "verification_summary.txt").write_text(
        "C10 six-state source-bound generated proof: compiler exit 0\n"
        "Every printed transitive axiom set is within propext/Classical.choice/Quot.sound.\n"
        "This is not verified arbitrary JSON parsing or empirical identification.\n",
        encoding="utf-8",
    )
    return manifest


def main(argv=None) -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--event-file", type=Path, required=True)
    parser.add_argument("--repository", required=True)
    args = parser.parse_args(argv)
    context = trusted_ci_context(args.event_file, args.repository)
    manifest = generate_release(args.directory, context)
    print("C10 generated Lean evidence PASS: " + manifest["source"]["head_sha"])
    print("C10 evidence manifest: " + str(args.directory / "evidence_manifest.json"))


if __name__ == "__main__":
    main()
