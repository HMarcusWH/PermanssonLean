"""PR113 successor A2-P02 source-identity proposal: a NEW read-only profile.

The inherited PR79/PR80 localized_prefix_support.inspect_repo and its test
remain untouched, and intentionally reject changed historical providers.
This separately versioned candidate pins the *entire* known T/B-to-PR113
modified-provider delta by actual Git blob identity, preserves all original
A2 mathematical provider objects, and checks the complete clean current tree.

It is NOT an authorized replacement for the historical verifier and cannot
issue mathematical acceptance, security approval, or a release receipt.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys

import localized_prefix_support as original

FORMAT = "Permansson.PR113.A2SuccessorIdentityCandidate.v1"
SHA = re.compile(r"^[0-9a-f]{40}$")
# The exact twelve already-changed former baseline files. No wildcard grants.
PINNED_MODIFIED_PROVIDERS = {
    ".github/workflows/application.yml": "bdd02d48265e08f8cb94b7402da56da9c8e3ec9d",
    ".github/workflows/e1-approx-quotient-smoke.yml": "11bba31567059d968133a513c78b9103e43418fc",
    ".github/workflows/f1-multiagent-protocols-smoke.yml": "b87a8c082f51f24dd7d533147e676813d1a78b85",
    ".github/workflows/lean.yml": "65aa095a9564cbef0bdca035c95b6d8f568d2cf4",
    ".github/workflows/research-integrity-portability.yml": "380a592039dd9e50b87bb2891771e76b071a2aaa",
    ".github/workflows/research-integrity.yml": "19bab92285ab2c981b0a1200c03024f7d022e31c",
    ".github/workflows/research-lean.yml": "06842a2da34d6ff06434f202a7630edd57e8cb20",
    ".github/workflows/research-release-verification.yml": "46ea7ebeae142f794394179154385cf1762b78d3",
    ".github/workflows/verification.yml": "c016aa6efcc42e19d81cb148f5db6bc6a439d7d3",
    "verification/integrity/tests/test_workflow.py": "1fa90e0dce90518b8052e42199867f11c77e1010",
    "verification/integrity/workflow_contract.py": "f8fa8196a7a0e33d2f218faa0ba570c09aac9a3a",
    "verification/research/test_paper_x1_lean_closure.py": "2ee078c86c58b5e577597acfc3ae950e4028ebac",
}
# These inherited verifier binaries themselves are preserved exactly.
INHERITED_A2_VERIFIERS = {
    "verification/research/localized_prefix_support.py": "93462e9546ba494e8384d75ce49ff9020f831216",
    "verification/research/localized_prefix_gate.py": "6f15dca74895e59a4d4bfcb54d38b471a1798be3",
    "verification/research/test_localized_prefix_compiler.py": "c0f49038ea9b590720c78be85968eb63f5ac820f",
}


def demand(ok: bool, message: str) -> None:
    if not ok:
        raise original.GuardError(message)


def reconcile(old: dict, current: dict) -> dict:
    """Reviewable pure Git-tree delta gate, never a blob-prefix wildcard."""
    demand(set(old) <= set(current), "historical provider deleted")
    modified = {p for p in old if old[p] != current[p]}
    exceptions = original.REVIEWABLE_DOCUMENTATION | {"PermanssonResearch.lean"}
    demand(modified - exceptions == set(PINNED_MODIFIED_PROVIDERS),
           "PR113 successor source delta differs from exact frozen inventory")
    for path, oid in PINNED_MODIFIED_PROVIDERS.items():
        demand(current[path] == ("100644", oid),
               "PR113 pinned provider changed without new security review: " + path)
    for path in modified & original.REVIEWABLE_DOCUMENTATION:
        demand(old[path][0] == current[path][0] == "100644",
               "reviewable document mode changed: " + path)
    demand("PermanssonResearch.lean" in modified,
           "A2 research-root extension unexpectedly absent")
    for path, oid in original.ACCEPTED_A2_PROOF_BLOBS.items():
        demand(current.get(path) == ("100644", oid),
               "accepted A2 mathematical proof blob changed: " + path)
    for path, oid in INHERITED_A2_VERIFIERS.items():
        demand(current.get(path) == ("100644", oid),
               "inherited A2 historical verifier changed: " + path)
    for path in ("lean-toolchain", "lake-manifest.json"):
        demand(old.get(path) == current.get(path),
               "frozen Lean/dependency pin changed: " + path)
    return {
        "modified_old_provider_paths": sorted(modified),
        "pinned_successor_provider_paths": sorted(PINNED_MODIFIED_PROVIDERS),
        "reviewable_documentation_paths": sorted(
            modified & original.REVIEWABLE_DOCUMENTATION),
        "accepted_a2_proof_blobs": len(original.ACCEPTED_A2_PROOF_BLOBS),
        "historical_a2_verifier_blobs": len(INHERITED_A2_VERIFIERS),
    }


def normalize_additive_root_separator(raw: bytes) -> bytes:
    """Permit only the two blank lines introduced at the original A2 tail.

    This is an exact-position formatting equivalence, never global
    whitespace canonicalization of mathematical source.
    """
    anchor = (b"import PermanssonResearch.ConstitutiveQuasi."
              b"LocalizedPrefixExamples\\n")
    original = anchor + b"\\n/-!\\n"
    current = anchor + b"\\n\\n\\n/-!\\n"
    if raw.count(current) == 1 and raw.count(original) == 0:
        return raw.replace(current, original, 1)
    return raw


def verify_root(repo: Path, old: dict, current: dict) -> None:
    """Original A2 imports plus direct imports of truly new modules only."""
    source = original.git_bytes(repo, "show",
                                original.BASE + ":PermanssonResearch.lean")
    demand(original.blob_sha(source) == original.ROOT_BLOB,
           "original A2 root anchor changed")
    expected = original.rewrite_root(source)
    actual = original.read_member(repo, "PermanssonResearch.lean")
    demand(original.blob_sha(actual) == current["PermanssonResearch.lean"][1],
           "current root differs from committed Git blob")
    for path in sorted(set(current) - set(old)):
        if path.startswith("PermanssonResearch/") and path.endswith(".lean"):
            module = path.removesuffix(".lean").replace("/", ".")
            line = ("import " + module + "\n").encode("utf-8")
            if line in expected:  # One of the original A2 new imports.
                continue
            demand(actual.count(line) == 1,
                   "missing/duplicated direct import: " + module)
            actual = actual.replace(line, b"", 1)
    demand(normalize_additive_root_separator(actual) == expected,
           "Research root differs from exact historical A2 import bridge")


def audit(repo: Path, head: str) -> dict:
    repo = repo.resolve(strict=True)
    demand(SHA.fullmatch(head) is not None, "invalid reviewed head")
    demand(Path(original.git_text(repo, "rev-parse", "--show-toplevel")).resolve()
           == repo, "not a genuine repository root")
    demand(original.git_text(repo, "rev-parse", "HEAD") == head,
           "requested H is not checked-out source")
    demand(original.git_text(repo, "rev-parse",
                             original.BASE + "^{tree}") == original.BASE_TREE,
           "historical PR79 source/tree identity changed")
    original.git_bytes(repo, "merge-base", "--is-ancestor", original.BASE, head)
    demand(not original.git_bytes(repo, "status", "--porcelain=v1",
                                  "--untracked-files=all"),
           "successor source has tracked or untracked modifications")
    old = original.parse_tree(original.git_bytes(
        repo, "ls-tree", "-r", "-z", original.BASE))
    current = original.parse_tree(original.git_bytes(
        repo, "ls-tree", "-r", "-z", "HEAD"))
    reconciled = reconcile(old, current)
    verify_root(repo, old, current)
    # No ignored/untracked/assume-unchanged source or byte substitution.
    for path, (mode, blob) in sorted(current.items()):
        actual = original.read_member(repo, path)
        demand(original.blob_sha(actual) == blob,
               "source file differs from exact Git blob: " + path)
        if path in original.REVIEWABLE_DOCUMENTATION:
            demand(b"\r" not in actual and actual.endswith(b"\n"),
                   "noncanonical reviewed documentation: " + path)
        if path in original.ACCEPTED_A2_PROOF_BLOBS:
            original.source_firewall(actual.decode("utf-8", "strict"))
        if path.endswith(".lean") and path.startswith("PermanssonResearch/"):
            demand(mode == "100644", "unexpected research proof mode: " + path)
    return {
        "format": FORMAT,
        "status": "SOURCE_IDENTITY_CANDIDATE_NEEDS_INDEPENDENT_SECURITY_REVIEW",
        "head_sha": head,
        "head_tree_sha": original.git_text(repo, "rev-parse", "HEAD^{tree}"),
        "inherited_baseline": original.BASE,
        "inherited_baseline_tree": original.BASE_TREE,
        "successor_delta": reconciled,
        "current_file_count": len(current),
        "source_byte_identity_checked": True,
        "original_a2_compiler_run": False,
        "successor_a2_compiler_run": False,
        "historical_verifier_replaced": False,
        "independent_security_review": False,
        "mathematical_acceptance": False,
        "full_release_approved": False,
    }


def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--head", required=True)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--out", type=Path, required=True)
    options = parser.parse_args(argv)
    try:
        target = options.out.resolve()
        repo = options.repo.resolve(strict=True)
        demand(not target.exists() and not target.is_relative_to(repo),
               "report must be a fresh detached path")
        report = audit(repo, options.head)
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n",
                          encoding="utf-8")
        print(json.dumps({"status": report["status"],
                          "head_sha": report["head_sha"]}))
        return 0
    except (original.GuardError, OSError, UnicodeError, ValueError) as exc:
        print("PR113 A2 SUCCESSOR IDENTITY BLOCKED:", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
