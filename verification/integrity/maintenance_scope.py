"""One-time maintenance acceptance; deliberately outside permanent CI policy."""
from .policy import ACCEPTED_RELEASE, ACCEPTED_RELEASE_TREE
from .preservation import validate_maintenance_scope
from .reports import run_cli


def verify_maintenance_candidate(repo, candidate):
    repo.validate_candidate(candidate, accepted_sha=ACCEPTED_RELEASE,
                            accepted_tree=ACCEPTED_RELEASE_TREE)
    validate_maintenance_scope(repo, candidate)
    return {
        "scope": "complete-canonical-Lean-trees-and-root-files",
        "acceptance_only": True,
        "permanent_preservation_policy": False,
        "accepted_release": ACCEPTED_RELEASE,
        "accepted_tree": ACCEPTED_RELEASE_TREE,
        "candidate": candidate,
        "candidate_tree": repo.commit(candidate).tree,
        "compared_paths": ["PermanssonLean/", "PermanssonLean.lean",
                           "PermanssonResearch/", "PermanssonResearch.lean"],
        "differences": [],
        "completed_stages": ["fixed_authority", "complete_Lean_scope_comparison"],
        "acceptance_binding": "Join this canonical candidate/tree with independently captured current PR H/B/S; local execution does not manufacture a GitHub event.",
    }


def main(argv=None):
    return run_cli("maintenance-Lean-scope", argv, verify_maintenance_candidate)


if __name__ == "__main__":
    raise SystemExit(main())
