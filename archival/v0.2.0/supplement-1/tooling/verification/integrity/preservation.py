"""Compare canonical candidate objects with the immutable accepted inventory."""

from dataclasses import dataclass
import hashlib

from .inventory import inventory_digest, load_reference_inventory
from .policy import (
    ACCEPTED_RELEASE, ACCEPTED_RELEASE_TREE, CLOSED_ROOTS, DIFFERENCE_LIMIT,
    PROTECTED_BLOB_LIMIT, PROTECTED_TOTAL_LIMIT, SENSITIVE_ROOTS,
)
from .reports import HardeningError


@dataclass(frozen=True)
class PreservationDifference:
    code: str
    path: bytes
    message: str


@dataclass(frozen=True)
class PreservationResult:
    differences: tuple[PreservationDifference, ...]
    protected_count: int
    protected_bytes: int

    @property
    def status(self):
        return "FAIL" if self.differences else "PASS"

    @property
    def error_code(self):
        return self.differences[0].code if self.differences else None

    def require_pass(self):
        if self.differences:
            first = self.differences[0]
            failure = HardeningError(first.code, first.message + ": " + repr(first.path))
            failure.details = {
                "scope": "canonical_commit_objects",
                "protected_count": self.protected_count,
                "differences": [{"code": diff.code,
                                 "path": diff.path.decode("utf-8", "backslashreplace"),
                                 "message": diff.message} for diff in self.differences],
            }
            raise failure


def _under(path, root):
    return path == root or path.startswith(root + b"/")


def compare_preserved(reference, reference_tree, candidate_tree, read_blob,
                      closed_roots=CLOSED_ROOTS):
    """Pure comparison. Never dereference repository filesystem paths.

    Primary precedence: ancestor/type, missing, mode, content, closed addition.
    All differences use deterministic (precedence,path) ordering and are bounded.
    """
    differences = []
    precedence = {"E_PROTECTED_TYPE": 0, "E_PROTECTED_MISSING": 1,
                  "E_PROTECTED_MODE": 2, "E_PROTECTED_CONTENT": 3,
                  "E_CLOSED_ADDITION": 4}

    def add(code, path, message):
        if len(differences) >= DIFFERENCE_LIMIT:
            raise HardeningError("E_LIMIT", "preservation difference budget exceeded")
        differences.append(PreservationDifference(code, path, message))

    replacement_paths = set()
    targets = set(closed_roots)
    reference_directories = {path for path, entry in reference_tree.items()
                             if entry.object_type == "tree"}
    for path in reference_tree:
        parts = path.split(b"/")
        reference_directories.update(b"/".join(parts[:i]) for i in range(1, len(parts)))
    for entry in reference:
        parts = entry.path.split(b"/")
        targets.update(b"/".join(parts[:i]) for i in range(1, len(parts)))
    for ancestor in sorted(targets):
        actual = candidate_tree.get(ancestor)
        # Callers may provide leaves alone (private fixtures) or full topology.
        if (actual is not None and actual.object_type != "tree"
                and ancestor in reference_directories):
            replacement_paths.add(ancestor)
            add("E_PROTECTED_TYPE", ancestor, "protected directory replaced by a leaf")

    total = 0
    for entry in reference:
        if any(entry.path.startswith(path + b"/") for path in replacement_paths):
            continue
        actual = candidate_tree.get(entry.path)
        if actual is None:
            # A file replaced by a directory is a topology/type change.
            if any(path.startswith(entry.path + b"/") for path in candidate_tree):
                add("E_PROTECTED_TYPE", entry.path, "protected file replaced by a directory")
            else:
                add("E_PROTECTED_MISSING", entry.path, "protected path is absent")
            continue
        if actual.object_type != "blob" or actual.mode not in ("100644", "100755"):
            add("E_PROTECTED_TYPE", entry.path, "protected regular file changed type")
            continue
        if actual.mode != entry.mode:
            add("E_PROTECTED_MODE", entry.path, "protected regular file changed mode")
        blob = read_blob(actual.oid, limit=PROTECTED_BLOB_LIMIT)
        total += len(blob)
        if total > PROTECTED_TOTAL_LIMIT:
            raise HardeningError("E_LIMIT", "candidate protected bytes exceed budget")
        if (actual.oid != entry.oid or len(blob) != entry.size
                or hashlib.sha256(blob).hexdigest() != entry.sha256):
            add("E_PROTECTED_CONTENT", entry.path, "protected canonical bytes changed")
    pinned = {entry.path for entry in reference}
    for path in sorted(set(reference_tree) - set(candidate_tree) - pinned):
        if any(_under(path, root) for root in closed_roots):
            if not any(path.startswith(ancestor + b"/") for ancestor in replacement_paths):
                add("E_PROTECTED_MISSING", path, "closed-root reference member is absent")
    for path in sorted(set(candidate_tree) - set(reference_tree)):
        if path in replacement_paths:
            continue
        if any(_under(path, root) for root in closed_roots):
            add("E_CLOSED_ADDITION", path, "new tracked path inside a closed root")
    differences.sort(key=lambda diff: (precedence[diff.code], diff.path))
    return PreservationResult(tuple(differences), len(reference), total)


def sensitive_changes(reference_tree, candidate_tree):
    return [path.decode("utf-8", "backslashreplace")
            for path in sorted(set(reference_tree) | set(candidate_tree))
            if any(_under(path, root) for root in SENSITIVE_ROOTS)
            and reference_tree.get(path) != candidate_tree.get(path)]


def verify_preservation(repo, candidate):
    repo.validate_candidate(candidate, accepted_sha=ACCEPTED_RELEASE,
                            accepted_tree=ACCEPTED_RELEASE_TREE)
    reference = load_reference_inventory(repo)
    trusted_tree = repo.tree_entries(ACCEPTED_RELEASE)
    candidate_tree = repo.tree_entries(candidate)
    result = compare_preserved(reference, trusted_tree, candidate_tree, repo.blob)
    result.require_pass()
    return {
        "scope": "canonical_commit_objects",
        "completed_stages": ["reference_inventory", "protected_comparison", "closed_root_membership"],
        "protected_count": result.protected_count,
        "protected_bytes": result.protected_bytes,
        "inventory_sha256": inventory_digest(reference),
        "trust_sensitive_changes": sensitive_changes(trusted_tree, candidate_tree),
        "trust_boundary": "Candidate-owned checker and workflow require independent review.",
    }


def validate_maintenance_scope(repo, candidate):
    """One-time acceptance check; deliberately absent from the permanent gate."""
    baseline = repo.tree_entries(ACCEPTED_RELEASE)
    target = repo.tree_entries(candidate)
    paths = set(baseline) | set(target)
    for path in sorted(paths):
        if (path in (b"PermanssonLean.lean", b"PermanssonResearch.lean")
                or _under(path, b"PermanssonLean") or _under(path, b"PermanssonResearch")):
            if baseline.get(path) != target.get(path):
                raise HardeningError("E_MAINTENANCE_SCOPE", "Lean source changed: " + repr(path))


def main(argv=None):
    from .reports import run_cli
    return run_cli("frozen-source-preservation", argv, verify_preservation)


if __name__ == "__main__":
    raise SystemExit(main())
