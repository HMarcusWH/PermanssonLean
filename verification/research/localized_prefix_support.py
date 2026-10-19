"""A2-P02 source contract and byte-level guards (not mathematical proof).

No network, checkout, dependency update, commit, or repository settings writes.
All paths in manifests are canonical POSIX paths; no symlink traversal is allowed.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path, PurePosixPath, PureWindowsPath
import re
import stat
import subprocess
from typing import Any

BASE = "674c1b557d99ab080afb65a797a99cb5840eab62"
BASE_TREE = "b391f32f503f07bcfd7b29d8c24c1f9ad61eb19f"
ROOT_BLOB = "13dafb1d5fe1930a2f7ed875c333179eaea07250"
TOOLCHAIN = "leanprover/lean4:v4.34.0"
MATHLIB_REV = "5ed2965256430c3649e86755f9576b54eca72435"
ANCHOR = b"import PermanssonResearch.X1.ExactMatrixTables\n"
CONTRACT = "Permansson.A2P02.v2"
LIBRARIES = (
    "PermanssonResearch/Probability/GoodHistoryVisit.lean",
    "PermanssonResearch/Probability/LocalizedFinitePrefix.lean",
    "PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixError.lean",
    "PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean",
)
MODULES = tuple(p.removesuffix(".lean").replace("/", ".") for p in LIBRARIES)
IMPORTS = tuple("import " + m for m in MODULES)
NEW_FILES = LIBRARIES + (
    "verification/research/localized_prefix_support.py",
    "verification/research/localized_prefix_gate.py",
    "verification/research/test_localized_prefix_exact.py",
    "verification/research/test_localized_prefix_integrity.py",
    "verification/research/test_localized_prefix_gate.py",
    "verification/research/test_localized_prefix_compiler.py",
    "research/paper_closures/post_merge_79/A2_P02_BUILD_SPEC.md",
    "research/paper_closures/post_merge_79/A2_P02_ACCEPTANCE_MATRIX.json",
)
ALLOWED_CHANGED = frozenset(NEW_FILES + ("PermanssonResearch.lean",))

# Compiler-accepted PR80 mathematical source blobs. A later additive PR may
# extend the root, but cannot silently swap the certified closure proof terms.
# Altering one of these requires a separately reviewed source-identity update.
ACCEPTED_A2_PROOF_BLOBS = {
    "PermanssonResearch/Probability/GoodHistoryVisit.lean":
        "24ee31695ce76f16bec5b7b318afd4b1af4c9c17",
    "PermanssonResearch/Probability/LocalizedFinitePrefix.lean":
        "d40bc59c0fe107a632c1ed7588e5b51a0fa0e3ba",
    "PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixError.lean":
        "296a1ce4b6edbffb474f0d5a4bc63504c9b91a1b",
    "PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean":
        "4942c414be31c2afb3169c872d5fdedb3073b299",
}

MANIFEST = "MANIFEST_SHA256.json"


class GuardError(RuntimeError):
    """A precondition or integrity invariant failed; never treat as acceptance."""


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def blob_sha(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()


def strict_json(text: str) -> Any:
    def unique(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        out: dict[str, Any] = {}
        for key, val in pairs:
            if key in out:
                raise GuardError(f"duplicate JSON key: {key}")
            out[key] = val
        return out
    try:
        return json.loads(text, object_pairs_hook=unique,
                          parse_constant=lambda value: (_ for _ in ()).throw(
                              GuardError(f"nonfinite JSON constant: {value}")))
    except (json.JSONDecodeError, UnicodeError) as exc:
        raise GuardError(f"invalid JSON: {exc}") from exc


def safe_relative(rel: str) -> str:
    if (not isinstance(rel, str) or not rel or "\\" in rel or ":" in rel
            or any(ord(c) < 32 for c in rel)):
        raise GuardError(f"unsafe relative path: {rel!r}")
    p = PurePosixPath(rel)
    if (p.is_absolute() or PureWindowsPath(rel).drive
            or any(part in ("", ".", "..") for part in rel.split("/"))
            or p.as_posix() != rel):
        raise GuardError(f"noncanonical relative path: {rel!r}")
    return rel


def safe_path(root: Path, rel: str, *, allow_missing: bool = False) -> Path:
    safe_relative(rel)
    root = root.resolve(strict=True)
    p = root
    parts = rel.split("/")
    for i, part in enumerate(parts):
        p = p / part
        try:
            mode = p.lstat().st_mode
        except FileNotFoundError:
            if allow_missing:
                continue
            raise GuardError(f"missing member: {rel}") from None
        if stat.S_ISLNK(mode):
            raise GuardError(f"symlink path component: {p}")
        if i < len(parts) - 1 and not stat.S_ISDIR(mode):
            raise GuardError(f"non-directory parent: {p}")
        if i == len(parts) - 1 and not stat.S_ISREG(mode):
            raise GuardError(f"not a regular file: {rel}")
    return p


def read_member(root: Path, rel: str) -> bytes:
    return safe_path(root, rel).read_bytes()


def kit_members(root: Path) -> set[str]:
    result: set[str] = set()
    for directory, dirs, files in os.walk(root, followlinks=False):
        for name in dirs:
            if (Path(directory) / name).is_symlink():
                raise GuardError(f"symlink directory in kit: {name}")
        for name in files:
            p = Path(directory) / name
            rel = p.relative_to(root).as_posix()
            safe_path(root, rel)
            if rel != MANIFEST:
                result.add(rel)
    return result


def verify_manifest(root: Path) -> dict[str, bytes]:
    """Return the verified immutable payload bytes; do not reread before copying.

    A manifest detects accidental/tampered bytes relative to this distribution.
    It is not an externally authenticated signature of the publisher.
    """
    root = root.resolve(strict=True)
    obj = strict_json(read_member(root, MANIFEST).decode("utf-8"))
    if not isinstance(obj, dict) or obj.get("format") != "Permansson.KitManifest.v2":
        raise GuardError("unsupported kit manifest")
    records = obj.get("files")
    if not isinstance(records, dict) or not records:
        raise GuardError("empty or invalid manifest file map")
    expected = set(records)
    if len({path.casefold() for path in expected}) != len(expected):
        raise GuardError("case-colliding manifest paths are not portable")
    if MANIFEST in expected or kit_members(root) != expected:
        raise GuardError("manifest coverage differs from actual kit members")
    out: dict[str, bytes] = {}
    for rel, record in records.items():
        data = read_member(root, rel)
        if (not isinstance(record, dict) or type(record.get("bytes")) is not int
                or record["bytes"] != len(data) or record.get("sha256") != sha256(data)):
            raise GuardError(f"hash/length mismatch: {rel}")
        out[rel] = data
    return out


def git_bytes(repo: Path, *args: str) -> bytes:
    p = subprocess.run(["git", *args], cwd=repo, capture_output=True, timeout=90)
    if p.returncode:
        raise GuardError(f"git {' '.join(args)}: {p.stderr.decode('utf-8', 'replace').strip()}")
    return p.stdout


def git_text(repo: Path, *args: str) -> str:
    return git_bytes(repo, *args).decode("utf-8", "strict").strip()


def rewrite_root(data: bytes) -> bytes:
    """Canonical bytes only: no silent CRLF normalization of reviewed source."""
    if b"\r" in data or data.splitlines(keepends=True).count(ANCHOR) != 1:
        raise GuardError("expected one canonical LF root import anchor")
    old_lines = data.decode("utf-8").splitlines()
    if any(line.strip() in IMPORTS for line in old_lines):
        raise GuardError("new imports already present")
    return data.replace(ANCHOR, ANCHOR + b"".join((s + "\n").encode() for s in IMPORTS), 1)


def lean_code(text: str) -> str:
    """Remove nested Lean comments and quoted strings, preserving line breaks.

    This is a source guard, not a Lean parser or a substitute for axiom auditing.
    """
    out: list[str] = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1; out.extend("  "); i += 2
            elif text.startswith("-/", i):
                depth -= 1; out.extend("  "); i += 2
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif string:
            if text[i] == "\\" and i + 1 < len(text):
                out.extend("  "); i += 2
            elif text[i] == '"':
                string = False; out.append(" "); i += 1
            else:
                out.append("\n" if text[i] == "\n" else " "); i += 1
        elif text.startswith("/-", i):
            depth = 1; out.extend("  "); i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j < 0: j = len(text)
            out.extend(" " * (j - i)); i = j
        elif text[i] == '"':
            string = True; out.append(" "); i += 1
        else:
            out.append(text[i]); i += 1
    if depth or string:
        raise GuardError("unterminated Lean comment/string")
    return "".join(out)


def source_firewall(text: str) -> None:
    code = lean_code(text)
    bad = re.search(r"\b(sorry|admit|native_decide|axiom|unsafe|implemented_by|run_cmd)\b|#eval\b", code)
    if bad:
        raise GuardError(f"prohibited proof/source shortcut: {bad.group(0)}")


def parse_tree(raw: bytes) -> dict[str, tuple[str, str]]:
    out: dict[str, tuple[str, str]] = {}
    for record in raw.split(b"\0"):
        if not record: continue
        header, name = record.split(b"\t", 1)
        mode, kind, oid = header.decode("ascii").split()
        rel = name.decode("utf-8", "strict")
        safe_relative(rel)
        if kind != "blob" or mode not in {"100644", "100755"}:
            raise GuardError(f"unsupported base entry (symlink/submodule): {rel}")
        if rel in out: raise GuardError(f"duplicate tree entry: {rel}")
        out[rel] = (mode, oid)
    return out


def inspect_repo(repo: Path, *, pristine: bool = False) -> dict[str, Any]:
    """Check canonical baseline bytes and the exact authorized changed surface.

    Git index cleanliness alone is insufficient (assume-unchanged and filters).
    All baseline files are read and compared to the actual BASE Git blob IDs.
    """
    repo = repo.resolve(strict=True)
    if Path(git_text(repo, "rev-parse", "--show-toplevel")).resolve() != repo:
        raise GuardError("--repo must name the repository root")
    head = git_text(repo, "rev-parse", "HEAD")
    tree = git_text(repo, "rev-parse", "HEAD^{tree}")
    if git_text(repo, "rev-parse", f"{BASE}^{{tree}}") != BASE_TREE:
        raise GuardError("pinned baseline tree mismatch")
    git_bytes(repo, "merge-base", "--is-ancestor", BASE, "HEAD")
    branch = git_text(repo, "branch", "--show-current")
    status = git_bytes(repo, "status", "--porcelain=v1", "-z", "--untracked-files=all")
    if pristine:
        if head != BASE: raise GuardError("installation requires the exact PR79 base")
        if not branch or branch in {"main", "master"}:
            raise GuardError("installation requires a named feature branch, not detached/main/master")
        if status: raise GuardError("installation requires a clean worktree and index")
    if status:
        raise GuardError("source worktree or index is dirty")
    old = parse_tree(git_bytes(repo, "ls-tree", "-r", "-z", BASE))
    current = parse_tree(git_bytes(repo, "ls-tree", "-r", "-z", "HEAD"))
    if set(old) - set(current):
        raise GuardError("original provider path deleted")
    added = set(current) - set(old)
    if pristine and added:
        raise GuardError("installer requires exact PR79 base")
    if not pristine and set(NEW_FILES) - added:
        raise GuardError("missing A2-P02 modules or verifier in HEAD")
    if not pristine:
        for rel, oid in ACCEPTED_A2_PROOF_BLOBS.items():
            if current.get(rel) != ("100644", oid):
                raise GuardError(f"accepted A2-P02 mathematical provider identity changed: {rel}")
    modified_base = {rel for rel in old if old[rel] != current[rel]}
    if modified_base - {"PermanssonResearch.lean"}:
        raise GuardError(f"original provider objects changed: {sorted(modified_base - {'PermanssonResearch.lean'})}")
    if pristine and modified_base:
        raise GuardError("installer requires exact original provider tree")
    for revision_args in (("diff", "--name-only", "-z", BASE, "HEAD"),
                          ("diff", "--cached", "--name-only", "-z", BASE)):
        changed = {p.decode("utf-8") for p in git_bytes(repo, *revision_args).split(b"\0") if p}
        if changed - (added | {"PermanssonResearch.lean"}):
            raise GuardError(f"original provider paths modified: {sorted(changed - added - {'PermanssonResearch.lean'})}")
    original_root = git_bytes(repo, "show", f"{BASE}:PermanssonResearch.lean")
    if blob_sha(original_root) != ROOT_BLOB:
        raise GuardError("baseline Research root blob mismatch")
    expected_root = original_root if pristine else rewrite_root(original_root)
    actual_root = read_member(repo, "PermanssonResearch.lean")
    # The compiler contract is stable under additive *committed* research PRs.
    # Remove only their direct-import lines; all original root bytes must match.
    root_without_successors = actual_root
    if not pristine:
        successor_modules = {p for p in added
            if p.startswith("PermanssonResearch/") and p.endswith(".lean")}
        for rel in sorted(successor_modules):
            module = rel.removesuffix(".lean").replace("/", ".")
            imp = ("import " + module + "\n").encode("utf-8")
            if imp in expected_root:
                continue
            if root_without_successors.count(imp) != 1:
                raise GuardError(f"successor import absent or duplicated: {module}")
            root_without_successors = root_without_successors.replace(imp, b"", 1)
    if root_without_successors != expected_root:
        raise GuardError("Research root changed beyond original A2 imports plus additive direct imports")
    snapshots: dict[str, dict[str, Any]] = {}
    for rel, (mode, oid) in old.items():
        data = read_member(repo, rel)
        if blob_sha(data) != current[rel][1]:
            raise GuardError(f"worktree disagrees with HEAD blob: {rel}")
        if rel == "PermanssonResearch.lean":
            if data != actual_root:
                raise GuardError("Research root changed during source verification")
        elif blob_sha(data) != oid:
            raise GuardError(f"preserved baseline file changed: {rel}")
        if os.name != "nt" and bool(safe_path(repo, rel).stat().st_mode & 0o111) != (mode == "100755"):
            raise GuardError(f"preserved executable mode changed: {rel}")
        snapshots[rel] = {"sha256": sha256(data), "bytes": len(data), "git_mode": mode}
    for rel in (NEW_FILES if pristine else sorted(added)):
        dest = safe_path(repo, rel, allow_missing=True)
        if pristine:
            if dest.exists():
                raise GuardError(f"installer destination already exists: {rel}")
        else:
            mode, oid = current[rel]
            data = read_member(repo, rel)
            if blob_sha(data) != oid:
                raise GuardError(f"new file disagrees with HEAD blob: {rel}")
            if os.name != "nt" and bool(dest.stat().st_mode & 0o111) != (mode == "100755"):
                raise GuardError(f"new source executable mode differs from HEAD: {rel}")
            snapshots[rel] = {"sha256": sha256(data), "bytes": len(data), "git_mode": mode}
    listed = {p.decode("utf-8") for p in git_bytes(repo, "ls-files", "-z", "--cached",
                                                  "--others", "--exclude-standard").split(b"\0") if p}
    allowed = set(old) if pristine else set(current)
    if listed != allowed:
        raise GuardError(f"tracked/untracked paths differ from HEAD: {sorted(listed ^ allowed)}")
    # Ignored extra source files must not evade direct-import coverage.
    actual_research = {p.relative_to(repo).as_posix() for p in (repo / "PermanssonResearch").rglob("*.lean")}
    expected_research = {p for p in allowed if p.startswith("PermanssonResearch/") and p.endswith(".lean")}
    if actual_research != expected_research:
        raise GuardError("unexpected or absent research Lean modules")
    if not pristine:
        root_code = lean_code(actual_root.decode("utf-8"))
        imports = [line.strip()[7:] for line in root_code.splitlines() if line.strip().startswith("import ")]
        for path in expected_research:
            module = path.removesuffix(".lean").replace("/", ".")
            if imports.count(module) != 1: raise GuardError(f"missing/duplicate direct root import: {module}")
        for path in LIBRARIES: source_firewall(read_member(repo, path).decode("utf-8"))
    digest = sha256(json.dumps(snapshots, sort_keys=True, separators=(",", ":")).encode())
    return {"contract": CONTRACT, "base": BASE, "base_tree": BASE_TREE,
            "git_head": head, "git_head_tree": tree, "branch": branch,
            "dirty": bool(status), "git_status": status.decode("utf-8", "replace").split("\0"),
            "source_digest": digest, "files": snapshots,
            "baseline_files_checked": len(old), "research_modules": len(actual_research),
            "event_binding": "LOCAL_CHECKOUT_NOT_GITHUB_EVENT"}


def root_patch(data: bytes) -> bytes:
    import difflib
    return "".join(difflib.unified_diff(
        data.decode("utf-8").splitlines(keepends=True),
        rewrite_root(data).decode("utf-8").splitlines(keepends=True),
        fromfile="a/PermanssonResearch.lean", tofile="b/PermanssonResearch.lean", n=3
    )).encode("utf-8")


def overlay_patch(payload: dict[str, bytes], import_patch: bytes) -> bytes:
    """Complete review patch: exact root diff plus every registered new file."""
    import difflib
    chunks = [import_patch]
    for rel in NEW_FILES:
        data = payload[rel]
        if not data.endswith(b"\n") or b"\r" in data:
            raise GuardError(f"source overlay requires canonical LF text: {rel}")
        patch_text = "".join(difflib.unified_diff([], data.decode("utf-8").splitlines(keepends=True),
                                               fromfile="/dev/null", tofile="b/" + rel, n=3))
        chunks.append(patch_text.encode("utf-8"))
    return b"".join(chunks)
