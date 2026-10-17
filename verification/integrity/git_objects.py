"""Canonical, bounded Git plumbing. Never repairs or lazily fetches history."""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import threading
from collections import OrderedDict

from .reports import HardeningError

HEX40 = re.compile(r"[0-9a-f]{40}\Z")
MAX_BLOB = 64 * 1024 * 1024
MAX_COMMAND = 256 * 1024 * 1024
MAX_TREE_DEPTH = 128
MAX_TREE_ENTRIES = 200000
MAX_TREE_CACHE_BYTES = 128 * 1024 * 1024


@dataclass(frozen=True)
class GitEntry:
    path: bytes
    mode: str
    object_type: str
    oid: str


@dataclass(frozen=True)
class Commit:
    oid: str
    tree: str
    parents: tuple[str, ...]


def full_oid(value):
    if not isinstance(value, str) or not HEX40.fullmatch(value):
        raise HardeningError("E_REFERENCE_ID", "Expected a complete lowercase 40-hex object identity", 2)
    return value


class GitRepo:
    def __init__(self, root, *, preflight=True):
        self.root = Path(root).resolve()
        self.executable = shutil.which("git")
        if not self.executable:
            raise HardeningError("E_DEPENDENCY_MISSING", "Git is unavailable", 3)
        self._config = tempfile.TemporaryDirectory(prefix="permansson-git-config-")
        self._cache = OrderedDict()
        self._cache_size = 0
        self._tree_nodes = OrderedDict()
        self._tree_nodes_size = 0
        self._tree_views = OrderedDict()
        self._tree_views_entries = 0
        self._tree_views_size = 0
        self.inherited = {key: value for key, value in os.environ.items()
                          if key.startswith("GIT_") and key not in {"GIT_TRACE", "GIT_TRACE2"}}
        self.env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        self.env.update({"GIT_NO_REPLACE_OBJECTS": "1", "GIT_NO_LAZY_FETCH": "1",
                         "GIT_TERMINAL_PROMPT": "0", "GIT_CONFIG_NOSYSTEM": "1",
                         "GIT_CONFIG_GLOBAL": os.devnull, "LC_ALL": "C",
                         "HOME": self._config.name, "XDG_CONFIG_HOME": self._config.name})
        self._validate_root()
        if preflight:
            self.preflight()

    def close(self):
        self._config.cleanup()

    def __del__(self):
        if hasattr(self, "_config"):
            self._config.cleanup()

    def _validate_root(self):
        try:
            raw = self.run("rev-parse", "--absolute-git-dir").strip()
            self.git_dir = Path(os.fsdecode(raw)).resolve()
            raw = self.run("rev-parse", "--git-common-dir").strip()
            common = Path(os.fsdecode(raw))
            self.common_dir = (self.root / common).resolve() if not common.is_absolute() else common.resolve()
        except HardeningError as exc:
            raise HardeningError("E_REFERENCE_MISSING", "Not a repository with an object database") from exc

    def run(self, *args, input=None, timeout=60, limit=MAX_COMMAND):
        command = [self.executable, "--no-replace-objects", "-c", "core.hooksPath=" + self._config.name,
                   "-c", "protocol.allow=never", "-c", "gc.auto=0", "-C", str(self.root), *map(str, args)]
        # File-backed capture bounds memory even for maliciously large plumbing output.
        with tempfile.TemporaryFile() as stdout, tempfile.TemporaryFile() as stderr:
            stopped = threading.Event()
            exceeded = []
            try:
                process = subprocess.Popen(command, env=self.env, stdin=subprocess.PIPE if input is not None else subprocess.DEVNULL,
                                           stdout=stdout, stderr=stderr)
                def monitor():
                    while not stopped.wait(0.02):
                        if os.fstat(stdout.fileno()).st_size > limit or os.fstat(stderr.fileno()).st_size > 128 * 1024:
                            exceeded.append(True)
                            process.kill()
                            return
                watcher = threading.Thread(target=monitor, daemon=True)
                watcher.start()
                process.communicate(input=input, timeout=timeout)
            except subprocess.TimeoutExpired as exc:
                process.kill()
                process.communicate()
                raise HardeningError("E_COMMAND_TIMEOUT", "Git subprocess exceeded its time budget") from exc
            finally:
                stopped.set()
                if 'watcher' in locals():
                    watcher.join()
            if exceeded:
                raise HardeningError("E_LIMIT", "Git subprocess exceeded its output budget")
            stdout.seek(0, 2)
            size = stdout.tell()
            if size > limit:
                raise HardeningError("E_LIMIT", f"Git output exceeds {limit} bytes")
            stdout.seek(0)
            output = stdout.read(limit + 1)
            stderr.seek(0)
            diagnostic = stderr.read(8192).decode("utf-8", "replace")
            if process.returncode:
                raise HardeningError("E_GIT", f"Git {args[0] if args else ''} failed: {diagnostic[:2000]}")
            return output

    def preflight(self):
        dangerous = {"GIT_DIR", "GIT_COMMON_DIR", "GIT_WORK_TREE", "GIT_OBJECT_DIRECTORY",
                     "GIT_ALTERNATE_OBJECT_DIRECTORIES", "GIT_NAMESPACE", "GIT_INDEX_FILE",
                     "GIT_CONFIG", "GIT_CONFIG_COUNT", "GIT_CONFIG_PARAMETERS", "GIT_REPLACE_REF_BASE"}
        if any(self.inherited.get(key) for key in dangerous):
            raise HardeningError("E_HISTORY_EXTERNAL", "Inherited Git redirection is unsupported")
        if self.run("rev-parse", "--is-shallow-repository").strip() == b"true":
            raise HardeningError("E_HISTORY_SHALLOW", "Shallow history is unsupported")
        if self.run("for-each-ref", "--format=%(refname)", "refs/replace").strip():
            raise HardeningError("E_HISTORY_EXTERNAL", "Git replacement refs are unsupported")
        for path in (self.common_dir / "info/grafts", self.common_dir / "objects/info/alternates",
                     self.common_dir / "objects/info/http-alternates"):
            if path.exists() and path.stat().st_size:
                raise HardeningError("E_HISTORY_EXTERNAL", "External/grafted object history is unsupported")
        config = self.run("config", "--null", "--list")
        if re.search(rb"(?:extensions\.partialclone|remote\.[^\x00\n]*\.(?:promisor|partialclonefilter))\n", config, re.I):
            raise HardeningError("E_HISTORY_EXTERNAL", "Promisor/partial-clone history is unsupported")
        if list((self.common_dir / "objects/pack").glob("*.promisor")):
            raise HardeningError("E_HISTORY_EXTERNAL", "Promisor packs are unsupported")

    def object(self, oid, *, limit=MAX_BLOB):
        full_oid(oid)
        if oid in self._cache:
            object_type, content = self._cache[oid]
            if len(content) > limit:
                raise HardeningError("E_LIMIT", "Object exceeds size budget")
            self._cache.move_to_end(oid)
            return object_type, content
        metadata = self.run("cat-file", "--batch-check", input=(oid + "\n").encode(), limit=256).strip().split()
        if len(metadata) != 3 or metadata[0] != oid.encode() or not metadata[2].isdigit():
            raise HardeningError("E_REFERENCE_MISSING", f"Missing object: {oid}")
        if int(metadata[2]) > limit:
            raise HardeningError("E_LIMIT", "Object exceeds size budget before payload read")
        data = self.run("cat-file", "--batch", input=(oid + "\n").encode(), limit=limit + 256)
        header, sep, payload = data.partition(b"\n")
        fields = header.split()
        if not sep or len(fields) != 3 or fields[0] != oid.encode():
            raise HardeningError("E_REFERENCE_MISSING", f"Missing object: {oid}")
        try:
            size = int(fields[2])
        except ValueError as exc:
            raise HardeningError("E_GIT_OBJECT", "Invalid object header") from exc
        if size < 0 or size > limit:
            raise HardeningError("E_LIMIT", "Object exceeds size budget")
        if len(payload) != size + 1 or payload[-1:] != b"\n":
            raise HardeningError("E_GIT_OBJECT", "Object payload length mismatch")
        object_type = fields[1].decode("ascii")
        content = payload[:-1]
        digest = hashlib.sha1(object_type.encode() + b" " + str(size).encode() + b"\0" + content).hexdigest()
        if digest != oid:
            raise HardeningError("E_GIT_OBJECT", "Object content does not match its identity")
        while self._cache and self._cache_size + len(content) > 128 * 1024 * 1024:
            _, (_, removed) = self._cache.popitem(last=False)
            self._cache_size -= len(removed)
        if len(content) <= 128 * 1024 * 1024:
            self._cache[oid] = (object_type, content)
            self._cache_size += len(content)
        return object_type, content

    def blob(self, oid, limit=None):
        object_type, content = self.object(oid, limit=MAX_BLOB if limit is None else limit)
        if object_type != "blob":
            raise HardeningError("E_PROTECTED_TYPE", "Expected a canonical blob object")
        return content

    def commit(self, sha):
        full_oid(sha)
        object_type, content = self.object(sha, limit=2 * 1024 * 1024)
        if object_type != "commit":
            raise HardeningError("E_REFERENCE_ID", "Object is not a commit")
        headers = content.split(b"\n\n", 1)[0].splitlines()
        trees = [line[5:].decode("ascii") for line in headers if line.startswith(b"tree ")]
        parents = tuple(line[7:].decode("ascii") for line in headers if line.startswith(b"parent "))
        if len(trees) != 1:
            raise HardeningError("E_GIT_OBJECT", "Commit has an invalid tree header")
        full_oid(trees[0])
        for parent in parents:
            full_oid(parent)
        return Commit(sha, trees[0], parents)

    def tree(self, sha):
        full_oid(sha)
        root = self.commit(sha).tree
        canonical, _directories, _count, _size = self._canonical_tree(root)
        observed = self._parse_tree(self.run("ls-tree", "-r", "-z", "--full-tree", sha))
        if observed != canonical:
            raise HardeningError("E_GIT_OBJECT", "ls-tree differs from independently hashed canonical tree objects")
        return dict(canonical)

    def tree_entries(self, sha):
        """Verified leaves and actual tree entries, including empty subtrees."""
        entries = self.tree(sha)
        _leaves, directories, _count, _size = self._canonical_tree(self.commit(sha).tree)
        entries.update(directories)
        return entries

    def _tree_records(self, oid):
        """Hash-check a tree and parse its direct, byte-relative entries once."""
        if oid in self._tree_nodes:
            self._tree_nodes.move_to_end(oid)
            return self._tree_nodes[oid][0]
        object_type, content = self.object(oid)
        if object_type != "tree":
            raise HardeningError("E_GIT_OBJECT", "Directory entry does not name a tree object")
        position = 0
        records = []
        seen = set()
        modes = {b"40000": ("040000", "tree"), b"100644": ("100644", "blob"),
                 b"100755": ("100755", "blob"), b"120000": ("120000", "blob"),
                 b"160000": ("160000", "commit")}
        while position < len(content):
            space = content.find(b" ", position)
            end = content.find(b"\0", space + 1) if space >= 0 else -1
            if space < 0 or end < 0 or end + 21 > len(content):
                raise HardeningError("E_GIT_OBJECT", "Truncated canonical tree record")
            raw_mode = content[position:space]
            name = content[space + 1:end]
            if (raw_mode not in modes or not name or name in (b".", b"..")
                    or b"/" in name or name in seen):
                raise HardeningError("E_GIT_OBJECT", "Invalid canonical tree name or mode")
            seen.add(name)
            mode, entry_type = modes[raw_mode]
            child_oid = content[end + 1:end + 21].hex()
            records.append(GitEntry(name, mode, entry_type, child_oid))
            if len(records) > MAX_TREE_ENTRIES:
                raise HardeningError("E_LIMIT", "Tree entry count exceeds policy budget")
            position = end + 21
        records = tuple(records)
        weight = len(content) + sum(len(entry.path) + 128 for entry in records)
        while self._tree_nodes and self._tree_nodes_size + weight > MAX_TREE_CACHE_BYTES:
            _, (_, removed) = self._tree_nodes.popitem(last=False)
            self._tree_nodes_size -= removed
        if weight <= MAX_TREE_CACHE_BYTES:
            self._tree_nodes[oid] = (records, weight)
            self._tree_nodes_size += weight
        return records

    def _canonical_tree(self, root):
        """Walk verified tree payloads; gitlink targets are deliberately opaque."""
        if root in self._tree_views:
            self._tree_views.move_to_end(root)
            return self._tree_views[root]
        leaves = {}
        directories = {}
        count = 0
        weight = 0
        stack = [(root, b"", 0)]
        while stack:
            oid, prefix, depth = stack.pop()
            if depth > MAX_TREE_DEPTH:
                raise HardeningError("E_LIMIT", "Tree nesting exceeds policy depth")
            for relative in self._tree_records(oid):
                path = prefix + relative.path
                count += 1
                weight += len(path) + 128
                if count > MAX_TREE_ENTRIES or weight > MAX_TREE_CACHE_BYTES:
                    raise HardeningError("E_LIMIT", "Expanded tree exceeds policy entry/size budget")
                entry = GitEntry(path, relative.mode, relative.object_type, relative.oid)
                if path in leaves or path in directories:
                    raise HardeningError("E_GIT_OBJECT", "Duplicate canonical expanded tree path")
                if entry.object_type == "tree":
                    directories[path] = entry
                    stack.append((entry.oid, path + b"/", depth + 1))
                else:
                    leaves[path] = entry
        view = (leaves, directories, count, weight)
        while self._tree_views and (self._tree_views_entries + count > MAX_TREE_ENTRIES
                                   or self._tree_views_size + weight > MAX_TREE_CACHE_BYTES):
            _, (_, _, removed_count, removed_size) = self._tree_views.popitem(last=False)
            self._tree_views_entries -= removed_count
            self._tree_views_size -= removed_size
        self._tree_views[root] = view
        self._tree_views_entries += count
        self._tree_views_size += weight
        return view

    @staticmethod
    def _parse_tree(data):
        result = {}
        for record in data.split(b"\0"):
            if not record:
                continue
            header, sep, path = record.partition(b"\t")
            fields = header.split()
            if not sep or len(fields) != 3 or path in result:
                raise HardeningError("E_GIT_OBJECT", "Invalid NUL-delimited tree record")
            mode, object_type, oid = (value.decode("ascii") for value in fields)
            full_oid(oid)
            result[path] = GitEntry(path, mode, object_type, oid)
        return result

    def entry(self, sha, path):
        full_oid(sha)
        raw_path = path if isinstance(path, bytes) else os.fsencode(path)
        # Use the same full validated traversal as the recursive API. Returning a
        # cached relative record alone would miss corruption in an ancestor tree.
        leaves = self.tree(sha)
        if raw_path in leaves:
            return leaves[raw_path]
        _leaves, directories, _count, _size = self._canonical_tree(self.commit(sha).tree)
        return directories.get(raw_path)

    def validate_candidate(self, candidate, *, accepted_sha, accepted_tree=None, require_ancestry=True):
        full_oid(candidate)
        try:
            authority = self.commit(accepted_sha)
        except HardeningError as exc:
            raise HardeningError("E_REFERENCE_MISSING", "Accepted reference commit is unavailable") from exc
        if accepted_tree is not None and authority.tree != accepted_tree:
            raise HardeningError("E_REFERENCE_ID", "Accepted reference tree disagrees with fixed policy")
        commit = self.commit(candidate)
        if require_ancestry:
            try:
                self.run("merge-base", "--is-ancestor", accepted_sha, candidate)
            except HardeningError as exc:
                raise HardeningError("E_ANCESTRY", "Candidate does not descend from accepted release") from exc
        return commit
