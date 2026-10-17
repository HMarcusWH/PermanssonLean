"""Private real-Git fixtures; no fixture authority is exposed by production CLI."""

from dataclasses import replace
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

from verification.integrity.git_objects import GitRepo
from verification.integrity.inventory import _load_reference_inventory
from verification.integrity.policy import _InventoryPolicy, CLOSED_ROOTS
from verification.integrity.preservation import compare_preserved


def json_bytes(data):
    return (json.dumps(data, sort_keys=True, indent=2) + "\n").encode()


class GitFixture:
    def __init__(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="permansson-integrity-fixture-")
        self.root = Path(self.temporary.name)
        env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        subprocess.run([shutil.which("git"), "init", "-q", str(self.root)],
                       check=True, capture_output=True, env=env)
        self.repo = GitRepo(self.root)
        # Raw Git paths can be legal in objects while impossible to materialize
        # on Windows. These fixtures never check out the adversarial names.
        self.repo.run("config", "core.protectNTFS", "false")
        self.repo.env["GIT_INDEX_FILE"] = str(self.root / ".git" / "fixture-index")
        self.counter = 0
        self.files = {
            b"PermanssonLean/Regime/Constitution.lean": b"theorem original : True := True.intro\n",
            b"PermanssonResearch/ReverseSolver/C10ReceiptSemantics.lean": b"-- D0 original\n",
            b"paper/original.md": b"Accepted paper\n",
            b"PermanssonLean.lean": b"import PermanssonLean.Regime.Constitution\n",
        }
        rows = [{"path": path.decode(), "mode": "100644", "git_blob_sha1": self.blob(data),
                 "sha256": hashlib.sha256(data).hexdigest()} for path, data in sorted(self.files.items())]
        self.manifest = {
            "schema_version": 1, "version": "0.2.0", "mode": "final",
            "baseline_sha": "1" * 40, "selected_source_sha": "2" * 40,
            "accepted_source_sha": "2" * 40, "protected_files": rows,
        }
        manifest = json_bytes(self.manifest)
        self.files.update({
            b"release/v0.2.0/manifest.json": manifest,
            b"release/v0.2.0/manuscript.json": b'{"F1.MA2":"OPEN"}\n',
            b"release/v0.2.0/output.tex": b"Original equation\n",
            b"release/Permansson_v0.2.0_research-kit.zip": b"fixture ZIP\n",
            b"release/Permansson_v0.2.0_research-kit.zip.sha256": b"original checksum\n",
        })
        self.accepted = self.commit({path: ("100644", data) for path, data in self.files.items()}, parent=None)
        self.repo.run("update-ref", "refs/heads/main", self.accepted)
        self.repo.run("symbolic-ref", "HEAD", "refs/heads/main")
        self.policy = _InventoryPolicy(
            self.accepted, self.repo.commit(self.accepted).tree, "1" * 40, "2" * 40,
            hashlib.sha256(manifest).hexdigest(), historical_count=4, release_count=5,
        )

    def close(self):
        self.repo._config.cleanup()
        self.temporary.cleanup()

    def blob(self, data):
        return self.repo.run("hash-object", "-w", "--stdin", input=data).strip().decode()

    def commit(self, changes, parent="accepted"):
        if parent == "accepted":
            parent = self.accepted
        self.repo.run("read-tree", parent if parent else "--empty")
        existing = self.repo.tree(parent) if parent else {}
        records = []
        zero = "0" * 40
        for path, replacement in changes.items():
            # Root replacement has to remove all old descendants from the index.
            for child in sorted(existing):
                if child.startswith(path + b"/"):
                    records.append(b"0 " + zero.encode() + b"\t" + child + b"\0")
            if replacement is None:
                records.append(b"0 " + zero.encode() + b"\t" + path + b"\0")
            else:
                mode, content = replacement
                oid = content if isinstance(content, str) else self.blob(content)
                records.append(mode.encode() + b" " + oid.encode() + b"\t" + path + b"\0")
        if records:
            self.repo.run("update-index", "-z", "--index-info", input=b"".join(records))
        tree = self.repo.run("write-tree").strip().decode()
        self.counter += 1
        args = ["-c", "user.name=Integrity Fixture", "-c", "user.email=fixture@example.invalid",
                "commit-tree", tree, "-m", "fixture " + str(self.counter)]
        if parent:
            args.extend(["-p", parent])
        return self.repo.run(*args).strip().decode()

    def compare(self, candidate):
        reference = _load_reference_inventory(self.repo, self.policy)
        return compare_preserved(reference, self.repo.tree(self.accepted),
                                 self.repo.tree(candidate), self.repo.blob,
                                 closed_roots=self.policy.closed_roots)

    def malformed_authority(self, manifest=None, *, files=None, **policy_changes):
        """Create an explicit private authority to reach post-hash parser checks."""
        payload = manifest if isinstance(manifest, bytes) else json_bytes(manifest or self.manifest)
        changes = {self.policy.manifest_path: ("100644", payload)}
        if files:
            changes.update(files)
        commit = self.commit(changes)
        return replace(self.policy, accepted_release=commit,
                       accepted_tree=self.repo.commit(commit).tree,
                       manifest_sha256=hashlib.sha256(payload).hexdigest(), **policy_changes)
