"""Independent companion probes; not the missing audit author's E1 program.

Read only the fixed accepted Git objects. No dependency installation, network,
Lean execution, release generation, repository settings or Git writes occur.
This documentation probe is not a replacement for the production gates.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile

A = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
TREE = "72ad841cc5b3cffc5f82979a9739b7fd03d75e15"
G = "5822cdff0fc360d9e368e10ff5f7576c3141a1b3"
PINS = {
    "manifest.json": "6065ec5431430f6804ebabffe636170d8bb349f08cfa817776b05a85bb6fe127",
    "build_release.py": "a711fce840920846e9ffdd55b2580ebe358233ca7b432bffa78af315be69ffa6",
    "verify_release.py": "abe1cd70491b4976ab7e3d1f06c405508e2fde7e3890f818a89b97ed88841dc2",
    "manuscript.json": "8022291f1ec19961578bdcb60f205fdec31057982bf9a78f6b9610bd3b184239",
    "output/pdf/Permansson_Research_Companion_v0.2.0.tex": "3524da1f1ef92cfee179917efebeb3c2786b8ad484653d2f1c8f4d8036952416",
}
OUTER = (b"release/Permansson_v0.2.0_research-kit.zip",
         b"release/Permansson_v0.2.0_research-kit.zip.sha256")
ZIP_SHA256 = "4db31db5b805ad2f455f27e5a2e013cd13ea257984e174f6453af8f8db5b1f6c"
MAX_BLOB = 64 * 1024 * 1024
WORKER = r'''
import hashlib,importlib,json,sys
from pathlib import Path
trusted=Path(sys.argv[1]).resolve(strict=True)
sys.path.insert(0,str(trusted))
builder=importlib.import_module("build_release")
helper=importlib.import_module("verify_release")
for module,name in ((builder,"build_release.py"),(helper,"verify_release.py")):
    if Path(module.__file__).resolve(strict=True)!=trusted/name:
        raise RuntimeError("Unexpected accepted-module import origin")
raw=(trusted/"manuscript.json").read_bytes()
sys.stdout.buffer.write(builder.tex_document(json.loads(raw),sys.argv[2],hashlib.sha256(raw).hexdigest(),False).encode("utf-8"))
'''


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def command(args, *, cwd, env, input=None, limit=MAX_BLOB, timeout=60):
    with tempfile.TemporaryFile() as out, tempfile.TemporaryFile() as err:
        process = subprocess.Popen(args, cwd=cwd, env=env,
                                   stdin=subprocess.PIPE if input is not None else subprocess.DEVNULL,
                                   stdout=out, stderr=err)
        try:
            process.communicate(input=input, timeout=timeout)
        except subprocess.TimeoutExpired:
            process.kill()
            process.communicate()
            raise RuntimeError("Probe subprocess timed out")
        require(out.tell() <= limit and err.tell() <= 8192, "Probe output exceeds its budget")
        out.seek(0)
        err.seek(0)
        diagnostic = err.read(8192).decode("utf-8", "replace")
        require(process.returncode == 0, "Probe subprocess failed: " + diagnostic)
        return out.read(limit + 1)


def reproduce(repo):
    git_path = shutil.which("git")
    require(git_path is not None, "Git is required; no objects are fetched automatically")
    env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
    env.update({"GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                "GIT_NO_REPLACE_OBJECTS": "1", "GIT_NO_LAZY_FETCH": "1", "GIT_TERMINAL_PROMPT": "0"})

    def git(*args, input=None, limit=MAX_BLOB):
        return command([git_path, "--no-replace-objects", "-c", "protocol.allow=never", "-C", str(repo), *args],
                       cwd=repo, env=env, input=input, limit=limit)

    cache = {}

    def object_bytes(oid, kind):
        if oid not in cache:
            raw = git("cat-file", "--batch", input=(oid + "\n").encode(), limit=MAX_BLOB + 256)
            header, sep, rest = raw.partition(b"\n")
            require(sep and len(header.split()) == 3, "Missing or invalid fixed Git object")
            observed, actual_kind, size_text = header.split()
            size = int(size_text)
            require(observed == oid.encode() and size <= MAX_BLOB and len(rest) == size + 1
                    and rest.endswith(b"\n"), "Git object identity/length mismatch")
            data = rest[:-1]
            require(hashlib.sha1(actual_kind + b" " + str(size).encode() + b"\0" + data).hexdigest() == oid,
                    "Git object payload does not match its name")
            cache[oid] = (actual_kind.decode("ascii"), data)
        actual_kind, data = cache[oid]
        require(actual_kind == kind, "Unexpected Git object type")
        return data

    accepted = object_bytes(A, "commit")
    require(accepted.startswith(("tree " + TREE + "\n").encode()), "Accepted tree differs from fixed pin")
    object_bytes(TREE, "tree")
    entries = {}
    for record in git("ls-tree", "-r", "-z", "--full-tree", A, limit=2 * 1024 * 1024).split(b"\0"):
        if record:
            header, path = record.split(b"\t", 1)
            mode, kind, oid = header.decode("ascii").split()
            require(path not in entries, "Duplicate Git path")
            entries[path] = (mode, kind, oid)

    def blob(path):
        mode, kind, oid = entries[path]
        require(kind == "blob" and mode in {"100644", "100755"}, "Expected a regular accepted file")
        return object_bytes(oid, "blob")

    inputs = {name: blob(b"release/v0.2.0/" + name.encode()) for name in PINS}
    for name, expected in PINS.items():
        require(sha256(inputs[name]) == expected, "Fixed accepted input digest differs: " + name)
    manifest = json.loads(inputs["manifest.json"])
    historical = manifest["protected_files"]
    require(len(historical) == 340, "Historical entry count differs")
    protected = []
    for row in historical:
        path = row["path"].encode("ascii")
        mode, kind, oid = entries[path]
        payload = blob(path)
        require((mode, kind, oid) == (row["mode"], "blob", row["git_blob_sha1"])
                and sha256(payload) == row["sha256"], "Historical protected entry differs")
        protected.append(dict(path=path.decode(), group="historical", mode=mode, oid=oid,
                              sha256=sha256(payload), size=len(payload)))
    release_paths = sorted({path for path in entries if path.startswith(b"release/v0.2.0/")} | set(OUTER))
    require(len(release_paths) == 29 and sha256(blob(OUTER[0])) == ZIP_SHA256, "Accepted release envelope differs")
    for path in release_paths:
        mode, _kind, oid = entries[path]
        payload = blob(path)
        protected.append(dict(path=path.decode(), group="release_v020", mode=mode, oid=oid,
                              sha256=sha256(payload), size=len(payload)))
    require(len({row["path"] for row in protected}) == 369, "Protected groups overlap")
    protected.sort(key=lambda row: row["path"])
    registry = json.loads((repo / "docs/hardening/registries/protected_inventory_369.json").read_bytes())
    require(registry["entries"] == protected, "Companion registry differs from accepted Git derivation")

    with tempfile.TemporaryDirectory(prefix="permansson-companion-probe-") as directory:
        trusted = Path(directory).resolve()
        for name in ("build_release.py", "verify_release.py", "manuscript.json"):
            (trusted / name).write_bytes(inputs[name])
        isolated_env = {key: value for key, value in env.items() if not key.upper().startswith("PYTHON")}
        def render(revision):
            return command([sys.executable, "-I", "-S", "-B", "-c", WORKER, str(trusted), revision],
                           cwd=trusted, env=isolated_env, limit=2 * 1024 * 1024, timeout=30)
        tex = render(G)
        wrong = render(A)
    tex_name = "output/pdf/Permansson_Research_Companion_v0.2.0.tex"
    require(tex == inputs[tex_name] and len(tex) == 71379 and sha256(tex) == PINS[tex_name],
            "Independent accepted export differs")
    require(tex.count(b"\n\\companionEquation{") == 10 and tex != wrong, "Renderer regression control failed")
    return {
        "format": "Permansson.Hardening.CompanionSourceProbes.v1", "schema_version": 1,
        "status": "PASS", "provenance": "NEW_INDEPENDENT_REPRODUCTION_NOT_ORIGINAL_E1",
        "executed_at_utc": datetime.now(timezone.utc).isoformat(),
        "reference": {"accepted_release": A, "accepted_tree": TREE, "research_source": G},
        "runtime": {"python": platform.python_version(), "platform": platform.system(),
                    "git": git("--version").decode().strip()},
        "script": {"path": "docs/hardening/contract/evidence/reproduce_source_probes.py",
                   "sha256": sha256(Path(__file__).read_bytes())},
        "original_audit_inputs": {
            "author_source_register": "NOT_SUPPLIED",
            "author_E1_program_and_results": "NOT_SUPPLIED",
            "author_source_zip": {"status": "NOT_SUPPLIED", "reconstruction_performed_here": False,
                                  "author_reported_sha256": "e1cae51533373cd87a1a8e82ea9d94fb72c048a45c1af66c6cf03843d723017b"},
            "original_proposal_file": "NOT_SUPPLIED"},
        "checks": [
            {"id": "COMPANION-REF", "status": "PASS", "accepted_tree_file_count": len(entries),
             "input_sha256": {name: sha256(data) for name, data in inputs.items()}},
            {"id": "COMPANION-INVENTORY", "status": "PASS", "historical": 340, "release": 29,
             "unique_total": 369, "canonical_bytes": sum(row["size"] for row in protected),
             "matches_companion_registry": True},
            {"id": "COMPANION-EXPORT", "status": "PASS", "bytes": len(tex), "sha256": sha256(tex),
             "equation_records": 10, "isolation_flags": ["-I", "-S", "-B"], "pdf_build_called": False},
            {"id": "COMPANION-WRONG-REVISION", "status": "PASS", "control_revision": A,
             "control_sha256": sha256(wrong), "differs_from_correct_export": True}],
        "not_performed": ["original source ZIP reconstruction", "original author toy-bundle probes",
                          "live main/protection/ruleset reads", "GitHub CI acceptance", "network-isolated archive replay",
                          "fresh Lean execution", "publisher authentication", "administrative rollout"]}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parents[4])
    parser.add_argument("--output", type=Path, help="Optional new result file; never overwrites")
    args = parser.parse_args()
    try:
        result = reproduce(args.repo.resolve())
        encoded = (json.dumps(result, sort_keys=True, indent=2) + "\n").encode()
        if args.output is not None:
            with args.output.open("xb") as stream:
                stream.write(encoded)
        sys.stdout.buffer.write(encoded)
        return 0
    except Exception as exc:
        print("Independent companion probe FAILED: " + str(exc)[:2000], file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
