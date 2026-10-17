"""Independently replay archived PR78 evidence; never invokes Lean."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parents[2] / "PermanssonLean-hardening"
HERE = Path(__file__).resolve().parent
ACCEPTED = "d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618"
SOURCE = {
    "repository": "HMarcusWH/PermanssonLean", "pr_number": 78,
    "head_sha": "ed8309843eedbd6cfe56b5e543c99285e28cead5",
    "base_sha": ACCEPTED,
    "synthetic_merge_sha": "4403ec593fe3178495b6633c9221ccd0e49bc166",
}
archive = HERE / "PR78-final-acceptance-c10.zip"
payload = archive.read_bytes()
digest = hashlib.sha256(payload).hexdigest()
if len(payload) != 9376 or digest != "3722dd43bc42277c6e3b100c7e37348126b6cb2a7f592d26275a41b707db34ff":
    raise ValueError("Publisher ZIP byte identity differs")
checked_sources = {}
paths = subprocess.check_output(["git", "-C", str(ROOT), "ls-tree", "-r", "--name-only", ACCEPTED,
                                 "verification/research"]).decode().splitlines()
closure = [path for path in paths if Path(path).name.startswith("c10_") and path.endswith(".py")]
closure.append("release/v0.2.0/c10_archive_validation.py")
with TemporaryDirectory(prefix="pr78-frozen-c10-") as temporary:
    canonical = Path(temporary)
    for relative in closure:
        frozen = subprocess.check_output(["git", "-C", str(ROOT), "show", ACCEPTED + ":" + relative])
        destination = canonical / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(frozen)
        checked_sources[relative] = hashlib.sha256(frozen).hexdigest()
    if checked_sources["release/v0.2.0/c10_archive_validation.py"] != "36dfefb05c863e46b50e17b0dcf5d397016b5420b05244367af89c98a5968706":
        raise ValueError("Accepted archive helper differs from its pinned digest")
    # Only Git object reads occur through this link. No original index, ref,
    # configuration, working file or object is written by this consistency run.
    git_dir = subprocess.check_output(["git", "-C", str(ROOT), "rev-parse", "--absolute-git-dir"]).decode().strip()
    (canonical / ".git").write_text("gitdir: " + git_dir + "\n", encoding="utf-8")
    sys.path.insert(0, str(canonical / "release/v0.2.0"))
    from c10_archive_validation import validate_c10_archive
    result = validate_c10_archive(archive, SOURCE, canonical)
record = {
    "format": "Permansson.PR78.C10Consistency.v1", "source": SOURCE,
    "publisher_artifact": 12113010574, "publisher_run": 39063559009,
    "publisher_zip_size": len(payload), "publisher_zip_sha256": digest,
    "accepted_helper_sha256": checked_sources, "result": result,
    "scope": "Archived source-bound structural/arithmetic/compiler-capture consistency; no local Lean execution",
}
(HERE / "c10-consistency.json").write_text(json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8")
print(json.dumps({"status": result["status"], "compiler_rerun": result["compiler_rerun"],
                  "sha256": digest, "bytes": len(payload)}))
