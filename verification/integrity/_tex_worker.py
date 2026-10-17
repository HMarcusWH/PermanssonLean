"""Fresh isolated harness for the accepted TeX function; never builds artifacts."""
from __future__ import annotations

import hashlib
import importlib
import json
from pathlib import Path
import sys


def _fail(code, message):
    sys.stderr.write("PERMANSSON_TEX_ERROR " + json.dumps({"code": code, "message": message}) + "\n")
    return 1


def main(argv=None):
    args = sys.argv[1:] if argv is None else argv
    if len(args) != 6:
        return _fail("E_EXPORT_REFERENCE", "Invalid internal worker invocation")
    directory, revision, manuscript_hash, builder_hash, verifier_hash, manuscript_name = args
    trusted = Path(directory).resolve(strict=True)
    try:
        if not sys.flags.isolated or not sys.flags.no_site or not sys.flags.dont_write_bytecode:
            return _fail("E_IMPORT_ORIGIN", "Worker requires -I -S -B")
        for name, expected in (("build_release.py", builder_hash), ("verify_release.py", verifier_hash),
                               (manuscript_name, manuscript_hash)):
            path = trusted / name
            if path.parent != trusted or path.is_symlink() or not path.is_file():
                return _fail("E_REFERENCE_MISSING", "Trusted input is absent or not a regular file")
            if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
                return _fail("E_EXPORT_REFERENCE", "Trusted input digest mismatch")
        # -I -S excludes cwd, PYTHONPATH, user site and startup hooks. The only
        # added import location is the fresh directory populated by the parent.
        sys.path.insert(0, str(trusted))
        if "build_release" in sys.modules or "verify_release" in sys.modules:
            return _fail("E_IMPORT_ORIGIN", "Reference modules were already imported")
        builder = importlib.import_module("build_release")
        verifier = importlib.import_module("verify_release")
        for module, name in ((builder, "build_release.py"), (verifier, "verify_release.py")):
            if Path(module.__file__).resolve(strict=True) != trusted / name:
                return _fail("E_IMPORT_ORIGIN", "Reference module has an unexpected import origin")
        manuscript = (trusted / manuscript_name).read_bytes()
        if hashlib.sha256(manuscript).hexdigest() != manuscript_hash:
            return _fail("E_EXPORT_REFERENCE", "Manuscript changed before rendering")
        result = builder.tex_document(json.loads(manuscript), revision, manuscript_hash, False)
        if not isinstance(result, str):
            return _fail("E_EXPORT_REFERENCE", "Renderer did not return text")
        sys.stdout.buffer.write(result.encode("utf-8"))
        sys.stdout.buffer.flush()
        return 0
    except Exception as exc:
        return _fail("E_EXPORT_REFERENCE", f"Reference rendering failed: {type(exc).__name__}: {str(exc)[:1000]}")


if __name__ == "__main__":
    raise SystemExit(main())
