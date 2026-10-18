"""Compile, semantically falsify, and audit the exact supplied X1 matrices."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time

import generate_x1_matrix_tables as generator
from test_x1_paper_closure import (ALLOWED, MODULES, classify_mutation,
                                  declaration_names, sha256, changed_files)

ROOT = generator.ROOT
MODULE = "PermanssonResearch.X1.ExactMatrixTables"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("PERMANSSON_X1_LEAN"))
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    command = [args.lean] if args.lean else ["lake", "env", "lean"]
    scratch = ROOT / ".lake/x1-matrix-closure"
    scratch.mkdir(parents=True, exist_ok=True)
    receipt_path = scratch / "receipt.json"
    source_relative = "PermanssonResearch/X1/ExactMatrixTables.lean"
    artifact_relative = ".lake/build/lib/lean/PermanssonResearch/X1/ExactMatrixTables.olean"
    source, artifact = ROOT / source_relative, ROOT / artifact_relative
    inputs = [source, generator.CERTIFICATE, Path(generator.__file__), Path(__file__),
              ROOT / "verification/research/test_x1_paper_closure.py",
              ROOT / "verification/research/test_paper_x1_matrix_lean.py"]
    inputs += [ROOT / f"PermanssonResearch/X1/{name}.lean" for name in MODULES]
    hashes = {path.relative_to(ROOT).as_posix(): sha256(path) for path in inputs}
    receipt = {"status": "RUNNING", "module": MODULE, "matrix_count": 8,
               "entries_per_matrix": 324, "literal_entries": 2592,
               "source_sha256": hashes, "compiler_command": command,
               "exact_certificate_rendering": source.read_bytes() == generator.render().encode("utf-8"),
               "positive_control": {}, "mutations": {}, "axiom_audit": {}}

    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")

    def run(label: str, arguments: list[str]):
        print("Checking", label, flush=True)
        started = time.monotonic()
        try:
            completed = subprocess.run(command + arguments, cwd=ROOT, capture_output=True,
                text=True, encoding="utf-8", timeout=args.timeout)
            output, code = completed.stdout + completed.stderr, completed.returncode
        except (subprocess.TimeoutExpired, OSError) as exc:
            output, code = str(exc), None
        (scratch / f"{label}.out").write_text(output, encoding="utf-8")
        return output, code, time.monotonic() - started

    save()
    if not receipt["exact_certificate_rendering"]:
        receipt.update(status="CERTIFICATE_RENDERING_MISMATCH")
        save()
        return 1
    output, code, elapsed = run("positive_ExactMatrixTables",
                                ["-o", str(artifact), source_relative])
    ok = (code == 0 and artifact.is_file() and
          not re.search(r"\berror(?:\([^)]*\))?:|declaration uses .sorry.", output))
    receipt["positive_control"] = {"status": "PASS" if ok else "FAIL", "returncode": code,
                                   "elapsed": elapsed, "control_sha256": sha256(source)}
    if not ok:
        receipt.update(status="POSITIVE_CONTROL_FAILED")
        save()
        return 1
    artifacts = {artifact_relative: sha256(artifact)}
    for name in MODULES:
        relative = f".lake/build/lib/lean/PermanssonResearch/X1/{name}.olean"
        artifacts[relative] = sha256(ROOT / relative)
    receipt["compiled_artifacts"] = artifacts
    save()

    negative = scratch / "corrupt_matrix_literal.lean"
    text = source.read_text(encoding="utf-8")
    assert "![3/4, 1/4" in text
    negative.write_text(text.replace("![3/4, 1/4", "![2/4, 1/4", 1),
                        encoding="utf-8", newline="\n")
    output, code, elapsed = run("corrupt_matrix_literal", [str(negative)])
    result = classify_mutation("corrupt_denominator", code, output) if code is not None else {
        "status": "INVALID_ENVIRONMENT", "returncode": None}
    result.update(elapsed=elapsed, mutation_sha256=sha256(negative))
    receipt["mutations"]["corrupt_matrix_literal"] = result
    ok &= result["status"] == "REJECTED"
    save()

    names = declaration_names(text)
    audit = scratch / "axiom_audit.lean"
    audit.write_text(f"import {MODULE}\n" + "".join(f"#print axioms {name}\n" for name in names),
                     encoding="utf-8")
    output, code, elapsed = run("axiom_audit", [str(audit)])
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    clean = re.findall(r"'([^']+)' does not depend on any axioms", output)
    missing = sorted(set(names) - ({name for name, _ in found} | set(clean)))
    forbidden = {name: sorted({a.strip() for a in used.replace("\n", " ").split(",")
                               if a.strip()} - ALLOWED) for name, used in found}
    forbidden = {name: used for name, used in forbidden.items() if used}
    audit_ok = code == 0 and not missing and not forbidden
    receipt["axiom_audit"] = {"status": "PASS" if audit_ok else "FAIL", "returncode": code,
        "declarations": len(names), "declaration_names": names, "missing": missing,
        "forbidden": forbidden, "elapsed": elapsed}
    changed = changed_files(hashes) + changed_files(artifacts)
    receipt.update(changed_files=changed,
        status="PASS" if ok and audit_ok and not changed else "FAIL")
    save()
    print(json.dumps(receipt, indent=2), flush=True)
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
