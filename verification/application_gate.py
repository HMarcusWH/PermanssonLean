#!/usr/bin/env python3
"""Repository synchronization for the non-theorem application-contract layer."""
from __future__ import annotations
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from application.validator.validate_application import load_json, validate_document, validator

REQUIRED = (
    "application/README.md", "application/APPLICATION_STANDARD.md",
    "application/VERSION.json", "application/requirements.txt",
    "application/validator/validate_application.py", "application/validator/README.md",
    "application/tests/test_application.py", "application/tests/test_codex_regressions.py",
    "application/examples/build_examples.py",
    "application/examples/expectations.json", "application/examples/README.md",
    "docs/APPLICATION_BOUNDARY.md", "docs/FUTURE_THEORY_ROADMAP.md",
    ".github/workflows/application.yml", ".gitattributes",
)
SCHEMAS = {"application_bundle", "application_certificate", "semantic_pipeline",
           "intervention_protocol", "identified_set", "provenance_graph", "common"}


def main() -> int:
    failures = []
    for relative in REQUIRED:
        if not (ROOT / relative).is_file():
            failures.append(f"Missing {relative}")
    if failures:
        print("\n".join(failures))
        return 1
    version = load_json(ROOT / "application/VERSION.json")
    for key, value in {
        "standard": "Permansson Application Standard", "version": "0.1.0",
        "compatible_theory": "0.1.8", "status": "DRAFT",
        "scope": "APPLICATION_CONTRACT_NOT_THEOREM_EXTENSION",
        "schema_dialect": "https://json-schema.org/draft/2020-12/schema",
        "digest_profile": "PERMANSSON_PIPELINE_V1",
    }.items():
        if version.get(key) != value:
            failures.append(f"Version boundary mismatch: {key}")
    schema_names = {p.name.removesuffix(".schema.json") for p in (ROOT / "application/schemas").glob("*.schema.json")}
    if schema_names != SCHEMAS:
        failures.append("Schema inventory mismatch")
    validator()  # Validate schemas and load only the local registry.
    expectations = load_json(ROOT / "application/examples/expectations.json")
    paths = {p.parent.name: p for p in (ROOT / "application/examples").glob("*/application.json")}
    if not paths or paths.keys() != expectations.keys():
        failures.append("Every example must have an explicit expected error-code set")
    for name, path in sorted(paths.items()):
        result = validate_document(load_json(path), path.parent)
        codes = sorted({e["code"] for e in result["errors"]})
        if codes != expectations.get(name):
            failures.append(f"{name}: expected {expectations.get(name)}, got {codes}")
        if result["scientific_claims_verified"] is not False:
            failures.append(f"{name}: contract validator improperly promotes scientific truth")
    attribute_rules = [line.split() for line in (ROOT / ".gitattributes").read_text(encoding="utf-8").splitlines()
                       if line.strip() and not line.lstrip().startswith("#")]
    if ["application/**", "-text"] not in attribute_rules:
        failures.append("Application evidence raw-byte preservation rule missing")
    for filename in ("README.md", "verification/README.md"):
        path = ROOT / filename
        if not path.is_file() or "application/" not in path.read_text(encoding="utf-8"):
            failures.append(f"Application documentation link missing: {filename}")
    print(json.dumps({"application_contract_gate": "FAIL" if failures else "PASS",
                      "examples": len(paths), "schemas": len(schema_names),
                      "failures": failures, "scope": "APPLICATION_CONTRACT_ONLY"}, indent=2))
    return 1 if failures else 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError) as exc:
        print(f"Application gate configuration error: {exc}", file=sys.stderr)
        sys.exit(1)
