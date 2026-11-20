#!/usr/bin/env python3
"""Compare new exact reproductions with the immutable v2.0.1 review records.

This runner verifies the archive before reading its JSON. Calculation modules
receive no archived answers. A matching result reproduces an output, not the
identity of the unavailable original program or its unrecorded fixture inputs.
"""
from __future__ import annotations

import argparse
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import sys
import zipfile

import quantitative_replay
import specialized_replay


HERE = Path(__file__).resolve().parent
ARCHIVE_NAME = "Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip"
ARCHIVE_BYTES = 7406118
ARCHIVE_SHA256 = "d66d9ac3a8e8dac1a15ecc5e7703569f5cbe3c29121a97d9cfe6d148546e8a18"
ARCHIVE_ROOT = "Permansson_Regimes_v2_0_1/"
RECORDS = {
    "quantitative": {
        "member": ARCHIVE_ROOT + "review/quantitative_exact_checks.json",
        "count": 43,
        "sha256": "13f383a2e1ae0ac0caf7ae5eca952270737f4e3a02e7c7b155f995abd67a100f",
    },
    "specialized": {
        "member": ARCHIVE_ROOT + "review/specialized_exact_checks.json",
        "count": 20,
        "sha256": "3c8bea7dd40ad1f74eaae15463aea3d6ea93971a6a06b16b0d9338fc4d15ea67",
    },
}


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def named_rows(rows: list[dict], count: int, kind: str) -> list[str]:
    require(isinstance(rows, list) and len(rows) == count,
            f"{kind}: expected exactly {count} records")
    names = []
    for row in rows:
        require(isinstance(row, dict), f"{kind}: record must be an object")
        name = row.get("name")
        require(isinstance(name, str) and bool(name), f"{kind}: missing record name")
        require(isinstance(row.get("actual"), str), f"{kind}/{name}: actual must be a string")
        if kind == "archived":
            require(isinstance(row.get("expected"), str), f"archived/{name}: expected must be a string")
            require(isinstance(row.get("passed"), bool), f"archived/{name}: passed must be a boolean")
        else:
            require(all(isinstance(row.get(key), str) and row[key] for key in ("source", "calculation")),
                    f"computed/{name}: missing source or calculation")
        names.append(name)
    require(len(set(names)) == count, f"{kind}: duplicate names")
    return names


def compare(computed: list[dict], archived: list[dict], count: int) -> list[dict]:
    """Fail closed on count, names, ordering, fields and actual value differences."""
    require(named_rows(computed, count, "computed") == named_rows(archived, count, "archived"),
            "Computed and archived names/order differ")
    return [
        {
            **new,
            "archived_actual": old["actual"],
            "archived_expected": old["expected"],
            "archived_passed": old["passed"],
            "passed": new["actual"] == old["actual"] == old["expected"],
        }
        for new, old in zip(computed, archived)
    ]


def comparison_controls() -> list[dict]:
    """New runner controls, counted separately from retained arithmetic results."""
    fresh = [{"name": "probe", "actual": "1/2", "source": "runner control", "calculation": "1/2"}]
    saved = [{"name": "probe", "actual": "1/2", "expected": "1/2", "passed": True}]
    require(compare(fresh, saved, 1)[0]["passed"], "Comparison positive control failed")
    controls = [
        {"name": "changed_archived_expected_is_detected",
         "passed": not compare(fresh, [{**saved[0], "expected": "2/3"}], 1)[0]["passed"]},
        {"name": "changed_computed_value_is_detected",
         "passed": not compare([{**fresh[0], "actual": "2/3"}], saved, 1)[0]["passed"]},
    ]
    probes = [
        ("duplicate_names_are_rejected", fresh * 2, saved * 2, 2),
        ("missing_record_is_rejected", fresh, [], 1),
        ("extra_record_is_rejected", fresh, saved + [{**saved[0], "name": "extra"}], 1),
    ]
    for name, computed, archived, count in probes:
        try:
            compare(computed, archived, count)
        except ValueError:
            rejected = True
        else:
            rejected = False
        controls.append({"name": name, "passed": rejected})
    return controls


def load_records(archive: Path) -> dict[str, list[dict]]:
    data = archive.read_bytes()
    require(len(data) == ARCHIVE_BYTES, "Reviewed archive byte count differs")
    require(sha256(data).hexdigest() == ARCHIVE_SHA256, "Reviewed archive SHA-256 differs")
    records = {}
    with zipfile.ZipFile(BytesIO(data)) as bundle:
        for group, identity in RECORDS.items():
            require(bundle.namelist().count(identity["member"]) == 1,
                    f"Archive member is missing or duplicated: {identity['member']}")
            raw = bundle.read(identity["member"])
            require(sha256(raw).hexdigest() == identity["sha256"], f"{group}: result-member SHA-256 differs")
            record = json.loads(raw)
            require(isinstance(record, dict) and record.get("count") == identity["count"],
                    f"{group}: retained count differs")
            records[group] = record["checks"]
    return records


def run(archive: Path) -> dict:
    saved = load_records(archive)
    groups = {}
    for name, module in (("quantitative", quantitative_replay), ("specialized", specialized_replay)):
        checks = compare(module.compute_checks(), saved[name], RECORDS[name]["count"])
        controls = module.negative_controls()
        require(len(controls) == 6 and len({row["name"] for row in controls}) == 6,
                f"{name}: expected six unique additional controls")
        require(all(isinstance(row.get("passed"), bool) for row in controls),
                f"{name}: control result must be boolean")
        groups[name] = {
            "checks": checks,
            "retained_results": len(checks),
            "results_matched": sum(row["passed"] for row in checks),
            "arithmetic_controls": controls,
            "arithmetic_controls_passed": sum(row["passed"] for row in controls),
        }
    controls = comparison_controls()
    passed = all(row["passed"] for group in groups.values()
                 for row in group["checks"] + group["arithmetic_controls"])
    passed = passed and all(row["passed"] for row in controls)
    return {
        "format": "Permansson.Paper2.NewReproduction.v1",
        "status": "PASS" if passed else "FAIL",
        "evidence_kind": "NEW_REPRODUCTION_NOT_ORIGINAL_REVIEW_PROGRAM",
        "source_archive": {"name": ARCHIVE_NAME, "bytes": ARCHIVE_BYTES, "sha256": ARCHIVE_SHA256},
        "source_records": RECORDS,
        "program_sha256": {name: sha256((HERE / name).read_bytes()).hexdigest()
                           for name in ("replay.py", "quantitative_replay.py", "specialized_replay.py")},
        "arithmetic": "Python standard-library fractions.Fraction; exact finite rational operations",
        "provenance": {
            "original_programs_recovered": False,
            "quantitative": quantitative_replay.__doc__.strip(),
            "specialized": specialized_replay.PROVENANCE,
            "comparison": "Computed strings must match both archived actual and expected strings. Archived passed flags are reported but do not determine the new result.",
        },
        "groups": groups,
        "comparison_controls": controls,
        "totals": {
            "retained_results": sum(group["retained_results"] for group in groups.values()),
            "results_matched": sum(group["results_matched"] for group in groups.values()),
            "additional_arithmetic_controls": sum(len(group["arithmetic_controls"]) for group in groups.values()),
            "arithmetic_controls_passed": sum(group["arithmetic_controls_passed"] for group in groups.values()),
            "additional_comparison_controls": len(controls),
            "comparison_controls_passed": sum(row["passed"] for row in controls),
        },
        "limits": [
            "These new programs reproduce 63 retained outputs; they do not authenticate the missing original execution.",
            "Unrecorded endpoint, shell and Gram inputs use declared new fixtures; matching outputs do not identify historical inputs.",
            "No general theorem proof, Lean compilation, empirical identification, independent acceptance or release approval is asserted.",
            "The reviewed PDF, source ZIP, result records and original publication manifest remain separate immutable artifacts.",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archive", type=Path, default=HERE.parents[1] / "v2.0.1" / ARCHIVE_NAME,
                        help="Exact reviewed ZIP; defaults to the sibling publication package")
    parser.add_argument("--full", action="store_true", help="Print the complete JSON result")
    parser.add_argument("--output", type=Path, help="Write complete JSON to a new file; existing files are refused")
    args = parser.parse_args()
    try:
        result = run(args.archive)
        rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
        if args.output:
            with args.output.open("x", encoding="utf-8", newline="\n") as destination:
                destination.write(rendered)
        print(rendered if args.full else json.dumps({"status": result["status"], **result["totals"]}, indent=2), end="" if args.full else "\n")
        return 0 if result["status"] == "PASS" else 1
    except (OSError, ValueError, KeyError, ArithmeticError, zipfile.BadZipFile) as error:
        print(f"Reproduction refused: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
