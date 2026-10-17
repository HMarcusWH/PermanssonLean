"""Execute a fixed suite with fail-closed case mapping and result accounting."""
from __future__ import annotations

import argparse
import io
import json
import platform
from pathlib import Path
import sys
import unittest

from .reports import HardeningError, strict_json, write_report

SUITES = {
    "reference": "verification.integrity.tests.test_reference",
    "preservation": "verification.integrity.tests.test_preservation",
    "tex": "verification.integrity.tests.test_tex",
    "context": "verification.integrity.tests.test_context",
    "workflow": "verification.integrity.tests.test_workflow",
    "archive": "verification.archive.tests.test_archive",
}

REQUIREMENTS = {}
for prefix, count, suite in (("REF", 15, "reference"), ("PRES", 23, "preservation"),
                             ("TEX", 20, "tex"), ("ARCH", 27, "archive")):
    for number in range(1, count + 1):
        REQUIREMENTS[f"{prefix}-{number:02}"] = (suite, "integration" if prefix == "ARCH" and number in {14, 23} else "unit")
for number in range(1, 12):
    level = "unit" if number in {3, 6, 7, 9} else "review" if number == 10 else "live_pr"
    suite = "context" if number in {3, 9} else "workflow" if number in {6, 7} else None
    REQUIREMENTS[f"CI-{number:02}"] = (suite, level)
for number in range(1, 13):
    REQUIREMENTS[f"OPS-{number:02}"] = (None, "authorized_rollout")


def flatten(suite):
    for item in suite:
        if isinstance(item, unittest.TestSuite):
            yield from flatten(item)
        else:
            yield item


def validate_mapping(registry, suite, discovered):
    return _validate_mapping(registry, suite, discovered, REQUIREMENTS)


def _validate_mapping(registry, suite, discovered, contract):
    rows = registry.get("cases", [])
    if {row.get("id") for row in rows} != set(contract):
        raise HardeningError("E_REPORT", "Registry differs from the complete required case inventory")
    for row in rows:
        if (row.get("suite"), row.get("level")) != contract[row["id"]]:
            raise HardeningError("E_REPORT", "A requirement's suite or evidence level changed")
    if not discovered:
        raise HardeningError("E_REPORT", "Zero tests discovered")
    if any("_FailedTest" in name for name in discovered):
        raise HardeningError("E_REPORT", "Test loading failed")
    requirements = [item for item in rows if item.get("suite") == suite and item["level"] == "unit"]
    if not requirements:
        raise HardeningError("E_REPORT", "Required executable-case mappings are absent")
    ids = [item["id"] for item in registry["cases"]]
    if len(ids) != len(set(ids)):
        raise HardeningError("E_REPORT", "Duplicate requirement IDs")
    methods = {}
    for case in requirements:
        names = case.get("methods", [])
        if not names or len(names) != len(set(names)):
            raise HardeningError("E_REPORT", f"Missing or duplicate mapping for {case['id']}")
        if len(names) > 1 and not case.get("mapping_explanation"):
            raise HardeningError("E_REPORT", "Multiple mappings require an explanation")
        for name in names:
            if name not in discovered:
                raise HardeningError("E_REPORT", f"Mapped method was not discovered: {name}")
            methods.setdefault(name, []).append(case["id"])
    for name, cases in methods.items():
        if len(cases) > 1:
            relevant = [case for case in requirements if case["id"] in cases]
            if not all(case.get("mapping_explanation") for case in relevant):
                raise HardeningError("E_REPORT", "Shared case mapping needs an explanation")
    if set(discovered) - methods.keys():
        # Additional positive controls are permitted, but must be explicitly declared.
        controls = set(registry.get("controls", {}).get(suite, []))
        if set(discovered) - methods.keys() - controls:
            raise HardeningError("E_REPORT", "Discovered methods lack requirement/control mapping")
    return methods


class RecordedResult(unittest.TextTestResult):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.records = []
        self.subtest_count = 0

    def addSuccess(self, test):
        super().addSuccess(test)
        self.records.append({"method": test.id(), "status": "PASS"})

    def addFailure(self, test, err):
        super().addFailure(test, err)
        self.records.append({"method": test.id(), "status": "FAIL"})

    def addError(self, test, err):
        super().addError(test, err)
        self.records.append({"method": test.id(), "status": "ERROR"})

    def addSkip(self, test, reason):
        super().addSkip(test, reason)
        self.records.append({"method": test.id(), "status": "SKIP", "reason": reason})

    def addSubTest(self, test, subtest, err):
        super().addSubTest(test, subtest, err)
        self.subtest_count += 1
        self.records.append({"method": test.id(), "subtest": str(subtest), "status": "PASS" if err is None else "FAIL"})

    def addExpectedFailure(self, test, err):
        super().addExpectedFailure(test, err)
        self.records.append({"method": test.id(), "status": "EXPECTED_FAILURE"})


def validate_result(result, discovered, mapping):
    if (not result.wasSuccessful() or result.skipped or result.expectedFailures
            or result.testsRun != len(discovered) or not result.testsRun):
        raise HardeningError("E_REPORT", "Suite failed, skipped, or did not execute every discovered method")
    executed = {row["method"] for row in result.records if "subtest" not in row and row["status"] == "PASS"}
    if set(discovered) != executed:
        raise HardeningError("E_REPORT", "Successful result records do not cover discovered methods")
    return sorted({case for name in executed for case in mapping.get(name, [])})


def main(argv=None):
    parser = argparse.ArgumentParser()
    parser.add_argument("--suite", required=True, choices=tuple(SUITES))
    parser.add_argument("--report", required=True)
    args = parser.parse_args(argv)
    result = None
    mapping = {}
    payload = {"format": "Permansson.Hardening.Tests.v1", "schema_version": 1, "suite": args.suite}
    try:
        from .git_objects import GitRepo
        from .ci_context import capture_context
        from dataclasses import asdict
        repo = GitRepo(Path(__file__).resolve().parents[2])
        candidate = repo.run("rev-parse", "HEAD").strip().decode("ascii")
        payload["context"] = asdict(capture_context(repo, candidate))
        payload["runtime"] = {"python": platform.python_version(), "git": repo.run("--version").strip().decode()}
        try:
            repo.run("diff", "--quiet", "HEAD", "--")
            tracked_clean = True
        except HardeningError:
            tracked_clean = False
        payload["execution_tracked_clean"] = tracked_clean
        if not tracked_clean and payload["context"]["event"] != "local":
            raise HardeningError("E_CONTEXT", "Tests cannot execute dirty tracked sources in CI")
        registry = strict_json(Path(__file__).with_name("test_coverage.json").read_bytes(), "E_REPORT")
        loader = unittest.TestLoader()
        suite = loader.loadTestsFromName(SUITES[args.suite])
        discovered = [case.id() for case in flatten(suite)]
        if loader.errors:
            raise HardeningError("E_REPORT", "Test loader errors: " + str(loader.errors)[:2000])
        mapping = validate_mapping(registry, args.suite, discovered)
        result = unittest.TextTestRunner(verbosity=2, resultclass=RecordedResult).run(suite)
        covered = validate_result(result, discovered, mapping)
        payload.update(status="PASS", error_code=None, covered_requirements=covered)
        code = 0
    except (HardeningError, OSError, KeyError, TypeError) as exc:
        payload.update(status="FAIL", error_code=getattr(exc, "code", "E_REPORT"), message=str(exc)[:4000])
        code = getattr(exc, "exit_code", 1)
    if result:
        for row in result.records:
            row["requirements"] = mapping.get(row["method"], [])
        payload.update(methods_run=result.testsRun, subtests_run=result.subtest_count,
                       failures=len(result.failures), errors=len(result.errors), skips=len(result.skipped),
                       results=result.records)
    write_report(args.report, payload)
    print(f"{args.suite}: {payload['status']}")
    return code


if __name__ == "__main__":
    raise SystemExit(main())
