"""Bounded actual Research failure diagnostics; preserve failing exit status."""
import argparse
import json
import os
from pathlib import Path
import sys
import unittest

FORMAT = "Permansson.PR113.ResearchRegressionDiagnostics.v1"


class Result(unittest.TextTestResult):
    def __init__(self, *args):
        super().__init__(*args)
        self.subtests = []

    def addSubTest(self, test, subtest, err):
        super().addSubTest(test, subtest, err)
        if err is not None:
            self.subtests.append({
                "id": subtest.id(), "parent_id": test.id(),
                "status": "failure" if issubclass(err[0], test.failureException) else "error",
                "traceback": self._exc_info_to_string(err, test)[-12000:],
            })


def summary(result):
    return {
        "format": FORMAT,
        "status": "TESTS_PASSED" if result.wasSuccessful() else "TESTS_FAILED",
        "tests_run": result.testsRun,
        "failure_count": len(result.failures),
        "error_count": len(result.errors),
        "skips": len(result.skipped),
        "subtest_failures": result.subtests,
        "failures": [{"id": test.id(), "traceback": detail[-12000:]}
                     for test, detail in result.failures],
        "errors": [{"id": test.id(), "traceback": detail[-12000:]}
                   for test, detail in result.errors],
        "github_sha": os.environ.get("GITHUB_SHA"),
        "github_run_id": os.environ.get("GITHUB_RUN_ID"),
        "historical_source_approved": False,
        "mathematical_acceptance": False,
    }


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True, type=Path)
    args = ap.parse_args(argv)
    from pr113_boundary_io import detached_destination
    out = detached_destination(args.out, Path(__file__).resolve().parents[2])
    try:
        suite = unittest.defaultTestLoader.discover(
            "verification/research", pattern="test_*.py")
        result = unittest.TextTestRunner(
            verbosity=2, resultclass=Result).run(suite)
        report = summary(result)
        out.parent.mkdir(parents=True, exist_ok=True)
        with out.open("x", encoding="utf-8") as handle:
            json.dump(report, handle, sort_keys=True, indent=2)
            handle.write("\n")
        print("PR113_RESEARCH_REGRESSION_DIAGNOSTICS",
              json.dumps({k: report[k] for k in (
                  "status", "tests_run", "failure_count", "error_count", "skips")}))
        return 0 if result.wasSuccessful() else 1
    except Exception as exc:
        print("RESEARCH_DIAGNOSTICS_FAILED_CLOSED", exc, file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
