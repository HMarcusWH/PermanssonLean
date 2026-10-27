"""Regression diagnostics cannot make a failing unittest suite green."""
import io
import unittest
import pr113_regression_diagnostics as diag


class DiagnosticTests(unittest.TestCase):
    def test_failures_distinct_from_subtest_failures(self):
        class Fixture(unittest.TestCase):
            def test_ok(self):
                self.assertTrue(True)
            def test_bad(self):
                self.assertEqual(1, 2)
            def test_sub(self):
                for x in (0, 1):
                    with self.subTest(x=x):
                        self.assertEqual(0, x)
        result = unittest.TextTestRunner(
            stream=io.StringIO(), resultclass=diag.Result).run(
                unittest.defaultTestLoader.loadTestsFromTestCase(Fixture))
        report = diag.summary(result)
        self.assertEqual(report["tests_run"], 3)
        self.assertEqual(report["failure_count"], 1)
        self.assertEqual(len(report["subtest_failures"]), 1)
        self.assertEqual(report["status"], "TESTS_FAILED")
        self.assertFalse(report["mathematical_acceptance"])
