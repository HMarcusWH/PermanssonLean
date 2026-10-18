"""The supplied independent Fraction checks, integrated without changing them.

These checks corroborate finite arithmetic. They are not Lean verification.
"""
import importlib.util
from pathlib import Path
import sys
import unittest

_package = Path(__file__).resolve().parents[2] / 'research/paper_closures/spec'
_path = _package / 'verification/exact_checks.py'
_spec = importlib.util.spec_from_file_location('permansson_paper_exact_checks', _path)
_module = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = _module
_spec.loader.exec_module(_module)

# unittest discovers the original 27 methods as distinct regression tests.
ExactChecks = _module.ExactChecks


if __name__ == '__main__':
    unittest.main()
