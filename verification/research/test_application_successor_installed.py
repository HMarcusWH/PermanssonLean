"""Installed-distribution qualification of the successor application.

Builds the sdist and an sdist-derived wheel from a *copy* of the package
source (the checkout is never written), installs the wheel into a fresh
virtual environment, and then exercises the installed package only:

* the import resolves to site-packages, never to the source tree;
* every packaged data file is byte-identical to its source;
* the console entry points run C10/C11 from exported packaged requests;
* the complete application test suite passes against the installed code.

The suite runs from a copy of the application tree with every package
``.py`` file removed, so its fixtures resolve while ``permansson_app``
can only be imported from the installed wheel. No skip or fallback: missing
build or schema dependencies must be installed and the actual tests must
pass. This qualifies the current source on this interpreter only; it is
not release acceptance for any other platform.
"""
from __future__ import annotations

from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
import venv
import zipfile

BASE = Path(__file__).resolve().parents[2]
APP = BASE / "apps/permansson/application-successor"
PACKAGE = APP / "src/permansson_app"
PINS = ["build==1.3.0", "jsonschema==4.26.0", "referencing==0.37.0", "rfc8785==0.1.4"]


def _run(cmd, *, cwd, env, timeout):
    process = subprocess.run([str(c) for c in cmd], cwd=cwd, env=env,
                             capture_output=True, text=True, timeout=timeout)
    return process.returncode, process.stdout + process.stderr


def _bin(env_dir: Path, name: str) -> Path:
    return env_dir / ("Scripts" if os.name == "nt" else "bin") / (name + (".exe" if os.name == "nt" else ""))


def _ignore_build_products(_dir, names):
    return [n for n in names if n in ("build", "dist", "__pycache__") or n.endswith(".egg-info")]


class InstalledDistributionTest(unittest.TestCase):
    def test_installed_wheel_runs_entry_points_and_full_suite(self):
        env = dict(os.environ)
        env["PERMANSSON_SOURCE_ROOT"] = str(BASE)
        env.pop("PYTHONPATH", None)
        with tempfile.TemporaryDirectory(prefix="permansson-installed-") as work:
            work = Path(work)
            source = work / "source"
            shutil.copytree(APP, source, ignore=_ignore_build_products)

            builder = work / "builder"
            venv.EnvBuilder(with_pip=True).create(builder)
            code, log = _run([_bin(builder, "python"), "-m", "pip", "install",
                              "--disable-pip-version-check", "--no-input", PINS[0]],
                             cwd=work, env=env, timeout=300)
            self.assertEqual(code, 0, log[-6000:])
            # Default `build` makes the sdist, then the wheel *from the sdist*.
            code, log = _run([_bin(builder, "python"), "-m", "build", "--outdir", work / "dist", source],
                             cwd=work, env=env, timeout=600)
            self.assertEqual(code, 0, log[-8000:])
            wheels = sorted((work / "dist").glob("*.whl"))
            sdists = sorted((work / "dist").glob("*.tar.gz"))
            self.assertEqual((len(wheels), len(sdists)), (1, 1), log[-4000:])

            names = zipfile.ZipFile(wheels[0]).namelist()
            self.assertFalse([n for n in names if "/tests/" in n or n.startswith("tests/")])
            self.assertFalse([n for n in names if n.endswith((".pyc", ".pyo"))])

            target = work / "installed"
            venv.EnvBuilder(with_pip=True).create(target)
            python = _bin(target, "python")
            code, log = _run([python, "-m", "pip", "install", "--disable-pip-version-check",
                              "--no-input", *PINS[1:], wheels[0]], cwd=work, env=env, timeout=300)
            self.assertEqual(code, 0, log[-6000:])

            # A tree with fixtures and docs but no package code: imports can
            # only resolve to the installed distribution.
            mirror = work / "mirror"
            shutil.copytree(APP, mirror, ignore=_ignore_build_products)
            for module in (mirror / "src/permansson_app").rglob("*.py"):
                module.unlink()

            probe = ("import sys,json;sys.path.insert(0,sys.argv[1]);"
                     "import permansson_app;print(json.dumps(permansson_app.__file__))")
            code, out = _run([python, "-B", "-c", probe, mirror / "src"], cwd=work, env=env, timeout=60)
            self.assertEqual(code, 0, out)
            located = Path(json.loads(out.strip().splitlines()[-1])).resolve()
            self.assertTrue(str(located).startswith(str(target.resolve())), located)
            installed_package = located.parent

            source_data = {p.relative_to(PACKAGE): p for p in (PACKAGE / "data").rglob("*") if p.is_file()}
            installed_data = {p.relative_to(installed_package): p
                              for p in (installed_package / "data").rglob("*") if p.is_file()}
            self.assertEqual(sorted(source_data), sorted(installed_data))
            for rel, path in source_data.items():
                self.assertEqual(sha256(path.read_bytes()).digest(),
                                 sha256(installed_data[rel].read_bytes()).digest(), str(rel))

            app_cli = _bin(target, "permansson-app")
            code, out = _run([app_cli, "resources", "--full", "--output", work / "resources"],
                             cwd=work, env=env, timeout=120)
            self.assertEqual(code, 0, out)
            for case, expected in (("c10", "c10.fixed_six_state.numeric.v1"),
                                   ("c11.multiclass", "c11.stationary_1_to_6.numeric.v1"),
                                   ("c11.periodic", "c11.stationary_1_to_6.numeric.v1")):
                with self.subTest(case=case):
                    request = work / "resources/examples" / f"{case}.request.json"
                    self.assertTrue(request.is_file(), request)
                    code, out = _run([app_cli, "run", request, "--source-root", BASE,
                                      "--output", work / f"run-{case}"], cwd=work, env=env, timeout=300)
                    self.assertEqual(code, 0, out[-6000:])
                    summary = json.loads(out)
                    self.assertIs(summary["ok"], True)
                    self.assertEqual(summary["numeric_status"], "EXACT_RATIONAL_VERIFIED")
                    result = json.loads(Path(summary["result_file"]).read_text(encoding="utf-8"))
                    self.assertEqual(result["capability"], expected)
                    self.assertEqual(result["lean_status"], "NOT_EXECUTED")
                    self.assertIs(result["scientific_claims_verified"], False)
            code, out = _run([_bin(target, "permansson-governance"), "--help"],
                             cwd=work, env=env, timeout=60)
            self.assertEqual(code, 0, out)

            code, out = _run([python, "-B", "-m", "unittest", "discover", "-s", mirror / "tests",
                              "-t", mirror / "tests", "-q"], cwd=work, env=env, timeout=900)
            self.assertEqual(code, 0, out[-12000:])
            self.assertIn("OK", out.strip().splitlines()[-1], out[-2000:])
            # The installed run must execute the whole suite, not a subset that
            # happened to import.
            ran = re.search(r"^Ran (\d+) tests? in ", out, re.M)
            self.assertIsNotNone(ran, out[-2000:])
            # Count the source-tree suite with the installed environment's
            # interpreter (it has every pinned dependency), and refuse any
            # module that failed to import instead of counting it as one test.
            counter = ("import json,sys,unittest;l=unittest.TestLoader();"
                       "s=l.discover(sys.argv[1],top_level_dir=sys.argv[1]);"
                       "print(json.dumps([s.countTestCases(),[str(e)[:400] for e in l.errors]]))")
            code, counted = _run([python, "-B", "-c", counter, APP / "tests"], cwd=work, env=env, timeout=120)
            self.assertEqual(code, 0, counted)
            expected, errors = json.loads(counted.strip().splitlines()[-1])
            self.assertEqual(errors, [])
            self.assertEqual(int(ran.group(1)), expected)


if __name__ == "__main__":
    unittest.main()
