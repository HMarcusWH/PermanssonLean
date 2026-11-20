"""Test discovery and CLI helpers work in shallow standalone extractions.

Load the four real affected test modules in a subprocess; do not rediscover this
regression recursively. Their selected existing tests exercise documentation,
source-pin rejection and CLI helpers without requiring a repository or Lean.
"""
from __future__ import annotations

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

APP = Path(__file__).resolve().parents[1]
MODULES = {
    "test_docs_registry": ("REPO", "DocsRegistryTests", "test_every_doc_is_indexed_and_relative_links_resolve"),
    "test_numeric": ("ROOT", "ResourcesTests", "test_missing_pins_rejected"),
    "test_extended_cli": ("ROOT", "ExtendedInstalledCLI", "test_both_successful_cli_scopes"),
    "test_integration": ("ROOT", "CLITests", "test_finite_kernel_end_to_end"),
}
SHALLOW_TEMP = Path("/tmp").resolve()
HAS_SHALLOW_TEMP = (len(SHALLOW_TEMP.parents) == 1 and SHALLOW_TEMP.is_dir()
                    and os.access(SHALLOW_TEMP, os.W_OK))
PROBE = """
import json, runpy, sys, unittest
from pathlib import Path
spec = json.loads(sys.argv[1])
app = Path(spec['app'])
suite = unittest.TestSuite()
for module, (root_name, case, method) in spec['modules'].items():
    namespace = runpy.run_path(str(app / 'tests' / (module + '.py')))
    expected = Path(spec['repo_root' if root_name == 'REPO' else 'source_root'])
    if namespace[root_name] != expected:
        raise AssertionError((module, str(namespace[root_name]), str(expected)))
    suite.addTest(namespace[case](method))
result = unittest.TextTestRunner(verbosity=2).run(suite)
sys.exit(0 if result.wasSuccessful() else 1)
"""


@unittest.skipUnless(HAS_SHALLOW_TEMP, "needs a writable one-level /tmp for shallow extraction")
class RootPortabilityTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        shallow_temp = tempfile.TemporaryDirectory(prefix="permansson-standalone-", dir=SHALLOW_TEMP)
        cls.addClassCleanup(shallow_temp.cleanup)
        cls.shallow = Path(shallow_temp.name).resolve()
        external_temp = tempfile.TemporaryDirectory(prefix="permansson-external-")
        cls.addClassCleanup(external_temp.cleanup)
        cls.external = Path(external_temp.name).resolve()
        cls.nested_root = cls.external / "checkout"
        cls.nested = cls.nested_root / "apps/permansson/application-successor"
        cls.nested.mkdir(parents=True)
        for target in (cls.shallow, cls.nested):
            shutil.copytree(APP / "src", target / "src", ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
            shutil.copytree(APP / "docs", target / "docs")
            shutil.copyfile(APP / "README.md", target / "README.md")
            (target / "tests").mkdir()
            for module in MODULES:
                shutil.copyfile(APP / "tests" / (module + ".py"), target / "tests" / (module + ".py"))

    def probe(self, app, repo_root, source_root, *, override=None, cwd=None):
        env = dict(os.environ)
        env.pop("PERMANSSON_SOURCE_ROOT", None)
        env.pop("PYTHONPATH", None)
        env["PYTHONDONTWRITEBYTECODE"] = "1"
        if override is not None:
            env["PERMANSSON_SOURCE_ROOT"] = str(override)
        spec = {"app": str(app), "repo_root": str(repo_root),
                "source_root": str(source_root), "modules": MODULES}
        result = subprocess.run([sys.executable, "-B", "-c", PROBE, json.dumps(spec)],
                                cwd=app if cwd is None else cwd, env=env,
                                text=True, capture_output=True, timeout=60)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_shallow_standalone_modules_and_cli(self):
        self.assertEqual(len(self.shallow.parents), 2)
        self.probe(self.shallow, self.shallow, self.shallow)

    def test_shallow_explicit_source_root_modules_and_cli(self):
        self.probe(self.shallow, self.shallow, self.external, override=self.external)

    def test_empty_source_root_still_resolves_to_working_directory(self):
        self.probe(self.shallow, self.shallow, self.external, override="", cwd=self.external)

    def test_repository_layout_keeps_original_default_root(self):
        self.probe(self.nested, self.nested_root, self.nested_root)


if __name__ == "__main__":
    unittest.main()
