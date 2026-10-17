"""Twenty independent F2 acceptance cases using real accepted input bytes.

Candidates live in a real disposable Git repository; none of these tests calls
F1. Fixture-policy seams are private Python calls, never production CLI options.
"""
from __future__ import annotations

from dataclasses import replace
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
from unittest import mock

from verification.integrity.git_objects import GitRepo
from verification.integrity.reports import HardeningError
from verification.integrity import tex_export as tex


class TexExportTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.production_repo = GitRepo(Path(__file__).resolve().parents[3])
        cls.production_reference = tex._production_reference()
        cls.inputs = tex._read_inputs(cls.production_repo, cls.production_reference)
        cls.accepted_tex = tex.render_accepted_tex(cls.production_repo)
        cls.directory = tempfile.TemporaryDirectory(prefix="ptex-git-")
        cls.root = Path(cls.directory.name)
        cls.git = shutil.which("git")
        cls.env = {key: value for key, value in os.environ.items() if not key.startswith("GIT_")}
        cls.env.update({"GIT_CONFIG_NOSYSTEM": "1", "GIT_CONFIG_GLOBAL": os.devnull,
                        "GIT_AUTHOR_NAME": "F2 fixture", "GIT_AUTHOR_EMAIL": "fixture@example.invalid",
                        "GIT_COMMITTER_NAME": "F2 fixture", "GIT_COMMITTER_EMAIL": "fixture@example.invalid",
                        "GIT_AUTHOR_DATE": "2026-10-17T00:00:00Z", "GIT_COMMITTER_DATE": "2026-10-17T00:00:00Z"})
        cls.raw_git("init", "--bare", str(cls.root))
        cls.files = {tex.INPUT_PATHS[key]: ("100644", payload) for key, payload in cls.inputs.items()}
        cls.files[tex.TEX_PATH] = ("100644", cls.accepted_tex)
        cls.authority = cls.commit_files(cls.files)
        cls.repo = GitRepo(cls.root)
        cls.reference = replace(cls.production_reference, accepted=cls.authority,
                                tree=cls.repo.commit(cls.authority).tree)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    @classmethod
    def raw_git(cls, *args, input=None):
        command = [cls.git, "--no-replace-objects", "-c", "core.autocrlf=false", "-c", "core.hooksPath=",
                   "-C", str(cls.root), *args]
        process = subprocess.run(command, input=input, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 env=cls.env, timeout=30)
        if process.returncode:
            raise RuntimeError(process.stderr.decode("utf-8", "replace"))
        return process.stdout

    @classmethod
    def commit_files(cls, files, parent=None):
        nested = {}
        for path, (mode, payload) in files.items():
            node = nested
            components = path.split(b"/")
            for component in components[:-1]:
                node = node.setdefault(component, {})
            oid = cls.raw_git("hash-object", "-w", "--stdin", input=payload).strip()
            node[components[-1]] = (mode.encode(), oid)

        def tree(node):
            records = []
            for name in sorted(node):
                value = node[name]
                if isinstance(value, dict):
                    mode, kind, oid = b"040000", b"tree", tree(value)
                else:
                    mode, oid = value
                    kind = b"blob"
                records.append(mode + b" " + kind + b" " + oid + b"\t" + name + b"\0")
            return cls.raw_git("mktree", "-z", input=b"".join(records)).strip()

        args = ["commit-tree", tree(nested).decode()]
        if parent:
            args += ["-p", parent]
        return cls.raw_git(*args, input=b"F2 isolated fixture\n").strip().decode()

    def compare_candidate(self, payload=None, *, changes=None, mode="100644"):
        files = dict(self.files)
        files[tex.TEX_PATH] = (mode, self.accepted_tex if payload is None else payload)
        files.update(changes or {})
        candidate = self.commit_files(files, self.authority)
        return tex._compare_tex(self.repo, candidate, self.reference)

    def expect_error(self, code, callback):
        with self.assertRaises(HardeningError) as caught:
            callback()
        self.assertEqual(caught.exception.code, code)
        self.assertEqual(caught.exception.exit_code, 1)
        return caught.exception

    def equation_lines(self):
        lines = self.accepted_tex.splitlines(keepends=True)
        indices = [index for index, line in enumerate(lines) if line.startswith(b"\\companionEquation{")]
        self.assertEqual(len(indices), 10)
        return lines, indices

    def equation_replacement(self):
        lines, indices = self.equation_lines()
        lines[indices[0]] = b"\\companionEquation{0=1}\n"
        return b"".join(lines)

    def test_tex_01_accepted_complete_export(self):
        """TEX-01: production two-module renderer, exact size/digest, ten equations."""
        self.assertEqual(len(self.accepted_tex), 71379)
        self.assertEqual(hashlib.sha256(self.accepted_tex).hexdigest(), self.production_reference.tex_hash)
        self.assertEqual(self.compare_candidate()["equation_records"], 10)
        self.assertEqual(tex.compare_tex(self.production_repo, self.production_reference.accepted)["actual_size"], 71379)

    def test_tex_02_wrong_render_revision(self):
        """TEX-02: A in place of G must fail the reference-output pin."""
        self.assertEqual(tex._render_trusted_inputs(self.inputs, self.production_reference), self.accepted_tex)
        reference = replace(self.production_reference, revision=self.production_reference.accepted)
        self.expect_error("E_EXPORT_REFERENCE", lambda: tex._render_trusted_inputs(self.inputs, reference))

    def test_tex_03_equation_zero_equals_one(self):
        """TEX-03: equation-only corruption is rejected by F2 directly."""
        self.assertEqual(self.compare_candidate()["actual_size"], 71379)
        error = self.expect_error("E_TEX_MISMATCH", lambda: self.compare_candidate(self.equation_replacement()))
        self.assertGreater(error.details["first_differing_byte"], 0)

    def test_tex_04_equation_sign(self):
        """TEX-04: change one equation sign, leaving every caption untouched."""
        lines, indices = self.equation_lines()
        index = next(index for index in indices if b"-" in lines[index])
        lines[index] = lines[index].replace(b"-", b"+", 1)
        self.expect_error("E_TEX_MISMATCH", lambda: self.compare_candidate(b"".join(lines)))

    def test_tex_05_equation_fraction(self):
        """TEX-05: alter a denominator without changing narrative."""
        altered = self.accepted_tex.replace(b"\\frac{121}{211}", b"\\frac{121}{212}", 1)
        self.assertNotEqual(altered, self.accepted_tex)
        self.expect_error("E_TEX_MISMATCH", lambda: self.compare_candidate(altered))

    def test_tex_06_equation_removed(self):
        """TEX-06: remove an equation block."""
        lines, indices = self.equation_lines()
        del lines[indices[0]:indices[0] + 2]
        self.expect_error("E_TEX_MISMATCH", lambda: self.compare_candidate(b"".join(lines)))

    def test_tex_07_equation_duplicated(self):
        """TEX-07: duplicate an equation and its caption."""
        lines, indices = self.equation_lines()
        index = indices[0]
        lines[index:index] = lines[index:index + 2]
        self.expect_error("E_TEX_MISMATCH", lambda: self.compare_candidate(b"".join(lines)))

    def test_tex_08_equation_order(self):
        """TEX-08: swap complete equation/caption blocks."""
        lines, indices = self.equation_lines()
        first, second = indices[:2]
        lines[first:first + 2], lines[second:second + 2] = lines[second:second + 2], lines[first:first + 2]
        self.expect_error("E_TEX_MISMATCH", lambda: self.compare_candidate(b"".join(lines)))

    def test_tex_09_caption_and_metadata(self):
        """TEX-09: caption-only and source-header-only changes both fail."""
        lines, indices = self.equation_lines()
        lines[indices[0] + 1] = lines[indices[0] + 1].replace(b"{\\small ", b"{\\small Altered caption: ", 1)
        for name, candidate in (("caption", b"".join(lines)), ("metadata", self.accepted_tex.replace(b"% Source-SHA:", b"% Altered-SHA:", 1))):
            with self.subTest(change=name):
                self.expect_error("E_TEX_MISMATCH", lambda: self.compare_candidate(candidate))

    def test_tex_10_trailing_newline(self):
        """TEX-10: exact equality includes the final newline."""
        self.assertTrue(self.accepted_tex.endswith(b"\n"))
        for candidate in (self.accepted_tex[:-1], self.accepted_tex + b"\n"):
            with self.subTest(size=len(candidate)):
                self.expect_error("E_TEX_MISMATCH", lambda: self.compare_candidate(candidate))

    def test_tex_11_repaired_receipts(self):
        """TEX-11: repair actual candidate hash fields; F2 still runs alone."""
        altered = self.equation_replacement()
        new_hash = hashlib.sha256(altered).hexdigest()
        old_hash = hashlib.sha256(self.accepted_tex).hexdigest()
        paths = (b"release/v0.2.0/compile-evidence.json", b"release/v0.2.0/review-evidence.json")
        production_entries = self.production_repo.tree(self.production_reference.accepted)
        changes = {}
        for path in paths:
            original = self.production_repo.blob(production_entries[path].oid)
            repaired = original.replace(old_hash.encode(), new_hash.encode())
            changes[path] = ("100644", repaired)
        manifest_path = b"release/v0.2.0/manifest.json"
        manifest = json.loads(self.production_repo.blob(production_entries[manifest_path].oid))
        for path, (_, payload) in {**changes, tex.TEX_PATH: ("100644", altered)}.items():
            relative = path.removeprefix(b"release/v0.2.0/").decode()
            manifest["artifact_files"][relative] = hashlib.sha256(payload).hexdigest()
        changes[manifest_path] = ("100644", (json.dumps(manifest, indent=2) + "\n").encode())
        # The original review binds the unchanged manuscript/code; compile inputs
        # and the inventory now consistently bind the false candidate TeX.
        compile_record = json.loads(changes[paths[0]][1])
        self.assertEqual(compile_record["tex_sha256"], new_hash)
        self.assertEqual(compile_record["desktop_tex_compiler"]["input_sha256"], new_hash)
        with mock.patch("verification.integrity.tex_export._read_inputs", wraps=tex._read_inputs) as read_reference:
            self.expect_error("E_TEX_MISMATCH", lambda: self.compare_candidate(altered, changes=changes))
            self.assertEqual(read_reference.call_count, 1)

    def test_tex_12_candidate_builder_shadow(self):
        """TEX-12: candidate builder bytes are never executed."""
        marker = self.root / "builder-marker"
        shadow = f"from pathlib import Path\nPath({str(marker)!r}).write_text('executed')\nraise RuntimeError('candidate builder imported')\n".encode()
        self.compare_candidate(changes={tex.INPUT_PATHS["builder"]: ("100644", shadow)})
        self.assertFalse(marker.exists())

    def test_tex_13_candidate_verifier_shadow(self):
        """TEX-13: candidate helper bytes are never executed."""
        marker = self.root / "verifier-marker"
        shadow = f"from pathlib import Path\nPath({str(marker)!r}).write_text('executed')\nraise RuntimeError('candidate helper imported')\n".encode()
        self.compare_candidate(changes={tex.INPUT_PATHS["verifier"]: ("100644", shadow)})
        self.assertFalse(marker.exists())

    def test_tex_14_pythonpath_startup_injection(self):
        """TEX-14: cwd, PYTHONPATH and parent sys.modules cannot supply helpers."""
        with tempfile.TemporaryDirectory(prefix="ptex-shadow-") as directory:
            cwd = Path(directory)
            marker = cwd / "executed"
            shadow = f"from pathlib import Path\nPath({str(marker)!r}).write_text('executed')\nraise RuntimeError('startup imported')\n"
            for filename in ("build_release.py", "verify_release.py", "sitecustomize.py", "usercustomize.py"):
                (cwd / filename).write_text(shadow, encoding="utf-8")
            environment = {**os.environ, "PYTHONPATH": directory, "PYTHONSTARTUP": str(cwd / "sitecustomize.py")}
            with mock.patch.dict("sys.modules", {"build_release": object(), "verify_release": object()}):
                actual = tex._render_trusted_inputs(self.inputs, self.production_reference, cwd=cwd, environment=environment)
            self.assertEqual(actual, self.accepted_tex)
            self.assertFalse(marker.exists())

    def test_tex_15_missing_accepted_helper(self):
        """TEX-15: missing dependency is a reference error, never a TeX rejection."""
        inputs = dict(self.inputs)
        del inputs["verifier"]
        self.expect_error("E_REFERENCE_MISSING", lambda: tex._render_trusted_inputs(inputs, self.production_reference))

    def test_tex_16_wrong_helper_hash(self):
        """TEX-16: changed trusted dependency fails before import."""
        inputs = dict(self.inputs)
        inputs["verifier"] += b"\n# altered reference helper\n"
        self.expect_error("E_EXPORT_REFERENCE", lambda: tex._render_trusted_inputs(inputs, self.production_reference))

    def test_tex_17_render_timeout(self):
        """TEX-17: a controlled test worker reaches the explicit timeout."""
        with tempfile.TemporaryDirectory(prefix="ptex-timeout-") as directory:
            worker = Path(directory) / "hang.py"
            marker = Path(directory) / "worker-entered"
            worker.write_text(f"import time\nfrom pathlib import Path\nPath({str(marker)!r}).write_text('entered')\ntime.sleep(60)\n", encoding="utf-8")
            self.expect_error("E_COMMAND_TIMEOUT", lambda: tex._render_trusted_inputs(self.inputs, self.production_reference, worker=worker, timeout=1.0))
            self.assertTrue(marker.exists(), "Timeout must follow execution of the controlled hanging worker")

    def test_tex_18_pdf_and_build_never_called(self):
        """TEX-18: fixture entry points throw; accepted TeX function still succeeds."""
        inputs = dict(self.inputs)
        inputs["builder"] += b"\ndef pdf_document(*args, **kwargs):\n    raise RuntimeError('PDF path forbidden')\ndef build(*args, **kwargs):\n    raise RuntimeError('Build path forbidden')\n"
        reference = replace(self.production_reference,
                            input_hashes=tuple((key, hashlib.sha256(value).hexdigest()) for key, value in inputs.items()))
        self.assertEqual(tex._render_trusted_inputs(inputs, reference), self.accepted_tex)

    def test_tex_19_output_budget(self):
        """TEX-19: streaming output cap rejects a controlled oversized renderer."""
        inputs = dict(self.inputs)
        inputs["builder"] += f"\ndef tex_document(*args, **kwargs):\n    return 'x' * {tex.MAX_OUTPUT + 65536}\n".encode()
        reference = replace(self.production_reference,
                            input_hashes=tuple((key, hashlib.sha256(value).hexdigest()) for key, value in inputs.items()))
        self.expect_error("E_LIMIT", lambda: tex._render_trusted_inputs(inputs, reference))

    def test_tex_20_candidate_symlink(self):
        """TEX-20: inspect Git mode; never follow a candidate symlink."""
        self.assertEqual(self.compare_candidate()["actual_size"], 71379)
        self.expect_error("E_TEX_TYPE", lambda: self.compare_candidate(b"../../manuscript.json", mode="120000"))


if __name__ == "__main__":
    unittest.main()
