"""NEXT-05: actual compiler census of arbitrary-measurable Fin 2 interfaces."""
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
MODULE = "PermanssonResearch.MultiAgent.MeasurableProductTwo"
NAMESPACE = "PermanssonResearch.MultiAgent.MeasurableProduct.Two"
REQUIRED = ("measurable_state", "measurable_inverseState",
            "measurable_inverseWorld", "measurable_inverseInput",
            "inverse_world_at_original", "inverse_input_at_original",
            "action_map_two")


class MeasurableProductTwoCompiler(unittest.TestCase):
    def test_declared_original_action_and_input_contract(self):
        # Positive nonmock compiler is mandatory; unavailable compiler fails.
        source = f"import {MODULE}\n" + "\n".join(
            f"#check {NAMESPACE}.{name}\n#print axioms {NAMESPACE}.{name}"
            for name in REQUIRED) + "\n"
        with tempfile.TemporaryDirectory(prefix="measurable-product-two-") as tmp:
            path = Path(tmp) / "CheckProductTwo.lean"
            path.write_text(source, encoding="utf-8")
            try:
                p = subprocess.run(["lake", "env", "lean", str(path)],
                                   cwd=ROOT, capture_output=True, text=True,
                                   timeout=240, check=False)
            except (OSError, subprocess.TimeoutExpired) as exc:
                self.fail("real pinned Lean compiler unavailable: " + str(exc))
        output = p.stdout + p.stderr
        self.assertEqual(p.returncode, 0, output[-7000:])
        self.assertNotIn("sorryAx", output)
        for name in REQUIRED:
            full = f"{NAMESPACE}.{name}"
            self.assertIn(full, p.stdout)
            pattern = (rf"'{re.escape(full)}' "
                       r"(does not depend on any axioms|depends on axioms: \[([^\]]*)\])")
            found = re.findall(pattern, p.stdout)
            self.assertEqual(len(found), 1, "missing transitive axiom report: " + full)
            used = {a.strip() for a in found[0][1].split(",") if a.strip()}
            self.assertLessEqual(used, {"propext", "Classical.choice", "Quot.sound"})


if __name__ == "__main__":
    unittest.main()
