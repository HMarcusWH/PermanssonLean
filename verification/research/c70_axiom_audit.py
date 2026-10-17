"""Focused transitive axiom audit for the C70 (C-Exit E) declarations.

Reuses the C69 audit driver; every theorem/def in the listed modules must
depend only on {propext, Classical.choice, Quot.sound}.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from c69_axiom_audit import run_audit  # noqa: E402

MODULES = [
    "PermanssonResearch/RegimeExit/OccupationPrefixDeletion.lean",
    "PermanssonResearch/RegimeExit/RandomEntryOccupation.lean",
    "PermanssonResearch/RegimeExit/InProbabilityOccupation.lean",
    "PermanssonResearch/RegimeExit/Proposition42f.lean",
]
IMPORT = "PermanssonResearch.RegimeExit.Proposition42f"

if __name__ == "__main__":
    sys.exit(run_audit(MODULES, IMPORT, "C70"))
