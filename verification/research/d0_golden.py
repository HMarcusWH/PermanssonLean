"""Generate and independently verify deterministic D0-F research examples.

Usage: python3 verification/research/d0_golden.py OUTPUT_DIRECTORY
Emitted manifests and hashes are illustrative mathematical evidence, not a
cryptographic signature or authorization to assert typed real-world validity.
"""
import hashlib
from fractions import Fraction as Q
from pathlib import Path
import sys

from d0_certificate import make_certificate, parse_json_strict
from d0_recheck_certificate import GOOD, check_certificate


HALF = ((Q(1, 2), Q(1, 2)), (Q(0), Q(1)))
SURE = ((Q(0), Q(1)), (Q(0), Q(1)))
A = ((Q(1, 2), Q(1, 2), Q(0)),
     (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(1)))
B = ((Q(0), Q(3, 4), Q(1, 4)),
     (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(1)))
C = ((Q(1, 4), Q(1, 4), Q(1, 2)),
     (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(1)))


def build_examples():
    return {
        "lean_two_state.json": make_certificate(
            [("half", HALF), ("sure", SURE)], HALF, 0, [1], [], 1),
        "python_three_state.json": make_certificate(
            [("A", A), ("B", B), ("C", C)], A, 0, [1], [2], 1),
    }


def main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output_directory")
    args = parser.parse_args(argv)
    dest = Path(args.output_directory)
    dest.mkdir(parents=True, exist_ok=True)
    manifest = []
    for name, raw in sorted(build_examples().items()):
        rec = parse_json_strict(raw)
        result = check_certificate(raw, rec["problem_sha256"])
        if result.status != GOOD:
            raise SystemExit(name + ": verification failed: " + result.reason)
        out = dest / name
        out.write_bytes(raw)
        if out.read_bytes() != raw or build_examples()[name] != raw:
            raise SystemExit("nonreproducible fixture " + name)
        manifest.append(name + " sha256=" + hashlib.sha256(raw).hexdigest() +
                        " problem_sha256=" + rec["problem_sha256"])
        print("PASS " + name + " selected=" + rec["calculation"]["selected"])
    (dest / "MANIFEST.txt").write_text("\n".join(manifest) + "\n", encoding="ascii")
    print("D0-F independent verification and deterministic regeneration PASS")
    return 0


if __name__ == "__main__":
    sys.exit(main())
