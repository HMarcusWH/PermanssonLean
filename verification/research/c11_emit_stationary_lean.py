"""Generate literal-bound Lean proof of the exact C11 stationary family.

The generated code binds the complete rational matrix, all state weights,
bottom classes and frozen Boolean label vector. JSON parsing is not verified.
"""
from __future__ import annotations

import argparse
from pathlib import Path
from c11_stationary_execution import fraction, strict_loads
from c11_verify_stationary import verify_report


def rational_expr(v):
    q = fraction(v)
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"(({q.numerator} : ℚ) / ({q.denominator} : ℚ))"


def indexed(var, entries, n):
    if len(entries) != n or n < 1:
        raise ValueError("invalid reflected finite dimension")
    if n == 1:
        return entries[0]
    return "".join(f"(if {var} = ({i} : Fin {n}) then {entries[i]} else "
                   for i in range(n-1)) + entries[-1] + ")"*(n-1)


def finite_set(indices, n):
    if not indices:
        return f"(∅ : Finset (Fin {n}))"
    return ("({" + ", ".join(f"({x} : Fin {n})" for x in indices)
            + f"}} : Finset (Fin {n}))")


def emit_source(report):
    verify_report(report)
    obj = report["normalized_input"]
    n = obj["n"]
    mats = [indexed("y", [rational_expr(v) for v in row], n)
            for row in obj["matrix"]]
    matrix = indexed("x", mats, n)
    labels = indexed("x", ["true" if v else "false" for v in obj["descriptor"]], n)
    lines = [
        "import PermanssonResearch.ReverseSolver.C11ObservedStationary",
        "import Mathlib.Tactic", "",
        "open PermanssonResearch.ReverseSolver",
        "open PermanssonResearch.ReverseSolver.C11",
        "open PermanssonResearch.ReverseSolver.C10",
        "open PermanssonResearch.ReverseSolver.FiniteStrategicRealization", "",
        "attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov", "",
        "set_option autoImplicit false",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 0", "",
        "namespace C11ReifiedFixture", "",
        f"def kernel : RationalMarkovMatrix {n} where",
        f"  entry := fun x y => {matrix}",
        "  entry_nonneg := by decide",
        "  row_sum_one := by decide", "",
        f"def descriptor : Fin {n} → Bool := fun x => {labels}", ""
    ]
    for index, c in enumerate(report["classes"]):
        weights = indexed("x", [rational_expr(v) for v in c["stationary"]], n)
        lines += [f"def member{index} : ClassStationaryCandidate {n} where",
                  f"  classStates := {finite_set(c['states'],n)}",
                  f"  weights := fun x => {weights}", "",
                  f"theorem member{index}_accepted :",
                  f"    checkClassStationary kernel member{index} = true := by decide",
                  f"theorem member{index}_share :",
                  f"    trueShare member{index} descriptor =",
                  f"      {rational_expr(c['true_share'])} := by decide", ""]
    # These proofs use the reified kernel itself as the baseline AND the
    # intervention member. They certify the constructed D0 typed model,
    # not arbitrary external models or JSON parsing.
    for index, c in enumerate(report["classes"]):
        lines += [
            f"def member{index}_reportedTrue : ℚ :=",
            f"  {rational_expr(c['true_share'])}", "",
            f"theorem member{index}_native :",
            f"    certifiedProbability kernel member{index} member{index}_accepted =",
            "      PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw.stationaryForSet",
            "        (rationalStrategicIntervention kernel kernel).intervention.apply.inducedKernel",
            f"        (decodedClass member{index}.classStates) := by",
            f"  exact checked_stationary_eq_native kernel kernel member{index}",
            f"    member{index}_accepted", "",
            f"theorem member{index}_native_observed :",
            "    ((PermanssonResearch.MultipleLimit.ClassStationarySelectionLaw.stationaryForSet",
            "        (rationalStrategicIntervention kernel kernel).intervention.apply.inducedKernel",
            f"        (decodedClass member{index}.classStates)).map",
            f"          (fun y : PermanssonLean.JointState Unit (Fin {n}) =>",
            "            descriptor (encode y))).toMeasure",
            "        ({true} : Set Bool) =",
            f"      ENNReal.ofReal (member{index}_reportedTrue : ℝ) := by",
            f"  simpa only [member{index}_share, member{index}_reportedTrue] using",
            f"    (checked_observed_true_mass_eq_native kernel kernel member{index}",
            f"      member{index}_accepted descriptor)", ""
        ]
    members = ", ".join(f"member{i}" for i in range(len(report["classes"])))
    lines += [f"def completeFamily : List (ClassStationaryCandidate {n}) :=",
              f"  [{members}]", "",
              "theorem completeFamily_accepted :",
              "    checkStationaryFamily kernel completeFamily = true := by decide",
              "", "end C11ReifiedFixture", ""]
    for i in range(len(report["classes"])):
        lines.append(f"#print axioms C11ReifiedFixture.member{i}_accepted")
        lines.append(f"#print axioms C11ReifiedFixture.member{i}_share")
        lines.append(f"#print axioms C11ReifiedFixture.member{i}_native")
        lines.append(f"#print axioms C11ReifiedFixture.member{i}_native_observed")
    lines.append("#print axioms C11ReifiedFixture.completeFamily_accepted")
    return "\n".join(lines) + "\n"


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args(argv)
    report = strict_loads(args.report.read_bytes())
    args.output.write_text(emit_source(report), encoding="utf-8")
    print("C11 exact stationary Lean literal source emitted: " + str(args.output))


if __name__ == "__main__":
    main()
