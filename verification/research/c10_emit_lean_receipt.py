"""Emit a *data-bound* Lean kernel-checkable C10 receipt from verified JSON.

This is deliberately a transparent reifier, NOT a verified JSON parser.
The generated Lean source literally includes the checked rational matrices,
the entire frozen comparison/menu order, all class weight tables and output
claims. Its checkFullReceipt theorem is proved by kernel-checked reduction.
The Python source cannot grant baseline Exact-GR certification.
"""
from __future__ import annotations

import argparse
import json
from fractions import Fraction
from pathlib import Path

from c10_verify_receipt import verify_receipt
from c10_exact_execution import strict_object, exact_fraction


def fraction_expr(v: str) -> str:
    q = exact_fraction(v)
    if q.denominator == 1:
        return f"({q.numerator} : ℚ)"
    return f"(({q.numerator} : ℚ) / ({q.denominator} : ℚ))"


def choice(var: str, values: list[str], dim: int) -> str:
    if len(values) != dim or dim < 1:
        raise ValueError("wrong finite table length")
    if dim == 1:
        return values[0]
    prefix = [f"(if {var} = ({j} : Fin {dim}) then {values[j]} else "
              for j in range(dim - 1)]
    return "".join(prefix) + values[-1] + ")" * (dim - 1)


def indexed_finite_set(items: list[int] | tuple[int, ...], n: int) -> str:
    if not items:
        return f"(∅ : Finset (Fin {n}))"
    return f"({{{', '.join(f'({i} : Fin {n})' for i in items)}}} : Finset (Fin {n}))"


def matrix_expr(matrix: list[list[str]], n: int) -> str:
    return choice("x",
                  [choice("y", [fraction_expr(v) for v in row], n)
                   for row in matrix], n)


def matrix_list_expr(matrices: list[list[list[str]]], n: int) -> str:
    return choice("i", [matrix_expr(m, n) for m in matrices], len(matrices))


def cert_defs(prefix: str, geometry: dict, n: int) -> str:
    classes = geometry["classes"]
    finite_classes = [
        indexed_finite_set(c, n) for c in classes
    ]
    class_names = [f"{prefix}Class{k}" for k in range(len(classes))]
    code = []
    for name, members in zip(class_names, finite_classes):
        code.append(f"def {name} : Finset (Fin {n}) := {members}")
    class_set = f"({{{', '.join(class_names)}}} : Finset (Finset (Fin {n})))"
    code.append(f"def {prefix}Cert : DirichletCertificate {n} where")
    code.append(f"  classes := {class_set}")
    columns = [
        choice("x", [fraction_expr(v) for v in col], n)
        for col in geometry["absorption"]
    ]
    if columns:
        code.append("  weight := fun C x => " +
                    "".join(f"(if C = {nm} then {col} else "
                            for nm, col in zip(class_names, columns)) +
                    "(0 : ℚ)" + ")" * len(columns))
    else:
        code.append("  weight := fun _ _ => (0 : ℚ)")
    return "\n".join(code)


def emit_source(receipt: dict) -> str:
    verify_receipt(receipt)
    raw = receipt["normalized_input"]
    n = raw["n"]
    m = len(raw["menu"])
    if not (n > 0 and m > 0):
        raise ValueError("invalid dimensions")
    lines = [
        "import PermanssonResearch.ReverseSolver.C10FullReceipt",
        "import Mathlib.Tactic",
        "",
        "/-! Deterministically reified C10 input-bound receipt.",
        "The source hash identifies the canonical input; it is not a proof.",
        f"Canonical input SHA-256: {receipt['input_sha256']}",
        "The actual rational data and claimed output are fully reified below.",
        "-/",
        "open PermanssonResearch.ReverseSolver.C10",
        "set_option autoImplicit false",
        "set_option maxRecDepth 8192",
        "set_option maxHeartbeats 0",
        "",
        f"def reifiedRaw : RawInput {n} {m} where",
        f"  baseline := fun x y => {matrix_expr(raw['baseline'], n)}",
        f"  members := fun i x y => {matrix_list_expr([x['matrix'] for x in raw['menu']], n)}",
        "  descriptor := fun x => " +
        choice("x", ["true" if x else "false" for x in raw["descriptor"]], n),
        "  comparison := " + indexed_finite_set(raw["comparison"], n),
        "",
        "/-- This performs the actual Lean row-stochasticity/input validation.",
        "No untrusted numeric validity flags enter the checked structure. -/",
        "def reifiedChecked : CheckedInput reifiedRaw :=",
        "  (validateInput reifiedRaw).get (by decide +kernel)",
        "",
    ]
    lines.append(cert_defs("reifiedBase", receipt["baseline"], n))
    for j, item in enumerate(receipt["members"]):
        lines.append("")
        lines.append(cert_defs(f"reifiedMember{j}", item["geometry"], n))
    lines.extend([
        "",
        f"def reifiedMenu : MenuCertificate {n} {m} where",
        "  baseline := reifiedBaseCert",
        "  members := fun i => " +
        choice("i", [f"reifiedMember{j}Cert" for j in range(m)], m),
        "",
        f"def reifiedReceipt : FullReceipt {n} {m} where",
        "  core := {",
        "    classTables := reifiedMenu",
        "    reportedMargin := fun i => " + choice("i",
            [fraction_expr(item["margin"]) for item in receipt["members"]], m),
        f"    selectedIndex := ({next(i for i,x in enumerate(raw['menu']) if x['id']==receipt['selected'])} : Fin {m})",
        "    reportedOptimum := " + fraction_expr(receipt["optimum"]),
        "    ties := [" + ", ".join(
            f"({j} : Fin {m})" for j, x in enumerate(raw["menu"])
            if x["id"] in receipt["ties"]) + "]",
        "  }",
        "  baselineEvent := fun x => " + choice(
            "x", [fraction_expr(x) for x in receipt["baseline"]["event"]], n),
        "  memberEvent := fun i x => " + choice(
            "i",
            [choice("x", [fraction_expr(x) for x in item["geometry"]["event"]], n)
             for item in receipt["members"]], m),
        "  pointwiseEffect := fun i x => " + choice(
            "i",
            [choice("x",
                    [fraction_expr(v) for v in item["effects"]]
                    if receipt["format"].endswith(".v2") else
                    [fraction_expr(str(abs(Fraction(b) - Fraction(v))))
                     for b, v in zip(receipt["baseline"]["event"],
                                     item["geometry"]["event"])], n)
             for item in receipt["members"]], m),
        "  worstState := fun i => " + choice(
            "i", [f"({item['worst_start']} : Fin {n})" for item in receipt["members"]], m),
        "",
        "/-- All claims match the COMPLETE exact reified data and the",
        "independently proved C10 certificate checker. Kernel reduction only. -/",
        "theorem reifiedReceipt_valid :",
        "    checkFullReceipt reifiedRaw reifiedChecked reifiedReceipt = true := by",
        "  decide +kernel",
        "",
        "/-- The checked reference is a proof term, not a trusted label. -/",
        "theorem reifiedReceipt_conditions :",
        "    FullReceiptConditions reifiedRaw reifiedChecked reifiedReceipt :=",
        "  checkFullReceipt_sound reifiedRaw reifiedChecked reifiedReceipt",
        "    reifiedReceipt_valid",
        "",
        "#print axioms reifiedReceipt_valid",
        "#print axioms reifiedReceipt_conditions",
        "",
    ])
    return "\n".join(lines)


def main(argv=None):
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("receipt")
    p.add_argument("lean_output")
    args = p.parse_args(argv)
    with Path(args.receipt).open(encoding="utf-8") as f:
        obj = json.load(f, parse_float=lambda _: (_ for _ in ()).throw(
            ValueError("floating JSON number")),
            object_pairs_hook=strict_object)
    source = emit_source(obj)
    output = Path(args.lean_output)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(source, encoding="utf-8")
    print(f"C10 emitted input-bound Lean receipt: {output}")


if __name__ == "__main__":
    main()
