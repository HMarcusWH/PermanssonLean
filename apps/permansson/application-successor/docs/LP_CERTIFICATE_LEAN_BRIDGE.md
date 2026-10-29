# Exact LP certificates — genuine source-bound Lean bridge candidate

**Development scope:** S03L, `feature/application-successor-full`, PR #115.
The application already independently verifies rational primal/dual optimality
and strict Farkas certificates for its affine-normalized finite LP problem.
This increment adds a Lean theorem that lifts checked rational certificates to
claims over **all real-valued feasible competitors**, and a bounded source
emitter that binds exact original model and witness bytes.

## Mathematical contract

The original variables are transformed to `z = x - lower` and the objective to
`max c · z + offset`, accounting for minimization by negating coefficients.
Constraints `≤`, `≥` and `=` and finite upper bounds are transformed into
explicit rows `A z ≤ b`. The consumer checks this exact transformation
against the original requested LP *before* source emission.

- **Optimality:** `z ≥ 0`, `A z ≤ b`, `y ≥ 0`, `Aᵀy ≥ c`, and
  `c·z = b·y` imply `c·w ≤ c·z` for **every real** feasible `w`.
- **Infeasibility:** `y ≥ 0`, `Aᵀy ≥ 0`, and `b·y < 0` exclude **every real**
  feasible nonnegative `z`. A solver timeout or missing vertex never qualifies.
- No optimal solution is asserted to be unique; alternative tied certified
  solutions remain valid. A passing LP certificate is not an identified
  strategy, constitutive GR/PR status, or empirical estimate.

Lean's `LinearProgramReceipt.lean` contains the soundness proofs. The Python
reifier `proof.lp_emit` serializes exact rational arrays and explicit witness
entries into a concrete `ReifiedLP.lean` module with four proof obligations.
It is limited to at most three variables and six normalized constraint rows.
Any larger valid LP remains numeric-only rather than silently expanding the
claim or emitting unsupported source.

## Reproduction and genuine compiler replay

Use the *actual source* and actual original certificate receipt, not a solver
summary or a human-edited instance:

```bash
python3 -B -m permansson_app.proof.lp_emit original_lp.json verified_receipt.json \
  --output /tmp/permansson-lp-instance
python3 -B -m permansson_app.proof.lp_source_check original_lp.json verified_receipt.json \
  /tmp/permansson-lp-instance
```

These commands return **`NOT_EXECUTED`**, not kernel proof. The external
compiler stage must use the repository's pinned Lean 4 and mathlib:

```bash
lake build PermanssonResearch
lake env lean /tmp/permansson-lp-instance/ReifiedLP.lean
```

`verification/research/test_application_lp_bridge_live_lean.py` runs positive
original optimum and Farkas instances, checks actual transitive axiom output
against the permitted allowlist, and compiles deliberate false-certificate
mutations that must fail *semantically*. The test is part of the existing
Research Lean discovery, without changing any active workflow or toolchain.
A successful current-head source and compiler test is not itself an
independently authenticated result/receipt, nor an authorization to publish,
merge or change a research certificate status.

## Trust boundary

1. Original model bytes, source-normalized model semantic identity, original
   certificate bytes, witness digest and the exact Lean source digest must
   match. Changing any one rejects source binding.
2. P/U source identification, policies, mathematical CERT, scientific review,
   external provenance and release approval remain **distinct**.
3. The historical `E_TOOLING_CLOSURE` failure and T/T2 migration remain
   separate and are not relaxed by these numerical/proof changes.
4. All advertised Lean status remains `NOT_EXECUTED` in ordinary numeric
   application outputs. A future trusted proof-evidence consumer must verify
   exact Git source H/S, expected theorem type, compiler and axiom audit,
   negative mutations, immutable logs, and origin authentication before
   changing a *specific receipt*'s status.
