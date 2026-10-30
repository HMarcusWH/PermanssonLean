# Rational real-algebra witnesses — source-bound Lean bridge candidate

**Development scope:** ADV-02 (specialized real-algebra witnesses),
`feature/application-successor-full`, PR #115. `finite-algebra` computes exact
rational witnesses for four profiles (see `NUMERIC_ALGEBRA.md`);
`receipts.algebra` independently re-derives them.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/RationalAlgebraReceipt.lean` casts
rational matrices to real matrices (`rm`) and rational vectors to
`EuclideanSpace ℝ (Fin n)` (`ev`); the witness identities are decided on the
rationals as matrix or vector equalities.

- `checkSeam` → `checked_seam_rank`: `(rm H).rank ≤ 2` via `seam_rank_le_two`;
  with `diag H` constant, `checked_common_mode`: constant entries, rank ≤ 1
  and `quadratic (rm H) v = δ (Σ v)²`.
- `PSDWitness` (`H = L diag(d) Lᵀ`, `d ≥ 0`) → `psd_of_witness`:
  `(rm H).PosSemidef`.
- `checkSchur` → `checked_schur`: with `ℓ < 0` and `(H − ℓ) X = B`, Research's
  `shellComplement` equals the declared `S`; `shell_determinant` and
  `shell_equations_iff` then hold with `S`.
- `checkCompatible` → `checked_compatible`: for the positive (hence
  symmetric) operator `op H`, a preimage `x` of `b` makes nonnegativity of
  `singularBlockForm` equivalent to `0 ≤ g = c − ⟨b, x⟩`, and every preimage has
  response `c − g`. `checkIncompatible` → `checked_incompatible`: a kernel
  vector `z` with `⟨b, z⟩ ≠ 0` rules out every preimage and gives a negative
  value of the bordered form for every `c`.
- `checkGram` → `checked_gram`: the declared `w` is `gramWitness`, the gap is
  the declared rational, the signed form on `w` equals `−c · gap²` and stays
  negative under every continuous operator perturbation with norm below the
  declared threshold `τ = c · gap / ‖x‖²`.

The identification of a strategic source (a feature or operator map on
actual path laws) with these objects is not checked and not claimed; the
conditional Research theorems that need it are not applied.

## Source emission and replay

`proof.algebra_emit` runs the independent checker, refuses receipts whose
premises fail (seam equations or a zero Gram gap), emits matrices and vectors
as `!![…]` / `![…]` rational literals, and states the profile's checked
theorem and conclusion (for the singular profile also the sign of the
bordered form).

```bash
python3 -B -m permansson_app finite-algebra request.json --output /tmp/algebra
python3 -B -m permansson_app.proof.algebra_emit request.json \
  /tmp/algebra/algebra_receipt.json --output /tmp/permansson-algebra-instance
python3 -B -m permansson_app.proof.control_source_check --family algebra \
  request.json /tmp/algebra/algebra_receipt.json /tmp/permansson-algebra-instance
lake env lean /tmp/permansson-algebra-instance/ReifiedAlgebra.lean
```

`verification/research/test_application_algebra_live_lean.py` compiles seven
instances covering every profile and outcome, audits axioms, and requires
single-line mutations to fail at the falsified check: an asymmetric seam
matrix, a wrong common mode, a wrong shell complement, a negative LDLᵀ pivot,
a nonnegative shift, a wrong bordered gap, a false preimage, a kernel witness
outside the kernel, an overstated Gram threshold and a wrong Gram witness.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
