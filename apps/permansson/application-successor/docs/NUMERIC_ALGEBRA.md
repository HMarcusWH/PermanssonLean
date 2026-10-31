# Rational real-algebra witnesses — numerical profile v1

**Source:** `PermanssonResearch/Specialized/SeamReduction.lean`,
`ShellSchur.lean`, `SingularCompatibility.lean` and `GramSeparation.lean`.
The numeric profile is a bounded exact-rational implementation; its Lean
correspondence for bounded instances is described in
[`ALGEBRA_LEAN_BRIDGE.md`](ALGEBRA_LEAN_BRIDGE.md). Application output
reports `lean_status=NOT_EXECUTED`.

## Profiles

Run `permansson-app finite-algebra <input.json> --output <new-directory>`.
Matrices and vectors are exact rationals of dimension at most four (shell
dimension at most three).

- `seam` (`H`, `pivot`): symmetry and the seam equations
  `H_ij − H_ip − H_pj + H_pp = 0`; with a constant diagonal the common mode.
  Failing premises are reported (`SEAM_PREMISES_FAIL`), not repaired.
- `schur` (`H`, `B`, `C`, `ℓ < 0`): an exact LDLᵀ witness `H = L diag(d) Lᵀ`
  with `d ≥ 0` (a matrix without one is refused), the solution `X` of
  `(H − ℓ) X = B` and the shell complement `S = (C − ℓ) − Bᵀ X`.
- `singular` (`H`, `b`, `c`): an LDLᵀ witness for symmetric `H`; either a
  preimage `x` of `b` with the response `⟨b, x⟩` and the bordered-form gap
  `c − ⟨b, x⟩`, or a kernel vector `z` with `⟨b, z⟩ ≠ 0`.
- `gram` (`x`, `y`, `c > 0`): the Gram gap `‖x‖²‖y‖² − ⟨x, y⟩²`, the witness
  `‖x‖² y − ⟨x, y⟩ x`, the signed value `−c · gap²` and the perturbation
  threshold `c · gap / ‖x‖²` (only for a positive gap).

`receipts.algebra.check_algebra` re-derives every identity from the request
without importing the producer and validates the stated witnesses and status.

## Limits

The identification of a strategic source model with these matrices or
vectors (a feature or operator map on actual path laws) is never established
here; it remains an explicit premise. No infinite-dimensional or complex
objects are encoded. Not an empirical or independently certified result.
