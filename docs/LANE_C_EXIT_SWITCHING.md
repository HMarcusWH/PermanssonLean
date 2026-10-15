# Lane C-Exit B — Certified intervention-driven regime switching (PR #67)

**Status:** active implementation draft; no theorem may be advertised as compiled
before exact-branch-head Lean smoke and full PR synthetic-merge CI have passed.

**Frozen base:** `main@a5987dc1fb840c220bb2f56876f8227f50be11c5`
(merged PR #66, all four post-merge workflows green).
**Normative mathematics:** `docs/PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md`
§2.3, Proposition 4.2f / V20.7–V20.9.

## Acceptance obligations (do not silently weaken)

1. Actual admissible strategic `J` leaves `P` fixed; baseline `M` and
   `J.apply` use the original `α→P→U` canonical path laws.
2. Baseline and destination `IsExactGeneratedRegime` are independent,
   quantified certificates (not merely named invariant sets). For
   confirmatory PR, discharge source `IsConfirmatoryGeneratedRegime`
   and true frozen grounded-factorization as additional gates.
3. Strictly disjoint source `B` and destination `B'` and baseline
   comparison `B₁ ⊆ B₀` in the original constitutive grammar.
4. Routing `R_B^{J,∞}(y,B'₀) ≥ 1-η` for every `y∈B₁`, not just a
   selected source state. `η=1` permits no positive-margin assertion.
5. Actual canonical first-exit event equals the PR #66 routed mass.
6. Independently **prove**, never assume, conditional future-path law at
   each finite first-exit time. Zero-mass arrivals are never normalized.
7. Prove destination retention and the declared occupation limit under
   random entry, separately for almost-sure weak convergence and a
   precisely defined in-probability convergence mode; generic custom
   `ConvergenceMode` does not automatically transport.
8. Original path law survival `ψ_B` and pointwise/margin lower bound
   `κ ≥ 1-η`, with no substitute changed definition of constitution.
9. Actual rational positive instance whose source and destination each
   satisfy every Exact-GR gate, plus explicit countermodels to invalid
   shortcuts (finite hit ≠ persistence; η=1 does not imply κ>0).
10. No paper edits, no external empirical certification, no core changes.

## Build order

- `RegimeExit/SwitchRouting.lean`: distinct source/target certificates
  and actual first-exit path-law bridge.
- `RegimeExit/SwitchProperty.lean`: frozen full-path survival property
  and source-side baseline value.
- `RegimeExit/SwitchRestart.lean`: stop-at-finite-time continuation law.
- `RegimeExit/SwitchRetention.lean`: destination retention.
- `RegimeExit/SwitchOccupation.lean`: random-entry limits for supported modes.
- `RegimeExit/SwitchConstitution.lean`: measured survival and genuine
  positive uniform constitutive margin from the PR66 conservation law.
- `RegimeExit/SwitchGrounded.lean`: confirmatory grounded PR bridge.
- `RegimeExit/SwitchWitness.lean`: typed exact five-state positive and
  negative cases.

The independent exact-Fraction computational suite in
`verification/research/test_c_exit_switch.py` is not a Lean proof
and does not count as a missing theorem.

**Mandatory before promotion:** source-HEAD focused smoke, four workflow
PR synthetic-merge CI gates, transitive 3-axiom audit, source firewall,
direct root imports, C10 source proof evidence, D0-F golden tests, original
default target. No auto-merge or substitution of old-SHA green receipts.
