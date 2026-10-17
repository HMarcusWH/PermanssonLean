# C-Exit E — Random-entry occupation and scoped Proposition 4.2f (C70)

**Depends on:** PR #69 (C-Exit D, C69.1–C69.5). This lane is stacked on #69 and
must not be merged before it. **Anchors:** C70.1–C70.3 in
[V020_IMPLEMENTATION_INDEX.md](V020_IMPLEMENTATION_INDEX.md).
**Normative mathematics:** [integration spec](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md)
§2.3, Proposition 4.2f, V20.7–V20.9 and the random-entry paragraph.

## Theorem-to-source crosswalk

| Anchor | Mathematical statement | Lean declaration | Module |
|---|---|---|---|
| C70.1a | Finite-prefix estimate: `\|∫f dν̂_{k+T}(w) − ∫f dν̂_T(θ_k w)\| ≤ 2kC/(k+T)` for measurable `\|f\| ≤ C` (bound attained) | `abs_average_sub_shift_average_le`, `abs_integral_empiricalOccupation_sub_shift_le`, `integral_empiricalOccupation_eq_average` | `RegimeExit/OccupationPrefixDeletion.lean` |
| C70.1b | Deleting a finite prefix preserves the weak occupation limit | `tendsto_empiricalOccupation_of_tailShift` | same |
| C70.1c | Path law is linear in its initial law: `P_μ = P_• ∘ₘ μ` | `pathLaw_eq_bind` | `RegimeExit/RandomEntryOccupation.lean` |
| C70.1d | Normalized POSITIVE-mass arrival law, supported on `D`; stopped future = mass · its path law | `normalizedArrivalLaw`, `normalizedArrivalLaw_apply_dest`, `finiteStoppedFutureMeasure_eq_smul_pathLaw` | same |
| C70.1e | Generic a.e. transport: a path property certified for every `D`-supported law holds a.s. for the future re-indexed at every finite first exit into `D` | `stoppedFuture_ae_of_basinLaws`, `stoppedFuture_ae_all_of_basinLaws` | same |
| C70.1 | Target Exact GR in `almostSureWeak` ⇒ a.s. post-entry occupation convergence and WHOLE-path occupation convergence on the routed event | `postEntry_occupation_ae`, `randomEntry_occupation_ae` | same |
| C70.2a | Research mode: in-probability convergence of every bounded-continuous test integral | `inProbabilityWeak`, `occupationDeviationSet`, `occupationDeviationSet_measurable` | `RegimeExit/InProbabilityOccupation.lean` |
| C70.2b | Deviation transfer across the prefix, per exit time | `occupationDeviation_subset_shift`, `firstExit_shift_le_mass_mul`, `firstExit_deviation_tendsto_zero` | same |
| C70.2 | `P_y(routed ∩ \|∫f dν̂_{n+1} − ∫f dν'\| > ε) → 0`; eventually `P_y(\|…\| > ε) ≤ η + δ` | `randomEntry_occupation_inProbability`, `inProbability_deviation_eventually_le` | same |
| C70.3 | Scoped Prop. 4.2f: margin `κ_{ψ_B,J}(B₁) ≥ 1−η`; switch + retention + occupation event probability `≥ 1−η` (a.s. mode); retention `≥ 1−η` and in-probability bounds (in-probability mode); η = 0 ⇒ probability one; positive constitution / grounded PR only with `η<1` and all gates | `proposition_4_2f_almostSure`, `proposition_4_2f_inProbability`, `proposition_4_2f_eta_zero_almostSure`, `proposition_4_2f_uniformPR`, `switchRetainEvent`, `switchOccupationEvent`, `switchRetainEvent_prob_ge` | `RegimeExit/Proposition42f.lean` |

## Design decisions that matter mathematically

1. **No measurability of convergence sets is assumed.** The set of paths along
   which `ν̂_T` converges weakly need not be measurable for a general descriptor
   space. C70.1 therefore never integrates `z ↦ P_z(convergence)`; it applies the
   target certificate to a single genuine probability law (the normalized
   positive-mass arrival law) and transfers the a.e. statement back through
   `c • ·` (`Measure.ae_ennreal_smul_measure_iff`), pushforward (`ae_of_ae_map`)
   and restriction (`ae_restrict_iff'`), none of which needs measurability of the
   predicate. Consequently the switching event in `proposition_4_2f_almostSure`
   is measured by outer measure; it agrees a.e. with the measurable routed event.
2. **Normalization only for positive mass.** Zero-mass arrivals are handled by a
   separate case in which the stopped-future measure is `0`; no law is invented.
3. **Random prefix, explicit estimate.** Whole-path occupation is obtained from
   post-entry occupation through the PROVED `2kC/(k+T)` estimate, evaluated
   pathwise at the realized finite entry time.
4. **Convergence modes.** Only the frozen `ConvergenceMode.almostSureWeak` and
   the research `inProbabilityWeak` are transported. An arbitrary
   `ConvergenceMode.custom` is not: the generic transport covers any a.e.-form
   property of the *post-entry* path, but whole-path conclusions need prefix
   invariance, which a custom predicate need not have (Python counterexample
   `test_custom_mode_without_prefix_invariance_not_transported`).
5. **`inProbabilityWeak` is a declared research mode**, not a claim of
   equivalence with metric in-probability convergence on `ProbabilityMeasure H`.
6. **Frozen property.** `ψ_B(P_y) = P_y(τ_B = ∞)` is PR #67's
   `switchSurvivalProperty`, unchanged; the margin bound is PR #67's
   `switch_constitutive_margin_ge`, unchanged.

## Executable adversaries

`verification/research/test_c_exit_random_entry.py` (12 exact-`Fraction` tests):
prefix-deletion bound exhaustively on small sequences and its tightness; post-entry
and whole-path occupation with explicit `τ/T` rate; routed/trapped/remainder mass
bookkeeping; in-probability deviation bounded by η and NOT tending to zero when
η > 0; per-exit-time restart bound under the lemma hypothesis, and a witness that
the hypothesis is needed; leaky-target counterexample (entry without invariance,
exact stationary share 9/13 < 1); non-prefix-invariant custom mode; η = 1 vacuity.

## Verification evidence (local; stacked on #69 head `d8a96a4`)

- Lean 4.34.0 / pinned mathlib: all four modules compile; full
  `lake build PermanssonResearch` 4089/4089 jobs.
- `verification/research/c70_axiom_audit.py`: 37/37 declarations allowlisted.
- Research regressions 727/727.
- Focused workflow: `.github/workflows/c-exit-random-entry-smoke.yml`.

CI evidence is recorded on the C70 PR once it exists; nothing is inherited.
