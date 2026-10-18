# Source review of the selected A3, strategy and quantitative-path scope

Review date: 2026-10-18. Baseline repository HEAD at review:
`17f380e94f4858c455a85b57d3a576c076c9d667`.

This is a read-only mathematical interface and source review of the current
working tree against the supplied `closure_contracts.json`, chapter 02,
chapter 04 and chapter 05. It does not infer mathematical coverage from a
receipt's PASS label. Sources, quantifiers, constructions and conclusions
were inspected directly. No Lean source or acceptance routing was changed,
and no compiler run was performed for this review. The sampled-source hash
manifest beside this document identifies the reviewed bytes. The final
committed-head review and CI remain separate obligations.

## Contract comparison

| Contract and selected theorem | Source-level conclusion examined | Finding and boundary |
| --- | --- | --- |
| X1-S01: bounded finite discounted games; arbitrary nonanticipating behavioral unilateral deviations; independent current opponent draw. S-TRACE / S-VERIFY / S-X1. | `ActionTrace.BehavioralPolicy`, `step`, the canonical trace/state erasure bridge; `DiscountedVerification.finite_performance_difference`, `discounted_verification`; X1 `expected_exact_behavioral_performance_difference`, `baseline_trace_stateLaw_eq_original`. | The history retains completed joint actions and states, and each rule returns a real probability row. The current own action is chosen before the independent fixed opponent row. Both indexed players and every finite-state start are quantified. Rewards are evaluated on action-retaining paths; whole original state-law equality is proved after erasure. The learner-update mode keeps equilibrium action rows and is explicitly not promoted to an equilibrium claim for the old learner-action baseline. |
| A3-K01: finite metric probabilities and complete separable Borel first-moment extension. A-KR-FIN / A-KR-POLISH. | `finite_couplingW1_eq_dual_supremum`; `firstMoment_w1DualLE_iff_couplingW1_le`; `firstMoment_couplingW1_eq_dual_supremum`. | Finite transport is constructed from separation. General transport is constructed by measurable finite nearest-center quantization, clipped Lipschitz extensions and normalized restricted-cell product lifts. Integrability and exact original marginals are derived. No optimal-coupling or transport-duality premise replaces the reverse inequality. The general infimum identification actually needs separability/Borel structure and first moments, without completeness. It does not claim an attained optimal coupling on that wider profile. |
| A3-C01: direct bounded-Lipschitz row criterion giving the exact original global dual predicate; finite Dobrushin and metric row couplings. A-CONTRACT. | `isW1Contraction_of_test_images`, `isW1Contraction_of_row_couplings`, `isW1Contraction_dobrushin`, `StateMetricBounds.original_isW1Contraction`. | The direct proof quantifies over all probability laws and all admissible real input dual bounds, without restricting them to P1. The zero contraction case is handled separately. The TV route retains diameter/minimum-separation factors; it is not an unbounded-metric TV-to-W1 claim. A numerical coefficient less than one remains an explicit strictness obligation. Actual zero-factor refresh/finite primitive regressions discharge it in concrete models. |
| A3-I01: contraction preserving first moments on a complete separable space, with finite shortcut. A-COMPLETE / A-INVARIANT. | `FirstMomentProbability.cauchySeq_has_limit`; `exists_unique_invariant`; `automatic_invariant_and_convergence`; `generated_coupling_bound`. | Countable coupling gluing and summable transport costs construct the P1 limit. Banach then constructs the invariant law from first-moment preservation and the original strict global contraction. Uniqueness is in P1. The generic generated pair separately requires contraction/moment preservation of both kernels; the regenerative pair constructs both invariant laws independently and uses only baseline contraction for its perturbation estimate. Neither branch infers a perturbed unique invariant solely from baseline contraction. |
| A3-F01: explicit occupation-limit functional, four finite unique-class kernels; separate regenerative Polish profile with moments. A-FACTOR-FIN / A-FACTOR-REGEN. | Finite and regenerative `four_actual_factorizations` and `generated_occupationMargin_robust`; `RegenerativeFirstMoment.canonical_descriptor_empirical_tendsto`. | The four identities concern the actual baseline, perturbed baseline, intervention and perturbed intervention typed path laws, for every start, with one predeclared property. The regenerative P1 profile derives all-initial scalar laws, empirical W1 convergence and tail uniform integrability from an explicit regenerative reward condition. It does not insert invariant measures as assumed path-law values. The precise global functional boundary is discussed below. |
| A3-P01: weighted product metric and conditional stage couplings, primitive errors and sensitivities. A-PRIMITIVE. | `sequential_weighted_cost`; `PrimitiveMetricBounds.exists_weighted_coupling`, `weighted_induced_bound`, `original_induced_bound`; `MetricProtocolBounds.original_occupationMargin`. | The implementation realizes the chapter's finite conditional-coupling alternative. It constructs couplings of actual alpha/P/U rows by finite KR, in chronological order, at every input. Its general measurable bounded-diameter TV wrapper is a distinct profile. No general nonfinite measurable sequential transport assembly is exported by the finite modules. A status covering A3-P01 should retain this finite primitive-route qualification. |
| E1-G01: finite spaces or the explicit measurable common-mass/RN profile; every fine row. Q-LIFT / Q-GEOMETRIC. | `map_liftProjectedDensity`, `projectedCommonKernel_mass`, `approxQuotient_prefix_tv_le_geometric`. | The fine common subkernel is actually constructed by pulling back a jointly measurable clipped coarse RN density. The RN `CountableOrCountablyGenerated` instance is visible. Fine prefix mass and its projected domination are propagated without making the projected fine process Markov. The theorem quantifies over every fine start and row. |
| A2-P01: actual ordered primitive composition with measurable common kernels and uniform stage errors. Q-PRIMITIVE. | `primitiveCommon_mass_ge_product`, `inducedKernel_tv_le_primitive_product`. | The retained product follows from uniform conditional masses in the actual alpha/P/U integrals. Independence of three error events is neither assumed nor deduced. Changed physical P is comparison between two models; an intervention within either model still has its original fixed P. |
| A2-P02 and E1-P01: history evolution with initial mismatch and expected local defects; summable whole-path scores and full-product variant. Q-LOCAL / Q-DISCOUNT. | `historyEvolution_tv_le_sum`, `discounted_output_score_error_initial`, `FullPathProduct.path_tv_le_product`. | Local defects are averaged under the first process's actual evolving history law. Normalized discounting retains the time-zero mismatch. The separate whole-product theorem uses constructed retained common histories and literal prefix-marginal identifications before the generating-ring extension to all product events. Its precise boundaries are discussed below. |

## Primitive weighted factors and global contraction

For strategic weight `a` and world weight `b`, the sequential result has
the literal budget

`a*deltaU + (b+a*LUx)*deltaP + (a*LUa+(b+a*LUx)*LPa)*deltaAlpha`.

The reference world action sensitivity and reference update action/world
sensitivities are assumptions on every input. The resulting plan has the
actual original induced rows as marginals. The two-coordinate fixture has
weights 2 and 3 and actual transport cost 5, including a second comparison
where changed world P propagates through update's world sensitivity.

The weighted metric is declared locally in the weighted conclusion. The
conversion to the frozen product-max metric explicitly divides the budget
and state contraction factor by `min(a,b)`, with both weights strictly
positive. The code does not silently change the metric used by the old
margin theorem. `MetricProtocolBounds` requires four actual same-model
primitive state-sensitivity records, two error records and four strict
numerical factor inequalities before it generates all invariant/class and
factorization data. General measurable unbounded-coordinate primitive
coupling selection/assembly is outside this finite construction.

The general direct contraction theorem is broader than this finite
instantiation: its proof rescales each bounded measurable Lipschitz kernel
image for positive rho and handles rho zero by constancy. Thus the original
all-probability-law `IsW1Contraction` is retained; P1 is only introduced
where transport finiteness or invariant construction actually requires it.

## The functional on P1 and the original global functional

The new descriptor target is the actual pushforward of the constructed
geometric invariant law. Its first moment follows from the nonnegative
extended series `sum r^n integral |f| d(seed R^n) < infinity`. An infinite
Bochner integral's default value cannot make this condition true.

Stationary L1 truncation is used only under the invariant initial law.
The arbitrary-initial transfer separately uses an actual common law of
mass `1-r^n`, a whole shifted-path TV bound, and a measurable pointwise
shift-invariant Cesaro convergence event. It assumes no initial absolute
continuity and no stationarity of an arbitrary initial law. Countably many
error/cell scalar limits then imply genuine empirical P1 convergence via
the finite quantization estimate. Uniform excess tails and ordinary
distance-times-tail indicators are separately proved for all positive
empirical horizons. The reset-and-increment real regression has an
unbounded identity descriptor and positive invariant atoms arbitrarily far
away; it is not only an infinite ambient type with compact support.

The global selector is fixed independently of kernels. It selects a P1
empirical limit or a fixed P1 fallback, is strongly measurable, and has a
weak-Borel measurable probability projection. It identifies actual P1
limits. It does not claim to identify every merely weak limit with failing
first moments. This is the selected added-moment regenerative profile,
not an unrestricted weak-limit selector assertion.

For the original margin, the source explicitly supplies both a globally
defined `Phi : Measure V -> Real` satisfying the original all-probability
dual-Lipschitz predicate and a bounded continuous P1 functional `Phi_b`,
with equality `Phi_b nu = Phi nu.measure` for every P1 law. A functional
defined only on P1 is not silently accepted as a global source functional.
The chapter explicitly allows bounded Borel Phi continuous for the limit
topology; the bounded continuous P1 input implements that profile. The four
primitive descriptor budgets, four state moment budgets, shared full
comparison states, baseline contractions and every-row errors remain
visible in the final theorem. An arbitrary preexisting time-zero or
survival property is not automatically an occupation property.

## Infinite product and boundary cases

`DependentHistory.evolution` genuinely evolves dependent history types
`H n` using `(mu_n compProd K_n).map Prod.snd`. Repeating the same evolution
with an initially common finite measure and finite kernels dominated by
both original kernels constructs a common law with mass at least
`(1-epsilon0)*product_(t<n)(1-eta_t)`. No recurrence for the actual TV
discrepancy is an input.

The full-law theorem requires the supplied actual P and Q to have exactly
these prefix marginals. This is a substantive identification hypothesis,
not a claim that arbitrary kernels already define those particular
original infinite laws. `CylinderTotalVariation` proves the extension to
the entire product sigma algebra by approximating with the generating
cylinder ring in the sum of P and Q.

For `0 <= eta_t <= 1` and summable eta, actual multipliability and partial
product convergence give
`TV(P,Q) <= 1-(1-epsilon0)*product'_t(1-eta_t)`.
Zero defects retain exactly epsilon0. Initial epsilon0 equal to one gives
the trivial bound one, and the opposing constant Bool path laws actually
attain TV one. A single unit defect is allowed in a summable sequence and
forces product zero. Fixed positive recurring defects are proved not
summable, and their finite-prefix budget tends to one. This argument does
not transfer exact infinite survival across recurring leakage.

## Strategy information and payoff scope

The Bellman calculation is applied at every completed history. It retains
the terminal `beta^N` value at finite horizons and proves an explicit
geometric payoff tail before passing to infinity. `DiscountedTraceExpectation`
identifies the scalar series with the actual canonical trace integral.
Both Player indices are checked in the exact eight-case advantage table;
the exact loss coefficient is `9/211`. `strategy_physical_expect_actual`
identifies P followed by the actual old-world/action update. The baseline
trace's erased full state measure equals the original equilibrium model's
typed `pathLaw`, rather than merely agreeing at single times.

The finite behavioral policy may depend on the entire completed history
and time and use arbitrary real probability rows. The current opponent
draw, future noise, risk-sensitive objectives and changes to physical P
are outside this interface. `InformationBoundary.actual_step_fair_matching`
versus `peeked_fair_matching` and the no-copy theorems supply actual
information countermodels, separately from the datatype gate. A general
private-seed behavioralization theorem or correlated-current-draw
verification theorem is not asserted by these modules and is not part of
the selected behavioral contract.

## Acceptance reference advice: D-03 and F-02

The current routing at review still points D-03 principally at the old
success monitor. Stronger addressable references are now available:

- `ThroughHorizonRisk.initial_risk_iff_time`,
  `actual_risk_probability_eq_occupancy` and
  `actual_success_integral_eq_original` in
  `ReverseSolver/ThroughHorizonRiskMonitor.lean`.
- `danger_at_zero_counts`, `danger_after_completed_success_counts`,
  `simultaneous_target_danger_counts` and
  `failure_and_danger_are_not_complements` in
  `ReverseSolver/ThroughHorizonRiskFixture.lean`.

These assert that a separate actual danger flag keeps updating after
success while the original success score is preserved. This is stronger
evidence for the selected separate risk clause than success absorption
alone. No routing was changed by this review.

F-02 can similarly cite `NatPrivateClock.advancing_update`, `actual_atom`,
`inherited_strictness`, `inherited_exogeneity`, `natural_scheduled_row` and
`natural_projection`. `NatClockTests.treated_clock_not_strict` in
`verification/research/MultiAgentNatPrivateClock.lean` is a named actual
negative theorem for a clock driven by the treated action. The same
compiler-checked fixture has anonymous examples of next-phase atom one
and stale-phase atom zero, and `schedule_nonperiodic` proves that its
schedule cannot be replaced by any periodic finite clock. Anonymous
examples should be cited as fixture compilation evidence, not invented
addressable theorem names. These current Nat modules use countable old
strategic coordinates and finite world/action coordinates; the separately
assigned arbitrary-measurable Nat-clock extension is not adjudicated here.
