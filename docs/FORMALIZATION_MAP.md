# PermanssonLean formalization map

This repository formalizes the mathematical core of **Permansson Regimes v0.1.7** in Lean 4.

## Claim firewall

Status labels are used strictly:

- **PROVED** — accepted by Lean on the pinned toolchain.
- **SCAFFOLDED** — definitions/types exist, theorem not yet formalized.
- **OPEN** — not yet represented in Lean.
- **EMPIRICAL / OUT OF SCOPE** — depends on data, scientific identification, or literature priority rather than pure formal derivation.

Green CI means only that the checked Lean declarations compile. It does not upgrade OPEN or empirical claims.

## Dependency DAG

| Layer | Paper object | Lean target | Status |
|---|---|---|---|
| 0 | Measurable spaces / kernels | mathlib | PROVED upstream |
| 1 | Joint state Y = S × X | `JointState` | SCAFFOLDED |
| 1 | Action-selection kernel α | `StrategicGenerator.action` | SCAFFOLDED |
| 1 | Strategic-update kernel U | `StrategicGenerator.update` | SCAFFOLDED |
| 1 | World-transition kernel P | `StrategicWorldModel.world` | SCAFFOLDED |
| 2 | Induced joint kernel K_{G,P} | `StrategicWorldModel.inducedKernel`, `inducedKernel_isMarkov` | PROVED |
| 2 | Paper-level setwise / indicator semantics | `inducedKernel_apply`, `inducedKernel_apply_indicator` | PROVED |
| 3 | Canonical Ionescu–Tulcea path law | `StrategicWorldModel.pathLaw`, `pathLaw_isProbability` | PROVED |
| 3 | Initial and finite-history transition identities | `pathLaw_prefix_zero`, `pathLaw_has_transition_pair` | PROVED |
| 3 | RCD Markov transition statement | `pathLaw_has_transition` | PROVED under explicit standard-Borel / nonempty hypotheses |
| 3 | Full path-law existence and uniqueness | `pathLaw_existsUnique`, `joint_process_well_posed` | PROVED |
| 4 | Frozen regime specification Σ=(B,B₀,h,ν,c) | `RegimeSpecification` | PROVED |
| 4 | Admissible initial-law class D(B₀) | `IsAdmissibleInitialLaw`, `dirac_admissible_iff` | PROVED |
| 4 | Assumption 4.1 ex-ante non-triviality | `Assumption41`, `basinHasTwoStates_iff_pathLawNontrivial` | PROVED as formal gate; chronology represented by immutable input boundary |
| 4 | Empirical descriptor occupation law | `empiricalOccupation`, `measurable_empiricalDescriptor` | PROVED as probability-valued construction with measurable descriptor map |
| 4 | Frozen occupation convergence semantics | `ConvergenceMode`, `IsLimitingOccupationLaw` | PROVED interface; almost-sure weak constructor formalized |
| 4 | Exact Generated Regime semantic kernel | `IsExactGeneratedRegime` | PROVED definition with well-posedness, Assumption 4.1, exact invariance, and all-admissible-law occupation convergence |
| 4 | Paper ambient Exact GR boundary | `IsPaperExactGeneratedRegime`, `IsPaperConfirmatoryGeneratedRegime` | PROVED wrapper requiring nonempty Polish/Borel S,X,H and standard-Borel A |
| 4 | Confirmatory descriptor-nondegenerate GR | `IsConfirmatoryGeneratedRegime`, `IsDescriptorNondegenerate` | PROVED |
| 4a | Polish descriptor-space generality / BL metrization proposition | theorem layer | OPEN |
| 4b | Exact invariance ↔ survival forever (Prop. 4.2) | `exactInvariant_iff_survivalForever` | PROVED |
| 5 | Killed-kernel finite persistence | `survivalProbability_eq_killedSurvivalMass`, `finitePersistence_iff_killed`, `oneStepRetention_pow_lowerBound`, `expectedExitTime_eq_greenSeries` | PROVED |
| 6 | Typed interventions | `InterventionReplacement`, `InterventionFamily`, `TypedIntervention`, `applyReplacement` | PROVED |
| 7 | PR constitution | `RegimePropertyMap`, `ConstitutiveComparisonSet`, `IsStrategicallyConstitutive`, `IsGeneralizedPermanssonRegime` | PROVED |
| 8 | Uniform constitutive margin / perturbation robustness | `constitutiveEffect`, `constitutiveMargin`, `IsUniformlyStrategicallyConstitutive`, `constitutiveMargin_perturbation_abs_le`, `robustUniformConstitution` | PROVED |
| 8b | Finite-horizon kernel-to-path TV envelope (Prop. 5.4) | path-perturbation theorem layer | OPEN |
| 9 | Intervention-family signatures | equivalence module | OPEN |
| 10 | Quotient preservation theorem | quotient module | OPEN |
| 11 | EGR → GR embedding | compatibility module | OPEN |
| 12 | QSD subclass | optional QSD module | OPEN |
| X | Scalar-defect / finite-detection / first-bad / singular lane | research modules | OPEN |

## First proof milestone — induced joint kernel

The induced kernel

\[
K_{\mathfrak G,P}(E\mid s,x)
=
\int_A\int_X\int_S
\mathbf 1_E(s',x')\,
U(ds'\mid s,x,a,x')\,
P(dx'\mid s,x,a)\,
\alpha(da\mid s,x)
\]

is implemented by `StrategicWorldModel.inducedKernel`.

The formalization explicitly preserves the dependency order
`α → P → U`: it uses `Kernel.compProd` rather than an independent product,
reassociates the retained history before applying `U`, and drops the realized
action only after the strategic update has consumed it.

The following are checked on the pinned Lean/mathlib toolchain:

- `inducedKernel_isMarkov`: the construction is a Markov kernel on `S × X`;
- `inducedKernel_apply`: the setwise law expands in the exact `α → P → U` order;
- `inducedKernel_apply_indicator`: the construction agrees with the paper's
  displayed triple-indicator integral.

## Second proof milestone — canonical path law and well-posedness

For an initial probability law `mu0` on `S × X`, the formalization constructs

\[
\mathbb P_{\mu_0,M}\in\mathcal P\big((S\times X)^{\mathbb N}\big)
\]

by Ionescu--Tulcea from the exact kernel `M.inducedKernel`.

The proof surface is split so existence, transition semantics, and uniqueness are
independently visible:

- `pathLaw_isProbability`: the constructed trajectory law is a probability measure;
- `pathLaw_prefix_zero`: the zeroth prefix is the declared initial law;
- `pathLaw_has_transition_pair`: every finite-history/next-state law is generated by
  the stationary induced kernel;
- `pathLaw_has_transition`: under explicit standard-Borel and nonempty assumptions,
  the regular conditional law of the next state given the finite history is the
  stationary induced kernel evaluated at the most recent coordinate;
- `prefix_maps_eq_of_initial_and_transition`: common initial law and transition-pair
  identities force equality of all finite-prefix laws;
- `measure_eq_of_prefix_maps_eq`: equality of all finite prefixes determines the
  full trajectory probability law;
- `pathLaw_existsUnique`: there is exactly one trajectory law satisfying the
  model-level specification;
- `joint_process_well_posed`: combines the proved Markov property of
  `M.inducedKernel` with full path-law existence and uniqueness.

## Third proof milestone — Exact Generated Regime semantics

The formalization now represents the frozen ex-ante regime object

\[
\Sigma=(B,B_0,h,\nu,\mathfrak c),
\]

including Borel region/basin certificates, the global measurable descriptor, a bundled
probability target law, and an immutable convergence-mode interface. The following
Section-4 objects are checked on the pinned toolchain:

- `IsAdmissibleInitialLaw`: the exact class \(\mathcal D(B_0)\), with
  `dirac_admissible_iff` for point initializations;
- `Assumption41`: nonempty basin, predeclared region non-triviality, descriptor
  variation on B, and the literal distinct-baseline-path-law basin condition;
- `basinHasTwoStates_iff_pathLawNontrivial`: under the point-separating Borel
  state-space assumption, machine-checks the paper's statement that Assumption
  4.1(iv) is equivalent to having at least two distinct basin states;
- `empiricalOccupation`: the exact finite-horizon empirical descriptor law as the
  push-forward of a uniform probability on `Fin T`, hence probability-valued by type;
  `measurable_empiricalDescriptor` and `measurable_descriptorAt` certify that the
  push-forward maps use the intended measurable branches of mathlib's measure map;
- `ConvergenceMode` and `IsLimitingOccupationLaw`: a frozen ex-ante semantic
  interface allowing the paper's canonical modes or another precisely declared mode;
- `IsExactlyInvariant`: one-step exact invariance of B under the proved induced kernel;
- `IsExactGeneratedRegime`: the reusable semantic kernel of Definition 4.3, including
  an explicit well-posedness gate discharged by the previously proved path-law
  uniqueness theorem and convergence for every admissible initial law;
- `IsPaperExactGeneratedRegime` / `IsPaperConfirmatoryGeneratedRegime`: paper-level
  wrappers exposing Assumption 3.1 / Section 4.1 ambient requirements at the type
  boundary: nonempty Polish/Borel strategic and world spaces, standard-Borel action
  space, and Polish/Borel descriptor space;
- `IsConfirmatoryGeneratedRegime`: Exact GR plus basin-reachable descriptor-law
  nondegeneracy, kept distinct from forward descriptor richness.

Proposition 4.1a's Polish/BL metrization theorem remains deliberately unpromoted.
The persistence layer is now machine-checked: finite-horizon path survival is identified
with killed-kernel mass, exact invariance is equivalent to almost-sure indefinite
retention, the one-step retention floor yields the paper's q^L bound, and the extended
expected first-exit time equals the killed-kernel Green/tail series.

## Fourth proof milestone — persistence calculus

The Section-4.2 persistence layer is checked through the following declarations:

- `killedKernel`: restriction of the induced kernel to the frozen regime region;
- `survivalProbability_eq_killedSurvivalMass`: exact path/killed-kernel bridge;
- `finitePersistence_iff_killed`: equivalence of the finite path and killed-kernel gates;
- `oneStepRetention_pow_lowerBound`: the uniform one-step retention q^L lower bound;
- `exactInvariant_iff_survivalForever`: Proposition 4.2 in iff form;
- `expectedExitTime_eq_greenSeries`: the extended Green/tail-sum identity.

## Fifth proof milestone — typed intervention grammar

The intervention layer freezes both the component target and the admissible replacement
family before any constitutive claim is made:

- `InterventionTarget.IsStrategic` separates strategic-generator interventions from
  structural world-transition interventions;
- `InterventionReplacement` is target-indexed, so a replacement kernel for one target
  cannot inhabit another target's payload type;
- `InterventionFamily.targetOf` freezes the target of each predeclared component;
- `InterventionFamily.admissible` keeps application-specific feasibility explicit
  rather than silently treating every Markov replacement as admissible;
- `applyReplacement` rebuilds the strategic-world model while copying all untargeted
  primitives from the baseline model;
- `applyReplacement_world_eq_of_strategic` proves that every strategic intervention
  holds the world-transition kernel P fixed;
- `TypedIntervention.intervenedKernel_isMarkov` proves that every well-typed
  intervention still induces a Markov kernel.

## Sixth proof milestone — generalized Permansson constitution

The constitution layer now formalizes the paper's pointwise strategic-constitution
criterion and Definition 5.1 without strengthening the basic hypothesis surface:

- `RegimePropertyMap` evaluates the complete point-initialized path probability law
  and deliberately imposes no measurability requirement for the pointwise criterion;
- `ConstitutiveComparisonSet` freezes the Borel comparison set B₁, its inclusion
  B₁ ⊆ B₀, and distinct baseline path laws on B₁;
- `IsStrategicallyConstitutive` requires the declared property to change at every
  comparison state under an admissible strategic intervention;
- `constitutiveIntervention_world_eq` exposes the already-proved hold-P-fixed
  guarantee at the constitution layer;
- `IsGeneralizedPermanssonRegimeRelative` records Exact GR plus constitution under
  one frozen constitutive protocol;
- `IsGeneralizedPermanssonRegime` is the family form: Exact GR plus existence of at
  least one admissible predeclared strategic intervention that is constitutive;
- `generalizedPR_world_fixed_witness` extracts a constitutive witness together with
  the theorem that its world-transition kernel equals the baseline P.

The diagnostic intervened model is not required to remain a GR or to satisfy an
equilibrium condition.

## Seventh proof milestone — quantitative constitution and robustness

The Section-5.4.1 quantitative layer is now formalized on top of the pointwise
constitution semantics without changing the GR/PR definitions themselves:

- `constitutiveEffect` is the metric-valued pointwise gap Δ_{ψ,J}(y);
- `constitutiveMargin` is the infimum κ_{ψ,J}(B₁) over the frozen comparison set;
- `strategicallyConstitutive_iff_effect_pos` identifies pointwise constitution with
  strictly positive pointwise effects;
- `IsUniformlyStrategicallyConstitutive` and
  `uniformlyConstitutive_iff_margin_pos` implement the positive uniform-margin
  strengthening from equation (16);
- `uniformlyConstitutive_implies_constitutive` proves the quantitative subclass
  implies the generalized pointwise notion, without asserting the converse;
- `constitutiveEffect_perturbation_abs_le` and
  `constitutiveMargin_perturbation_abs_le` formalize the two-sided perturbation
  bounds of Proposition 5.2;
- `perturbedConstitutiveMargin_ge` exposes the lower-bound form
  κ̃ ≥ κ - ε₀ - εJ;
- `robustUniformConstitution` formalizes Corollary 5.3: if the true margin dominates
  the total output-error envelope, the perturbed margin remains positive;
- `IsUniformGeneralizedPermanssonRegime` is the quantitative PR subclass, and
  `uniformGeneralizedPR_implies_generalizedPR` certifies its inclusion in the
  generalized PR class;
- `robustUniformPRCertificate` preserves the baseline Exact-GR certificate together
  with positivity of the perturbed constitutive margin, while deliberately not
  claiming that the approximate profile itself is a new GR.

Proposition 5.4's finite-horizon kernel-to-path total-variation envelope remains OPEN.
That result should be formalized as a later probability-theory layer supplying concrete
error bounds to Proposition 5.2 rather than being conflated with the abstract
output-perturbation theorem.

The next main dependency boundary remains intervention-family signatures/equivalence;
the finite-horizon TV envelope can be developed as a parallel quantitative support layer.
Quotients, EGR compatibility, grounded confirmatory refinements, and QSDs remain later
layers.
