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
| 9 | Intervention-family signatures / representation equivalence | `FrozenStrategicInterventionFamily`, `InterventionKernelSignature`, `exactGR_iff_of_inducedKernel_eq`, `frozenFamilyPR_iff_of_signature_match` | PROVED |
| 9a | Factorization non-identification (Thm. 7.2) | `factorization_nonidentification` | PROVED |
| 9b | Constitutive non-invariance under baseline equivalence (Thm. 7.3) | `constitutive_noninvariance_under_baseline_equivalence`, `interventionB_constitutiveMargin_eq_one` | PROVED |
| 9c | Nuisance-padding exclusion (Prop. 7.5) | `nuisancePadding_grounded_gap_eq`, `nuisancePadding_cannot_create_grounded_change` | PROVED |
| 10 | Type-respecting intervention-compatible quotient preservation | `TypeRespectingStateCompression`, `KernelIntertwines`, `pathLaw_map_eq_of_kernelIntertwines`, `exactGR_iff_of_quotient`, `quotient_frozenFamilyPR_iff` | PROVED |
| 11 | Paper-I EGR → GR embedding / conservative PR recovery | `PaperISelectedModel`, `embeddedModel`, `embedded_unit_kernelIntertwines`, `paperIEGR_iff_embeddedExactGR`, `paperIPermansson_iff_embeddedRelativePR`, `paperIUniformPermansson_iff_embeddedRelativePR` | PROVED |
| 11b | Grounded confirmatory PR / representation / quotient / world-path EGR transport | `GroundedRelevanceMap`, `IsGroundedPropertyRelative`, `IsGroundedConfirmatoryPermanssonRegimeRelative`, `groundedFrozenFamilyPR_iff_of_signature_match`, `quotient_groundedFrozenFamilyPR_iff`, `paperIGroundedPermansson_iff_embeddedGroundedConfirmatoryPR` | PROVED |
| 11c | Recorded-action decode / action-sensitive conservative PR recovery | `PaperIDecodedPath`, `recordedDecode`, `recordedPathProbability`, `transportRecordedProperty`, `paperIRecordedPermansson_iff_embeddedRelativePR`, `worldActionRecordRelevanceMap`, `paperIRecordedGroundedPermansson_iff_embeddedGroundedConfirmatoryPR` | PROVED |
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

## Eighth proof milestone — intervention-family signatures and representation equivalence

The Section-7 representation layer now freezes a concrete declared intervention family
on top of the typed admissibility grammar and formalizes intervention-compatible
equivalence without widening the claim beyond that family:

- `FrozenStrategicInterventionFamily` stores an explicit nonempty, label-indexed family
  of admissible strategic interventions;
- `FrozenFamilyMatching` fixes a cross-model label equivalence and requires preservation
  of the declared intervention target;
- `InterventionKernelSignature` implements equation (18a): the baseline induced kernel
  together with all post-intervention induced kernels in the frozen family;
- `InterventionCompatibleFamilyEquivalence` bundles target-preserving matching with
  equality of those signatures;
- `pathLaw_eq_of_inducedKernel_eq`, `pathProbability_eq_of_inducedKernel_eq`, and
  `exactGR_iff_of_inducedKernel_eq` formalize the baseline representation-invariance
  bridge, including Proposition 7.1 for Exact-GR status;
- `ConstitutiveComparisonSet.transport` carries the same frozen B₁ state set across
  equal induced kernels while transporting only its baseline path-law certificate;
- `strategicallyConstitutive_iff_of_kernel_eq`,
  `constitutiveEffect_eq_of_kernel_eq`,
  `constitutiveMargin_eq_of_kernel_eq`, and
  `uniformlyConstitutive_iff_of_kernel_eq` formalize matched-intervention preservation
  of pointwise and quantitative constitution;
- `HasConstitutiveWitnessInFrozenFamily` and
  `NoConstitutiveWitnessInFrozenFamily` give positive and protocol-scoped negative
  family classifications without making claims about omitted admissible interventions;
- `hasConstitutiveWitness_iff_of_familyEquivalence`,
  `noConstitutiveWitness_iff_of_familyEquivalence`, and
  `frozenFamilyPR_iff_of_signature_match` lift the matched-intervention result to the
  whole frozen family, corresponding to Proposition 7.4a;
- the uniform-margin family analogues are also preserved under signature matching.

The Section-7 negative and representation-safety claims are also machine-checked:

- `factorization_nonidentification` formalizes Theorem 7.2 by an explicit finite typed
  witness with equal baseline induced kernels but distinct strategic generators and
  world-transition kernels;
- `constitutive_noninvariance_under_baseline_equivalence` formalizes Theorem 7.3 at
  the predicate level: the witness models share the same baseline kernel and Exact-GR
  status, yet the same typed action-selection replacement is non-constitutive in one
  representation and uniformly constitutive in the other;
- `interventionB_constitutiveMargin_eq_one` computes the deterministic witness's exact
  uniform constitutive margin as 1.  This is an equivalent existential witness to the
  manuscript's Bernoulli illustration, not a claim that the manuscript's 1/2 gap was
  rederived from the same finite construction;
- `nuisancePadding_grounded_gap_eq` and
  `nuisancePadding_cannot_create_grounded_change` formalize Proposition 7.5's
  relevance-grounded nuisance-padding exclusion.

Grounded relevance-map preservation was not part of this milestone itself, but is now
formalized later in Layer 11b.  This milestone still does not identify frozen-family
equivalence with equivalence over every admissible intervention in `InterventionFamily`.

The next dependency boundary is the type-respecting quotient preservation theorem
(Theorem 7.4b). Proposition 5.4's finite-horizon TV envelope remains an independent
open quantitative-support lane, with EGR compatibility, grounded confirmatory
refinements, and QSDs still later.


## Ninth proof milestone — type-respecting intervention-compatible quotients

The quotient layer formalizes the general/uniform core of Theorem 7.4b with the
strategic/world type split preserved explicitly.

- `TypeRespectingStateCompression` stores separate measurable surjections
  (q_S:S\to\bar S) and (q_X:X\to\bar X), inducing the joint-state map
  (q(s,x)=(q_S(s),q_X(x)));
- `KernelIntertwines` is the exact commuting-square condition
  `K.map q = Kbar.comap q`, with a setwise preimage theorem matching the paper;
- `InterventionCompatibleKernelQuotient` requires that the baseline kernel and every
  frozen strategic intervention kernel commute with the same state compression;
- `pathLaw_map_eq_of_kernelIntertwines` proves that coordinatewise path pushforward
  of the canonical Ionescu--Tulcea law equals the canonical compressed path law;
- `QuotientCompatibleRegimeSpecifications` freezes region/basin preimages,
  descriptor factorization, and target-law equality;
- `ConvergenceModesCompatibleUnderCompression` makes convergence-mode naturality
  explicit. This is necessary because the repository permits arbitrary custom
  convergence predicates, which cannot be assumed quotient invariant automatically;
- `HasAdmissibleInitialLifts` records the paper's lift condition for compressed
  admissible initial laws;
- `exactGR_iff_of_quotient` preserves Exact-GR status while taking Assumption 4.1
  independently on both representations, matching the paper's nontriviality caveat;
- `PropertyFactorsThroughCompression` and
  `QuotientCompatibleComparisonSets` encode the frozen property/comparison-set
  compatibility needed for constitutive transport;
- `strategicallyConstitutive_iff_under_quotient`,
  `constitutiveEffect_eq_under_quotient`,
  `constitutiveMargin_eq_under_quotient`, and
  `uniformlyConstitutive_iff_under_quotient` prove exact preservation of the
  pointwise and quantitative constitutive tests;
- `InterventionCompatibleStateQuotient` bundles the full semantic certificate;
- `quotient_frozenFamilyPR_iff` and `quotient_frozenFamilyUniformPR_iff`
  provide the family-level generalized and uniform PR preservation results.

The theorem remains deliberately scoped to the explicitly frozen intervention family.
Grounded (g)-relative confirmatory preservation is now formalized later in Layer 11b.
Proposition 5.4's finite-horizon kernel-to-path TV envelope remains an independent open
quantitative-support lane.

The next main dependency boundary is the EGR-to-GR embedding/compatibility layer,
unless the grounded confirmatory or finite-horizon TV support lanes are prioritized first.


## Tenth proof milestone — Paper-I EGR embedding and conservative recovery

Layer 11 is now machine-checked for the semantic core of Section 6.

- `PaperISelectedModel` freezes the selected measurable pure stationary Paper-I policy
  and the original world-transition kernel after upstream equilibrium certification;
- `equilibriumKernel` is the Paper-I post-equilibrium kernel
  (P^{\pi^*}(D\mid x)=P(D\mid x,\pi^*(x)));
- `PaperIStrategicState A = \mathbb N \times (\mathbf 1 \sqcup A)` implements the
  canonical clock/action-record state (S_E=\mathbb N_0\times(A\cup\{\bot\}));
- `embeddedModel` implements the deterministic selected-policy action kernel,
  recording update, and world kernel that ignores the bookkeeping coordinate;
- `recordingCompression` and `embedded_unit_kernelIntertwines` prove the one-step
  projection identity behind equation (18);
- `embedded_pathProbability_push_unit` and
  `embedded_worldPathLaw_eq_paperI` lift that identity to canonical path laws;
- `embeddedSpec` transports the region, initial basin, descriptor, target,
  convergence semantics, reference measure, and admissible initial laws;
- `paperI_exactInvariant_iff_embedded`,
  `paperI_limiting_iff_embedded_worldMarginal`, and
  `paperI_nontriviality_iff_embedded_assumption41` prove preservation of the
  three substantive Exact-GR clauses;
- `paperIEGR_iff_embeddedExactGR` is the machine-checked semantic core of
  Theorem 6.1;
- `PaperIPolicyIntervention` transports a measurable date/state rule
  \(\rho_t^J(x)\) into a typed action-selection intervention while holding both
  the recording update and world-transition kernel fixed;
- `transported_baselinePropertyValue_eq` and
  `transported_intervenedPropertyValue_eq` preserve Paper-I world-path property
  values at every comparison state;
- `paperIConstitutive_iff_embedded` and
  `paperIPermansson_iff_embeddedRelativePR` give the pointwise conservative
  Theorem-6.2 core;
- `transported_constitutiveEffect_eq`,
  `paperIConstitutiveMargin_eq_embedded`,
  `paperIUniformlyConstitutive_iff_embedded`, and
  `paperIUniformPermansson_iff_embeddedRelativePR` prove exact preservation of
  constitutive effects and the uniform-margin subclass.

The Layer-11 claim is deliberately scoped to the world-path protocol branch of
Theorem 6.2 and to a selected measurable pure stationary Paper-I equilibrium supplied
as an upstream certificate. It does not claim a new MPE existence theorem.

Two Section-6 refinements remain separate rather than silently folded into Layer 11:
the explicit recorded-action decode branch for Paper-I properties that depend on
realized actions, and grounded (g)-relative confirmatory transport. Those are tracked
as Layer 11b. Proposition 5.4's finite-horizon TV envelope, BL metrization, and QSD
support also remain open independent lanes.

The grounded confirmatory layer is formalized in the next milestone.  The remaining
Section-6 refinement is explicit recorded-action decoding; Layer 8b and Layer 4a
remain independent quantitative/topological support work.


## Eleventh proof milestone — grounded confirmatory semantics and preservation

The grounded confirmatory subclass from Sections 5.2, 5.4, 6, and 7 is now
machine-checked without strengthening the broad generalized-PR definition.

- `GroundedRelevanceMap` freezes a measurable observation map (g:Y\to G), a
  measurable regime region (B_G\subseteq G), and a measurable descriptor
  (h_G:G\to H), with exact factorization
  (B=g^{-1}(B_G)) and (h=h_G\circ g);
- `GroundedRelevanceMap.pathMap` and `pushPath` implement the coordinatewise
  path observation (g^\infty) and its push-forward on path probability laws;
- `IsGroundedPropertyRelative` is source-faithful: a single frozen
  `ψ_G` must represent `ψ` on every admissible baseline and intervened law
  relevant to the declared protocol, rather than on every abstract path law;
- `GloballyFactorsThroughRelevanceMap` is exposed only as a sufficient stronger
  constructor, and `grounded_propertyValues` recovers the same `ψ_G` for both
  point-initialized baseline and intervention values on (B_1);
- `IsGroundedConfirmatoryPermanssonRegimeRelative` formalizes the confirmatory
  (\mathrm{PR}_g) subclass as confirmatory GR + strategic constitution +
  grounded property semantics, while `IsGroundedPermanssonRegimeRelative`
  keeps the broader grounded/non-confirmatory notion separate;
- `IsGroundedConfirmatoryUniformPermanssonRegimeRelative` reuses the existing
  constitutive-margin machinery rather than defining another quantitative object;
- `descriptorNondegenerate_iff_of_inducedKernel_eq`,
  `confirmatoryGR_iff_of_inducedKernel_eq`,
  `groundedPropertyRelative_iff_of_kernel_eq`, and the grounded relative-PR
  equivalence theorems close the grounded part of representation invariance;
- `GroundedFrozenFamilyProperty` requires one predeclared `ψ_G` across the
  complete frozen intervention family; `groundedFrozenFamilyPR_iff_of_signature_match`
  and its uniform analogue preserve the grounded family classification under
  intervention-signature equivalence;
- `RelevanceMapFactorsThroughCompression` formalizes the quotient condition
  (g=\bar g\circ q); its path/push-forward lemmas combine with kernel
  intertwining to prove descriptor-nondegeneracy, confirmatory-GR, grounded-family,
  and grounded-uniform-family preservation under the type-respecting quotient;
- `worldRelevanceMap` is the canonical relevance map for the world-path branch
  of the Paper-I embedding, and `transportProperty_globallyGrounded` proves that
  the transported property factors through it with the original Paper-I property
  as `ψ_G`;
- `paperIConfirmatoryEGR_iff_embeddedConfirmatoryGR`,
  `paperIGroundedPermansson_iff_embeddedGroundedConfirmatoryPR`, and
  `paperIGroundedUniformPermansson_iff_embeddedGroundedUniformPR` close the
  grounded world-path branch of conservative Paper-I recovery.

The grounded layer remains intentionally separate from the broad
`IsGeneralizedPermanssonRegime`; no relevance restriction has been retrofitted
onto the general class.

The explicit recorded-action decode branch is formalized in the next milestone. Proposition 5.4's finite-horizon kernel-to-path TV envelope, Proposition 4.1a's Polish/BL metrization result, and the optional QSD subclass remain independent open lanes.


## Twelfth proof milestone — recorded-action decoding and action-sensitive Paper-I recovery

The remaining Section-6 action-sensitive transport branch is now machine-checked on
top of the canonical recording embedding.

- `PaperIDecodedPath X A = (ℕ → X) × (ℕ → A)` is the decoded execution space;
- `decodeActionRecord` supplies the arbitrary total extension allowed by Section 6.2
  on the bottom/off-support action-record branch, while `decodeActionRecord_inr`
  recovers every actually recorded action value exactly;
- `recordedActionPath` implements (a_t=\bar a_{t+1}), and
  `recordedDecode` is the measurable decoding map (D) from embedded state paths
  to world/action execution paths;
- `recordingUpdateMap_records_action` and
  `recordingUpdateMap_advances_clock` expose the deterministic structural
  identities of (U^{\mathrm{rec}});
- `recordedPathProbability` and
  `recordedCounterfactualPathProbability` are the baseline and transported-policy
  (D_\#)-execution laws;
- `recordedPathProbability_worldMarginal` and
  `recordedCounterfactualPathProbability_worldMarginal` prove that their first
  marginals recover the already-verified Paper-I baseline and counterfactual world
  laws;
- `PaperIRecordedPropertyMap` and `transportRecordedProperty` implement the
  action-sensitive branch of Theorem 6.2, where the transported property is evaluated
  on (D_\#\mu);
- `transported_recorded_baselinePropertyValue_eq`,
  `transported_recorded_intervenedPropertyValue_eq`, and
  `paperIRecordedConstitutive_iff_embedded` preserve the pointwise constitutive
  protocol on every state in the frozen comparison set;
- `paperIRecordedPermansson_iff_embeddedRelativePR` gives generalized-PR recovery
  for action-sensitive Paper-I protocols;
- `transported_recorded_constitutiveEffect_eq`,
  `paperIRecordedConstitutiveMargin_eq_embedded`,
  `paperIRecordedUniformlyConstitutive_iff_embedded`, and
  `paperIRecordedUniformPermansson_iff_embeddedRelativePR` preserve the exact
  metric gap and uniform-margin subclass;
- `worldActionRecordRelevanceMap` freezes the sufficient grounded record
  (g_A((t,\bar a),x)=(x,\bar a));
- `decodeRelevantPath` and `recordedDecode_factor_relevancePath` prove that the
  action-sensitive decoder factors through (g_A^\infty) on every path, including
  the total off-support extension;
- `transportRecordedProperty_globallyGrounded` therefore proves global
  (g_A)-grounding of every transported recorded-action property;
- `paperIRecordedGroundedPermansson_iff_embeddedGroundedConfirmatoryPR` and
  `paperIRecordedGroundedUniformPermansson_iff_embeddedGroundedUniformPR` close
  the grounded pointwise and uniform branches.

The decoder deliberately uses a chosen fallback action on the bottom/off-support branch.
Section 6.2 permits an arbitrary extension there, so this is a totalization convention,
not an additional behavioral hypothesis.  The proved transport claims concern the
canonical (D_\#)-property protocol and its exact world marginal; they do not add a
separate theorem identifying malformed/off-support decoded action paths with an
independently reconstructed policy-action process.

With both the world-only and recorded-action branches checked, the Section-6
conservative transport architecture is closed.  The remaining main paper-support lanes
are Proposition 5.4's finite-horizon TV envelope, Proposition 4.1a's Polish/BL
metrization theorem, and the optional QSD subclass.
