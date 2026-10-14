# Lane C9 — Certified finite-menu strategic constitution synthesis

**PR:** [#60](https://github.com/HMarcusWH/PermanssonLean/pull/60)
**Specification:** PR60_C9_Certified_Finite_Menu_Strategic_Constitution_Spec_v1.1_AUDITED (2026-10-13)
**Parent:** merged C8 `main@6c5a1c29bb05702eddc4634e51153643445be569` (all four original post-merge workflows green)
**STATUS: MERGED, final-head verified.** Final source head
`f474be8a66d0227459e701911441ec2549fd255e`; exact-head
[Research Lean #38469985022](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38469985022)
passed **317/317** exact-rational regressions and **3,078** transitive
declarations within the three permitted axioms, with **266** direct imports,
D0-F golden and source firewall. The other three final-head workflows passed
(Original Lean, executable verification, Ubuntu+Windows application contract).
PR #60 merged to `main@b4989fc4fc633601197cdfa733fbce3f5c9ea2c8`.
Superseded draft/checkpoint descriptions below document *historical development*,
not the current state. C9 did **not** supply C10's executable infinite-path
absorption and original-margin evaluator; that is a separate research task.
CI and code review do not constitute independent mathematical peer review.

## Mathematical object and exact hypotheses

Fix a genuinely typed `M : StrategicWorldModel S X A`, ORIGINAL Boolean regime `spec`, reference measure `m`, original intervention family `F`, valid nonempty original `B₁ : ConstitutiveComparisonSet M spec`, and D0 `FrozenMenu M F I` with `indices.Nonempty`. Fix the SAME predeclared eventual-true descriptor path property for baseline and every candidate. Require the **literal** equality `spec.convergenceMode = ConvergenceMode.almostSureWeak ... Bool`.

For each i, let `Jᵢ := menu.choice i`, `Lᵢ := Jᵢ.intervention.apply.inducedKernel` and define:

- `Eligible(i) := ∀ y∈B₁.states, OpposingClassReachable Lᵢ spec.descriptor spec.target y`
- `κ(i) := constitutiveMargin M spec F (eventuallyObservedProperty spec.descriptor true) B₁ Jᵢ`
- `PR(i) := IsUniformGeneralizedPermanssonRegimeRelative M spec m F ... B₁ Jᵢ` — *the original predicate*, not a local approximation
- `I₊ := menu.indices.filter Eligible`, classically noncomputable for general real Markov kernels

**C9-A:** `PR(i) ↔ IsExactGeneratedRegime M spec m ∧ Eligible(i)`. This theorem uses the literal mode but does NOT add an Exact-GR premise, because it preserves baseline status as a conjunct.

**C9-B:** With separately proved original `hGR : IsExactGeneratedRegime M spec m`, `0 < κ(i) ↔ Eligible(i)` and `κ(i)=0 ↔ ¬Eligible(i)`. Without `hGR` these are false in general. A missing GR proof is NOT `¬ExactGR`.

**C9-C:** `(∃ i∈menu.indices, PR(i)) ↔ IsExactGeneratedRegime M spec m ∧ I₊.Nonempty`. Under `hGR`, `I₊=∅` iff all listed margins are zero, iff no listed intervention is PR. The negative certificate addresses the declared **finite menu only** and does not refute family-level uniform PR. A positive listed member *does* imply original family-level PR.

**C9-D:** Every nonempty declared finite menu admits a mathematical maximum of the *actual real-valued original margin*. Under `hGR`, `hmode` and nonempty eligible subset there exists a listed eligible member with `κ>0` that dominates **all listed margins**, including ineligible zeros. Existence may use classical choice; not an executable argmax.

**C9-E:** A real probability-event constitutive effect, and thus the original `B₁` margin, is at most one even without Exact GR. Therefore C6's previously formal-proved full disruption with margin one globally maximizes any finite menu containing it. No formal exact 1/2-versus-1/1000 quantitative ordering is claimed for C8 half/tiny from their support alone.

**C9-F:** For D0's specially constructed `Unit × Fin n` rational model, strict positive entry `L.entry x z > 0` iff the *genuine typed intervention's* singleton mass is positive. Actual graph-reachable paths transport through the D0 `decode/encode` equivalence. To screen the original protocol also require descriptor equality on ALL encoded states, unchanged `spec.target`, and representation of ALL original `B₁` starts by a rational `BR`. Only for nonempty states can the full C8 recurrence statements be invoked. This adapter does **not** certify arbitrary external models, executable BSCC enumeration, or numerical infinite-horizon absorption computation.

## New source modules

1. `PermanssonResearch/ReverseSolver/FrozenConstitutiveMenu.lean`: genuine member choices, support screen, filtered finite set, actual original margin, and nonnegativity
2. `.../MenuConstitutionClassification.lean`: original PR ↔ ExactGR + eligibility, positive margin, zero margin, explicit negative-baseline proof gate
3. `.../MenuFeasibilityCertificates.lean`: menu-level existence, scope-limited rejection, one-way original family-level promotion
4. `.../MenuMarginOptimization.lean`: original actual margin argmax, eligible global maximizer, probability-event upper bound ≤1, equal-support qualitative invariance
5. `.../RationalTypedSupportBridge.lean`: D0 typed kernel strict-positive-edge and graph-path transport, frozen descriptor and comparison-set representation
6. `.../ExactSixStateC9MenuWitness.lean`: actual typed two-member (C8 half/tiny) and three-member (C6 full, C8 half, C8 tiny) menus, formal margin-one maximum, separate **identity-only** zero-margin/empty-eligible menu, one-row typed response proven positive from u but not a0, exhaustive listed-only negative identity/one-row menu, and explicitly fixed P/U in the constructed menus

All six must appear as direct imports in the separate `PermanssonResearch.lean` root. Old `PermanssonLean/`, C1–C8 .lean, application standard, paper, compiler, manifest, CI workflows and historical freeze evidence are strictly unchanged.

## Independent adversarial suite

`verification/research/test_lane_c9_constitutive_menu.py` adds **50** exact-Fraction tests to the inherited **267**, for an intended **317** total. It is independently recomputed from C6's exact rational Markov absorbing-class equations; it does NOT invoke a noncomputable Lean maximizer as executable code. Cases: duplicate vs distinct menu indices, invalid/empty menu, baseline proof absent/refuted/verified, nonliteral mode, all/one/many/no eligible members, incomplete B₁, bad/good periodic classes, transient false labels, tiny exact positive edges, same support/different magnitude, original six-state full margin one, D0 finite one-step hitting vs C9 eventual-event margin ranking reversal, unchanged alpha/P/U construction constraints, and family-level exclusion counterexample.

**The user's v1.1 audit notes that only C6 full disruption's exact margin one was already a Lean theorem.** C8 half/tiny 1/2 and 1/1000 are independent exact-rational test values until separately formalized numerically.

## Audited v1.1 witness-completeness follow-on

A source audit against the attached v1.1 implementation specification
found that the earlier fully green C9 checkpoint lacked a *separately
named* single-index identity-only menu and an explicit proof that
one-row response is positive at frozen u while absent at frozen a0.
Commit `4e1c5f4622e6c9e5ac1406a7d1382a0f3b0ef60f`
adds `identityOnlyMenu`, `identityOnlyMenu_margin_zero`,
`identityOnlyMenu_eligible_empty`,
`identityOnlyMenu_all_listed_not_PR`,
`identityOnlyMenu_not_family_obstruction`,
`oneRow_bad_u`, `oneRow_opposing_from_u`,
`oneRow_partial_not_uniform`,
and P/U preservation for the two-member, identity-only and
two-candidate negative menus. All the theorem statements still use
the **ORIGINAL** exact GR, Boolean descriptor, original `B₁` and
untouched PR predicate. They do NOT claim support fixes numerical
half/tiny margins, or that a negative finite menu refutes family PR.
Lean elaboration and permitted-axiom checks on the follow-on head
are separate release gates.

The C9 rational adapter remains a *limited* exact one-step/
reachability and frozen-protocol representation bridge, not a
complete executable graph/BSCC/absorption-value solver. In the
Python reference suite, malformed matrix rejection is not a test
that arbitrary external models are represented by the constructed
D0 strategic-world factorization; that limitation is enforced
by the Lean constructor/theorem types and kept outside C9 execution.

## Proof and release firewall

- No new GR/PR predicates, changed comparison starts or descriptor, unproven Exact-GR assumption inference, generalized U preservation, floating-point cutoffs, custom axiom, `sorry`, `admit`, unsafe opaque certificate, hidden implicit variable or semantic target replacement
- `set_option autoImplicit false` in every new C9 Lean file; no general external model realization assertion
- Unknown baseline certification has provenance/status `BASELINE_UNVERIFIED`, NOT false Exact GR; do not treat classical case splits as a verified runtime status engine
- Executor/absorbing-class/margin-value solver with independently certified rational algorithm belongs to C10, not this mathematical C9 layer
- Three-axiom transitive audit only `propext`, `Classical.choice`, `Quot.sound`
- Final head AND exact GitHub synthetic merge: full research Lean, ≥317 exact-rational regressions, root-import coverage, D0 golden check, source firewall, Original Lean, Executable verification and Ubuntu/Windows Application contract all green
- All Codex source/hypothesis findings resolved, explicit verified release ledger, author-controlled PR merge; no empirical/causal identification or independent scholarly peer review is asserted

## Verified mathematical-source checkpoint (pre-documentation HEAD)

- Source commit: `88fc674f25b5767e8bd5d3639abc61549de90de0`; GitHub synthetic merge: `2700df89978c710894fe596f5b4864ff304434c1`
- [Research Lean #38452924510](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38452924510): compiled all six C9 modules, **3,062 declarations** transitive-axiom audited within `propext`, `Classical.choice`, `Quot.sound`; **317/317** exact-rational regressions, **266** direct imports, default build, independently regenerated D0-F golden values, source placeholder/axiom firewall all passed
- [Original Lean #38452924501](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38452924501): passed
- [Executable verification #38452924944](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38452924944): passed
- [Application contract #38452924728](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38452924728): passed on both Ubuntu and Windows
- `ExactSixStateC9MenuWitness.lean` now includes separate genuine **two-index** half/tiny menu, original PR and identical support proof; **three-index** full/half/tiny menu with verified full-disruption margin-one global optimum; typed identity/one-row negative menu, and explicit proof that negative listed-menu status coexists with positive family-level PR
- `MenuMarginOptimization.lean` explicitly transports original qualitative PR status between two menu members with identical support, but NEVER numerical margin equality
- `RationalTypedSupportBridge.lean` proves exact positive rational-edge iff genuine D0 typed edge, finite graph reachability, descriptor equality and frozen `B₁` quantifier representation. **No complete decidable rational BSCC/absorption algorithm or numerical executable C9 optimizer is proved. That is C10's scope**, as permitted by v1.1's minimum adapter contract

This paragraph describes the historical C9 source checkpoint. The final verified C9 head and subsequent main merge are recorded in the updated status at the top. The mathematical scope and absence of external-model identification remain unchanged. Do not confuse `BASELINE_UNVERIFIED` with a mathematical `¬ExactGR`.

**Final-head release gate:** any commit after the original successful source checkpoint, including the v1.1 witness-closure and documentation commits, must pass the complete *new* exact-head/synthetic-merge workflows, regressions, axiom audit and review; record those runs in the PR discussion. This document alone does not authorize merge.
