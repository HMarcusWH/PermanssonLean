# Proposed PR #61 — Lane C10
## Executable exact-rational absorption and certified constitutive-menu optimization

**Status:** Audited revised implementation specification; not implemented or compiler-verified.  
**Audit basis:** Read exact repository source at `main@b4989fc4fc633601197cdfa733fbce3f5c9ea2c8`, including the original `UniformPermansson`/`ConstitutiveMargin` predicates, C6–C9 numerical/path-law/witness modules, D0 realization and menu modules, Python regressions, and Research Lean workflow.  
**Current baseline:** All four **post-merge PR #60** workflows passed on that exact `main` merge commit. Branch and PR number remain proposals, not created/reserved.

### v1.1 corrections — mandatory implementation decisions

1. **Negative certificates:** an exact **zero original margin** proves a listed member is **not a uniform relative PR without requiring baseline Exact GR**. It rules out the uniform strategic-constitution conjunct directly. C9's full support/margin equivalence requires `hGR` and literal mode, while its existing `PR ↔ (ExactGR ∧ Eligible)` theorem needs only literal mode and already gives the one-way **support-ineligible → not PR** implication without `hGR`. Positive margin alone cannot establish PR without `hGR`.
2. **Input reflection:** `RationalMarkovMatrix n` is a proof-carrying structure, not an untrusted serialized input. Add an explicit checked conversion `RawInput → Except Error CheckedInput` and prove that success actually constructs row-stochastic matrices, nonempty finite menu, exact comparison states, and descriptor labels. The string/JSON parser itself remains outside the formal trust claim unless separately verified.
3. **Computable fixtures:** C8's `halfMatrix`/`tinyMatrix` and C9's `oneRowMatrix` are declared inside `noncomputable section`; a runtime cannot assume these definitions are executable. Reify them as *separate computable rational data* and prove equality of entries/the constructed matrices, while preserving the original theorem source.
4. **B-only witness:** `B_ONLY` exists in Python's C6 fixtures, not as an original named Lean typed witness. Construct a genuine D0 alpha-only `bOnlyJ` and prove its probability/margin statements, or clearly downgrade that one row to Python-only. v1.1 requires constructing it.
5. **Index binding:** D0 `RationalMatrixMenu` stores an ordered `List I` and a total `I → RationalMarkovMatrix n`; C9 `FrozenMenu` stores a `Finset I`. Normalize and bind indices **before** evaluation, preferably to `Fin m`, prove every listed matrix/index corresponds to the genuine typed C9 choice, and preserve declared tie order.
6. **Certificate scope:** separate exact numerical `checkCertificate` soundness from the semantic `hR`/`B₁`/typed-menu transport proofs. A valid matrix or matching digest does not establish a valid original comparison-set or intervention-family correspondence. Distinguish kernel-checked literal receipts from executable output and hash identity checks.
7. **Implementation risk:** full generic BSCC algorithm + total generic rational solver + original margin bridge + verified receipt checker is substantial. Establish a compiler-checked vertical slice for the six-state model early. Do not silently replace totality by Python-only tests or claim that a proposed matrix API has compiled before it does.

**Repository:** `HMarcusWH/PermanssonLean`  
**Inspected base:** `main@b4989fc4fc633601197cdfa733fbce3f5c9ea2c8` — merged PR #60 / C9.  
**C9 final source head:** `f474be8a66d0227459e701911441ec2549fd255e`.  
**Suggested branch:** `research/lane-c10-exact-constitutive-execution`.  
**Suggested title:** `research(C10): executable exact absorption and certified constitutive-menu optimization`.

The PR number is proposed, not reserved. All four post-merge workflows were completed successfully on the inspected main merge. Re-read main and post-merge CI before implementation in case the repository advances; never substitute a PR synthetic-merge run for a different head.

---

## 1. Release objective

Turn C9's mathematical finite-menu optimizer into an actual exact-rational computation, with a Lean proof connecting its output to the **original** constitutive margin on the **actual** typed strategic-world path laws.

For one frozen Boolean descriptor `h`, write

\[
E_h=\{w:\exists N,\;\forall t\geq N,\;h(w_t)=\mathrm{true}\}.
\]

For a rational stochastic matrix `K`, the new evaluator must compute

\[
f_K(x)=\Pr_x^K(E_h)\in\mathbb Q.
\]

For baseline `K₀`, each listed intervention matrix `Kᵢ`, and a finite set `BR` representing **all** states of the original comparison set `B₁`, compute

\[
\Delta_i(x)=|f_{K_0}(x)-f_{K_i}(x)|,
\qquad
\widehat\kappa_i=\min_{x\in BR}\Delta_i(x),
\qquad
\widehat\kappa_* = \max_{i\in I}\widehat\kappa_i.
\]

The central bridge theorem must establish, after the exact rational-to-real cast,

\[
(\widehat\kappa_i:\mathbb R)
=
\operatorname{constitutiveMargin}(M,\mathrm{spec},F,
\operatorname{eventuallyObservedProperty}(\mathrm{spec.descriptor},\mathrm{true}),B_1,J_i).
\]

Then certify a selected listed member attaining the global maximum over **every** listed candidate, not merely over a prefiltered positive subset.

The numerical equality does **not** need an Exact-GR hypothesis. Promotion to the original uniform relative PR predicate **does** require an independently supplied original Exact-GR proof. C9 support-screen equivalence additionally retains its literal `almostSureWeak` hypothesis.

### Non-negotiable distinctions

- This is the infinite-path eventually-always-true event, not finite-horizon hitting, eventual occupation frequency, or an arbitrary temporal-logic property.
- The baseline and every intervention get their own support graph, bottom classes, and numerical absorption weights.
- One intervention is fixed for the whole path and across the entire comparison set. Optimize `max_i min_x Δᵢ(x)`, never `min_x max_i Δᵢ(x)`.
- Optimize the declared finite menu, not arbitrary stationary policies, feedback policies, history policies, or the entire admissible intervention family.
- A computed positive margin is not by itself an Exact GR, a grounded confirmatory PR, or an empirical causal certificate.
- A computed **zero** original margin *does* refute original uniform relative PR for that member, without needing to disprove or certify Exact GR. This is stronger evidence than a support-only negative result.

## 2. Existing code that must be reused

The inspected source provides these interfaces; the proposed module names later in this specification are new.

| Existing source | Reusable interface / boundary |
|---|---|
| `ReverseSolver/RationalKernel.lean` | `RationalMarkovMatrix` has `entry`, `entry_nonneg`, `row_sum_one` proof fields, requiring a real validation/reflection boundary for serialized data. `rationalHittingValue` has a different finite-horizon objective. |
| `ReverseSolver/CertifiedSelection.lean`, `FrozenMenu.lean`, `TypedMenuCertification.lean` | `RationalMatrixMenu` uses an ordered list and total matrix mapping; original `FrozenMenu` uses a nonempty finite index set. D0 currently optimizes a **different finite-horizon hitting objective**. |
| `ReverseSolver/FiniteStrategicRealization.lean` | `realizedModel`, `rationalStrategicIntervention`, exact induced-kernel atom/cylinder equalities; the constructed family keeps P and U fixed. |
| `MultipleLimit/FiniteObservedEventMass.lean` | Almost-sure equivalence of eventual truth with selection of an all-true recurrent class. |
| `MultipleLimit/TypedObservedEventConstitution.lean` | `pointGoodMass`, baseline/intervened property identities, `effect_eq_abs_goodMass_difference`. |
| `MultipleLimit/FiniteObservedUniformMargin.lean`, original `Regime/ConstitutiveMargin.lean`, `Regime/UniformPermansson.lean` | Existing original finite-margin and PR predicates. Zero original margin refutes uniform PR *without* requiring hGR. |
| `ReverseSolver/MenuMarginOptimization.lean` | Original real-margin maximum, global eligible maximum, event-margin upper bound one. These choices may be noncomputable. |
| `ReverseSolver/RationalTypedSupportBridge.lean` | Exact strict-positive edge and reachability transport, global descriptor transport, complete B₁ correspondence. Not yet a numerical absorption bridge. |
| `verification/research/test_lane_c6_typed_response.py` | Existing exact Gauss–Jordan/class-absorption reference. Its `observed_limit_probability` **rejects mixed-label recurrent classes**, so it cannot be reused unchanged to validate C10's general eventual-true evaluator. `B_ONLY` is a Python fixture here. |
| `MultipleLimit/ExactSixStateC8SupportWitness.lean`, `ReverseSolver/ExactSixStateC9MenuWitness.lean` | Half/tiny/one-row/menus are already *proved typed witnesses*, but several rational definitions are inside `noncomputable section`; runtime data require independently computable reifications and equality proofs. |
| `verification/research/test_lane_c9_constitutive_menu.py` | Existing scope/status/margin adversaries. Its baseline-status string is explicitly a test oracle, not real evidence. |

Do not add an `exact_values` field that assumes the numerical-to-path-law equality which C10 is supposed to prove.

## 3. Frozen input contract

### 3.1 Numerical layer

A valid numerical instance contains:

- `n > 0` and certified `RationalMarkovMatrix n` data for the baseline and every listed candidate;
- one Boolean label for **every** state;
- a finite, nonempty comparison-state set;
- a nonempty finite menu with a frozen ordering of its distinct indices;
- exact rational entries, never machine floating-point probabilities.

The low-level probability evaluator must work for `n=1`, and `n=0` must not be admitted as a valid stochastic query despite the vacuous `RationalMarkovMatrix 0` proof fields. The original PR adapter must separately require a genuine original `ConstitutiveComparisonSet` with `pathLawNontrivial`, `states_subset_basin`, and measurable states; a one-state or singleton-comparison numerical calculation does not satisfy that original gate.

Normalize repeated identical index assignments by keeping their first occurrence, or reject them under an explicitly stricter input format. Never silently accept a conflicting assignment to one index. Distinct indices with identical matrices remain distinct listed interventions. The default specification is first-occurrence normalization, consistent with the existing C9 reference tests.

For a dynamic external menu, freeze the normalized list and explicitly assign each item an internal `Fin m` index. Prove that every index corresponds to exactly the listed rational matrix and **the original C9 typed intervention member**; do not treat the ordered numeric list as identical to `FrozenMenu.indices : Finset I` by notation alone. Use lowest numeric state index to break ties among worst-case starts and the first normalized menu index to break ties among maximizing interventions.

### 3.2 Typed semantic layer

The first release uses the existing D0 constructive realization:

`S = Unit`, `X = Fin n`, `A = Fin n`, alpha selects the next-state label, P copies it, U retains Unit.

Require exact transport of the global descriptor and of all original comparison states:

\[
h_Y(\operatorname{decode}x)=h_R(x)\quad\forall x,
\qquad
x\in BR\iff\operatorname{decode}x\in B_1.\mathrm{states}.
\]

Use the actual D0 constructed typed menu, or a proved member-by-member identification with it. Preserve the original region, basin, target law, reference measure, intervention family, and convergence mode in the semantic wrapper. P/U preservation is claimed for this constructed alpha-only family, not for every general strategic intervention.

An externally supplied matrix is not identified with an external strategic-world model merely because it is square, stochastic, or has the same support. Arbitrary external-model adapters are outside this release.

### 3.3 Checked input and serialization boundary

Define a new *computable* untrusted-data representation, e.g. rectangular arrays of numerator/denominator pairs plus labels, comparison indices, and ordered menu items. Implement `validateInput : RawInput → Except InputError (Σ n : ℕ, CheckedInput n)`, where `CheckedInput n` includes a proof `0 < n`, properly constructed `RationalMarkovMatrix n` baseline/member matrices, the complete label function `Fin n → Bool`, nonempty comparison `Finset (Fin n)`, and normalized nonempty menu. Prove successful validation establishes all these properties and does not silently round/change any rational value.

Define the explicit *external parser boundary*: bytes/JSON → RawInput → checked Lean value. Only the second step is called verified unless the first is separately proved. Reject missing labels, conflicting duplicate indices, noncanonical/zero denominators, invalid dimensions, and non-stochastic rows. The original semantic adapter has further obligations not implied by this numerical structure.

For release fixtures, kernel-checked Lean literals are acceptable even if a standalone verified JSON parser is deferred. This must be reported honestly: a Python CLI plus Lean literal checker is not a verified arbitrary-JSON decoding pipeline.

## 4. C10.1 — Computable strict-support graph and complete bottom classes

Implement an actual finite algorithm over `Fin n` and rational comparisons. Prefer a bounded Boolean transitive-closure algorithm for the first Lean reference implementation; optimized graph algorithms can follow later.

The reachability relation includes length-zero paths. Prove the computed Boolean result equivalent to `Relation.ReflTransGen` of strict positive entries, then compose with C9's genuine typed-edge bridge.

Use mutual reachability to enumerate strongly connected components. A bottom strongly connected component (BSCC) is one with no positive outgoing edge to another component. Use the smallest numeric state as a deterministic computational representative.

Prove completeness, not just soundness of the returned examples:

1. Returned classes are nonempty, pairwise disjoint, strongly connected, and closed.
2. Every bottom communicating class is returned exactly once.
3. Every state reaches some returned bottom class.
4. There is at least one returned bottom class for every nonempty finite stochastic matrix.
5. Returned classes correspond to the existing recurrent-class objects by their **state sets**.

Do not equate the computed minimum representative with an older classical representative without a proof. Their labels may differ while their class sets agree.

No epsilon thresholds, floating spectral tests, assumed acyclicity, or aperiodicity assumptions.

## 5. C10.2 — Exact absorption system and a total reference solver

Let the computed bottom classes be `C₁,…,Cᵣ`, let `R` be their union, and let `T` be the remaining states. For each class compute

\[
H_j(x)=\Pr_x^K(\text{eventually enters }C_j).
\]

Its defining equations are

\[
H_j(x)=\mathbf1_{C_j}(x)\quad(x\in R),
\qquad
H_j(x)=\sum_yK(x,y)H_j(y)\quad(x\in T).
\]

The conventional transient block is `(I-K_TT)H_Tj = b_j`. To avoid special matrix indexing for an empty transient set, an acceptable and recommended full-state encoding is

\[
Q(x,y)=\mathbf1_T(x)K(x,y)\mathbf1_T(y),\qquad A=I-Q,
\]

\[
b_j(x)=
\begin{cases}
\mathbf1_{C_j}(x),&x\in R,\\
\sum_{z\in C_j}K(x,z),&x\in T.
\end{cases}
\]

Then solve `A H_j = b_j`. When every state is recurrent, `A=I`; the same algorithm still works.

**Never invert `I-K` for the full stochastic matrix.** That matrix is generally singular. The full-state encoding above is different: recurrent rows and columns have been removed from Q.

### Proof obligations

Prove uniqueness from the graph, rather than accepting invertibility as an input hypothesis. If a homogeneous solution is nonzero, take a state maximizing its absolute value. The harmonic equation forces extremal values to propagate along positive edges, but some such path reaches a zero-boundary recurrent state, a contradiction.

Use that uniqueness to prove the rational system nonsingular. The first total Lean reference solver may use explicit finite determinant/adjugate arithmetic, **subject to an early Lean 4.34.0 API/compiler spike**; this is a mathematical algorithm design, not an assertion that the following pseudocode is already valid Lean syntax:

`H_j = (det A)⁻¹ • (adjugate A).mulVec b_j`.

Verify that the implementation actually remains computable over finite rational data. A `noncomputable` matrix inverse or an abstract chosen solution is not an executable completion. No polynomial-time claim is attached to this simple reference implementation.

A faster Python Gauss–Jordan producer is acceptable behind the verified checker in Section 9; its implementation is not thereby a Lean-verified Gaussian-elimination algorithm.

Prove for every valid matrix:

- total reference evaluation and exact boundary/harmonic equations;
- `0 ≤ H_j(x) ≤ 1`;
- `Σ_j H_j(x)=1`;
- `H_j(x)>0` iff class `C_j` is reachable from `x`;
- exact equality with the genuine canonical class-entry / selection probability.

Derive the last identity using the native finite Markov path law, the first-step equation, and the already established almost-sure recurrent-class entry. Do not make actual event probabilities another assumed solution certificate.

## 6. C10.3 — Exact eventual-observation values

A bottom class is good precisely when **every** member has label true:

\[
\operatorname{Good}(C_j)\iff\forall z\in C_j,\;h(z)=\mathrm{true}.
\]

Define the executable rational value

\[
\operatorname{eventValue}(K,h,x)=\sum_{j:\operatorname{Good}(C_j)}H_j(x).
\]

Prove its exact equality to `pointGoodMass K h x`, with the correct ENNReal/real/rational bridges, and hence to the canonical probability of `E_h`.

Mixed-label recurrent classes contribute zero to this event, even when their limiting true occupation share is positive. False transient states do not disqualify an eventual-true path. All-true periodic classes contribute their full absorption probability.

The distributional extension for a rational initial law is a finite weighted sum of these point-start values. It does not change the original pointwise B₁ margin or silently replace that minimum by optimization over arbitrary initial mixtures.

## 7. C10.4 — Exact typed probability and original-margin correspondence

For the actual typed baseline and every actual listed intervention, prove the executable event values equal the existing original property outputs. Reuse:

- D0's exact one-step mass/cylinder equations, not only equal support;
- C9's graph and frozen-protocol transport;
- C7's `baselineValue_eq_goodMass` and `intervenedValue_eq_goodMass`;
- `effect_eq_abs_goodMass_difference` and the existing finite-margin interface.

The resulting margin theorem must refer to the unmodified original `constitutiveMargin`. Every comparison state must be included. Descriptor agreement on the baseline basin alone is insufficient, because interventions can reach other states.

Keep two theorem layers:

**Numerical layer, no hGR:** event probabilities, effects, minima, maxima, witnesses, and exact equality to the original margin are correct for the represented typed instance. Furthermore, an exact original **zero margin** refutes `IsUniformlyStrategicallyConstitutive` and hence `IsUniformGeneralizedPermanssonRegimeRelative` for that candidate without `hGR`. This is a direct original-definition theorem, not an application of C9's hGR-conditional support criterion.

**Regime layer:** with the independent original `IsExactGeneratedRegime` proof, a listed member has the original uniform relative PR status iff its exact margin is positive. Under literal C9 `almostSureWeak` mode, also prove agreement with C9's support-eligible indices and opposing-class criterion. Even without `hGR`, C9's unchanged PR iff theorem yields **support-ineligible → not PR** (a one-way conclusion), but never implies a zero numerical margin without `hGR`. A strictly positive computed margin warrants **uniform strategic constitution only** until `hGR` is supplied. An actual proof of `¬ IsExactGeneratedRegime` refutes PR independently of the margin.

Do not require `spec.target=δ_true` globally. A valid mixed observed occupation target can give baseline eventual-true probability zero. Computing both actual probability vectors avoids using an unjustified baseline-extremality shortcut.

## 8. C10.5 — Actual executable finite-menu optimizer

Compute every listed margin. Return:

- every candidate's probability vector and pointwise effect vector;
- its exact margin and the deterministically chosen lowest-index comparison state attaining that minimum;
- the exact global maximum;
- the complete tied-maximizer set;
- one deterministic selected member: the first maximizer in the frozen normalized menu ordering.

Prove membership, minimum attainment, dominance over **all** listed candidates, exact agreement with the original real margin, and preservation of the constructed family's P/U.

When every margin is zero, a nonempty menu still has mathematical maximizers. Return that honest numerical result; separately report that there is no positive-margin candidate. Do not return no optimizer merely because no listed PR exists.

Under hGR and the C9 mode, positive exact margins must match the original support eligibility predicate. Even without hGR, an exact computed zero optimum refutes uniform relative PR for every listed candidate because all original margins are zero (provided the typed correspondence to original `B₁` has been established). In either case it is **listed-menu only**, never a family-wide impossibility theorem.

The selected index need not be invariant under changing the frozen ordering when ties exist. The optimum and tied-index set are invariant under order permutation; state relabeling must preserve values under the proved transported query.

## 9. C10.6 — Proof-carrying execution and input-bound receipts

Implement a **computable Lean certificate checker**, distinct from the producer. It validates the actual normalized and **checked** input, complete bottom-class decomposition, class-absorption arrays, exact boundary/harmonic equations, event sums, all margins, worst-case starts, tied maximizers, and selected index. Its soundness theorem begins with exact `CheckedInput` values, not with unproved claims about input files.

The checker need not rerun matrix inversion. Its soundness uses the proved uniqueness theorem. This permits an independent fast rational producer without trusting its linear algebra.

Required theorems:

- `checkCertificate input receipt = true` implies the exact numerical and typed-semantic conclusions under the explicit adapter premises;
- the actual Lean reference evaluator produces an accepted receipt for **every** valid finite numerical instance;
- the original PR conclusions require the actual original hGR term, not a Boolean flag.

A theorem that merely says some valid receipt exists does not establish totality of the executable evaluator.

### Evidence categories

Keep arithmetic, semantic transport, and baseline evidence separate. A convenient report carries three fields rather than one overloaded certification adjective:

| Layer | Meaning |
|---|---|
| Arithmetic | Candidate, independently rechecked, or Lean-checked for the exact decoded rational input. |
| Typed transport | Constructed D0 family with a checked exact adapter, or unavailable. |
| Baseline | `BASELINE_UNVERIFIED`, an input-bound hGR proof, or an explicit input-bound refutation proof. |

An actual input-bound `hGR` proof is required to **affirm** original uniform PR or to derive `positive original margin ↔ graph support` using C9. The existing C9 `PR(i) ↔ (ExactGR ∧ Eligible(i))` theorem itself only requires literal mode: **support-ineligible → not PR** follows without hGR, but support eligibility alone cannot certify PR. Separately, a proved numerical zero original margin refutes uniform constitution and original uniform relative PR for that listed member **without** `hGR` or a literal-mode hypothesis. Thus an all-zero exact margin menu has a listed-only negative PR theorem without `hGR`; an empty-eligible menu also has a one-way listed-negative theorem when the literal C9 mode holds. The reverse support-emptiness iff no-PR and numeric margin↔support equivalences still require the original hGR gate. None excludes unlisted interventions.

### Serialization boundary

Use exact integer numerator/denominator representations, normalized positive denominators, canonical ordering, and a normalized-input fingerprint. Bind the report to the matrices, descriptor, complete BR, menu ordering, typed realization identifier, source commit, and applicable frozen specification/evidence reference.

A digest supplies identity binding, not a mathematical proof. A CLI option such as `baseline_proof="certified"` must never create baseline certification.

For the first release, generate deterministic Lean literal fixtures/receipts from the validated input and require actual kernel checking of acceptance plus application of the generic soundness theorem. Echo and independently compare the complete normalized input, not only its digest. Record the proof artifact, command result, source SHA, and transitive axiom audit.

Do not claim that Python or the entire JSON parser has been formally verified. Lean correctness applies to the exact decoded/reified data. Unsupported or malformed input is an input error; resource exhaustion is an execution limitation. Neither is mathematical infeasibility.

Proof fixtures use kernel-checked arithmetic (`decide`, `norm_num`, or equivalent within the allowlist), not `native_decide` evidence that introduces a new trusted axiom. `#eval` can supply execution evidence but is not a theorem.

## 10. Mandatory six-state release witness

Reuse the original C6–C9 typed model, global descriptor, proper basin, target, comparison states `{u,a0}`, and original Exact-GR certificate. Do not build a lookalike witness with a different property.

| Listed intervention | f(u) | f(a0) | Exact original margin |
|---|---:|---:|---:|
| Identity | 1 | 1 | 0 |
| U-only row intervention | 0 | 1 | 0 |
| B-only rerouting to the true class | 1 | 1 | 0 |
| Tiny disruption | 0 | 999/1000 | 1/1000 |
| Half disruption | 0 | 1/2 | 1/2 |
| Full disruption | 0 | 0 | 1 |

The table is the proposed mandatory expected result, **independently recomputed with an exact rational boundary-value solver** and consistent with the existing rational fixtures. C10 must add new Lean numerical-equality proofs for half and tiny, through the generic evaluator and exact typed bridge, not just copy their Python values into an assumption.

**Required source reconciliation:** `sixStateMatrix` is a separately defined rational baseline. `halfMatrix` and `tinyMatrix` are currently inside C8's `noncomputable section`; `oneRowMatrix` is in C9's `noncomputable section`; and B-only exists as Python `B_ONLY` but not as a named typed Lean witness. Add computable `Fin 6` matrices/entries with normalized rows and prove their **extensional equality** to the original half/tiny/one-row definitions, plus equality to the corresponding original actual typed kernel atoms. Construct `bOnlyJ := rationalStrategicIntervention sixStateMatrix bOnlyMatrix` and prove fixed P/U, probability one at both original `B₁` starts, and zero original margin. Do **not** edit C6–C9 files or merely import an unverified new lookalike table.

Certify identity-only zero-margin output, the genuine one-row partial response, half/tiny numerical ordering despite identical support, full-disruption maximum, and a tie example with two distinct indices. Verify the existing family-positive / listed-negative distinction.

Retain the D0/C10 objective-ranking reversal: tiny can have a larger one-step probability of reaching true B while having a smaller constitutive disruption margin than half. This is not an optimizer bug; the objectives differ.

## 11. Proposed source and integration inventory

Names below are proposed, not existing APIs. All new library modules should be under `PermanssonResearch/ReverseSolver/` and imported directly by `PermanssonResearch.lean`.

| New module | Principal responsibility |
|---|---|
| `CheckedRationalInput.lean` | Computable raw-to-validated rational matrix/descriptor/comparison/menu construction; input-normalization proof (not a claim that arbitrary JSON parsing is verified). |
| `RationalSupportGraph.lean` | Computable positive graph, bounded reachability, correctness. |
| `RationalBSCC.lean` | Deterministic complete bottom-class enumeration and recurrence transport. |
| `FiniteAbsorptionDirichlet.lean` | Boundary-value uniqueness and native probabilistic characterization. |
| `RationalAbsorptionSolve.lean` | Actual computable exact reference solve and totality. |
| `RationalAbsorptionCorrespondence.lean` | Rational class weights equal canonical probabilities. |
| `RationalEventuallyObserved.lean` | All-true class sums and exact eventual-event values. |
| `TypedEventuallyObservedCorrespondence.lean` | Genuine D0 typed baseline/intervention event-value transport. |
| `RationalConstitutiveMargin.lean` | Complete-B₁ minima, witnesses, original-margin equality. |
| `ExecutableConstitutiveSelection.lean` | Deterministic exact maximum, tie set, global dominance. |
| `ConstitutiveCertificateCheck.lean` | Computable checker, soundness, reference acceptance. |
| `ConstitutiveEndToEndCertificate.lean` | Original typed margin/PR wrappers and evidence boundaries. |
| `ComputableSixStateFixtures.lean` | Executable rational matrices for the old noncomputable-section witnesses; entry/matrix equality and new B-only typed witness. |
| `ExactSixStateC10Execution.lean` | Computed exact fractions and original typed release examples. |

Add separate Python files under `verification/research/` for production/reference execution, independent checking, golden receipt generation, arithmetic tests, and Lean receipt integration. Do not turn old test helpers into the production implementation and then call imports of the same implementation independent verification.

Add `docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md`; update the research build guide and relevant documentation index. Reconcile C9's stale draft/pending headers with its actual final verified source and merge commit, preserving its historical checkpoint evidence rather than overwriting the chronology.

## 12. Adversarial verification matrix

Target at least **100 meaningful new regression cases**, for at least **417** research regressions if the inherited 317-test baseline remains unchanged. The count is a floor, not a substitute for covering the following failure modes.

| Area | Required attacks |
|---|---|
| Input | Empty/non-square matrices, row sums not exactly one, negative probabilities, float input, bad rational denominators, mismatched menu dimensions, empty/out-of-range BR, duplicate-index conflicts. |
| Graph | Identity matrix, irreducible chain, multiple bottom classes, unreachable bad class, transient SCC with a cycle, very small positive edge, exact zero edge, omitted/duplicated/fabricated bottom class. |
| Absorption | No transient states, one transient self-loop, repeated transient cycling, split absorption, exact tiny probabilities, boundary-state initializations, singular-system corruption. |
| Observation | All-true periodic class; all-false class; mixed two- and three-cycles; false transients; two classes with the same observed status; positive occupation share but zero eventual truth. |
| Margin | Identity, U-only, B-only, tiny, half, full, ties, attained worst-case state, global maximum including zeros, changed comparison state rejected. |
| Quantifiers | Complementary partial interventions with `max min = 0` but `min max = 1`; no selecting a different fixed intervention at each start; mixed initial-law cancellation outside the hGR extremal case. |
| Baseline | Unknown baseline with positive margin (constitution but PR unverified); unknown baseline with zero margin (direct uniform-PR rejection); all-zero menu listed rejection without hGR; support-ineligible → not PR under literal mode without hGR but not necessarily zero margin; true hGR permits positive PR; explicit hGR refutation requires proof; wrong target/mode; unsupported baseline-certificate flag. |
| Bridge | Correct shape but wrong actual typed kernel; equal support but unequal weights; descriptor changed outside the baseline basin; incomplete B₁ transport; unproved external model; constructed P/U mismatch; Python-only B-only cannot count as original typed proof; original noncomputable witness cannot be assumed directly executable. |
| Receipt | Modified matrix, probability, class member, descriptor, BR, omitted candidate, wrong maximum, wrong tie set, stale fingerprint, stale proof binding, unsuccessful Lean check, output falsely labeled Lean-checked. |
| Integration | Reference vs independent producer/checker, reproducible golden output, exact-head source/proof provenance, existing D0 golden compatibility, kernel-checked numeric witnesses. |

Use deterministic exact fixtures and a bounded small-matrix enumeration grid with a fixed denominator/state-count scope. Supplement with rational metamorphic tests for state relabeling, menu permutation, and duplicate-kernel indices. Do not rely on Monte Carlo or approximate eigenvalues.

Some semantic negative cases cannot be represented by malformed matrix input alone. They require actual adapter type-check failures or named Lean counterexamples; retain that distinction in the test ledger.

## 13. Build order and hard stop conditions

1. **Parent preflight:** confirmed `main@b4989fc4...` and **four passed post-merge workflows** at audit time; recheck before branch creation. Freeze exact exported APIs, guard original source diffs, and compiler-spike the rational solver and computational six-state inputs.
2. **Graph vertical slice:** executable reachability, complete BSCCs, all-cycle/all-recurrent cases.
3. **Probability vertical slice:** prove Dirichlet uniqueness, implement total rational solve, connect one computed eventual-event value to the actual canonical path law.
4. **Typed vertical slice:** connect the computed value to the existing original D0/C6 typed property; then prove exact half/tiny margins using original B₁.
5. **Menu layer:** all candidate minima, deterministic global maximum, tie set, original-margin theorem and conditional PR wrapper.
6. **Execution evidence:** checker, reference acceptance theorem, exact receipts, independent producer/checker, adversarial suite, documentation and final review.

The highest integration risks are graph completeness, native first-step/absorption identities, computability of the chosen rational solve, and exact input-to-proof binding. Resolve these before expanding the CLI surface.

Do not accept a graph-only result, a noncomputable optimizer, a standalone exact-arithmetic report without valid original typed transport, or Python-only absorption arithmetic as completion of C10. A reduced release would require a separately named and explicitly narrower specification. If total verified producer+checker+transport becomes too large for one PR, split at an explicit **verified graph/absorption certificate** milestone and keep any C10 end-to-end claims for the successor; do not relabel an incomplete stage as full C10.

## 14. Protected files and release gates

Keep the frozen original `PermanssonLean/` and `PermanssonLean.lean`, v0.1.8 paper, application schemas/validator/fixtures, toolchain, dependency manifest, and C1–C9 proof sources unchanged. Keep the original default Lake target unchanged.

Prefer the existing automatic research-test discovery for the new tests and receipt integration. Add a discovered integration test which runs the C10 golden/receipt checks after the research library has built. This keeps the existing workflows unchanged; preserve D0 golden generation and its existing assertions. Generated receipts live in temporary output, not as undeclared library modules.

Every new library module uses `set_option autoImplicit false`. No placeholders, custom axioms, unsafe certificate bypasses, or replacement GR/PR predicates. Every static new module is directly imported. Audit generated receipt theorem dependencies as well as the research root, permitting only `propext`, `Classical.choice`, and `Quot.sound`.

Release requires all four workflows green at the exact final PR source and actual synthetic merge: Research Lean, Original Lean, Executable verification, and Application contract on Ubuntu and Windows. Require the expanded exact-rational suite, C10 receipt checks, D0 golden, original default build, direct-import coverage, source firewall, final theorem/assumption review, and exact-head Codex review. Any later source or documentation commit requires fresh final-head verification.

Record actual tests, declarations, imports, source head, base, synthetic merge, and receipt artifacts. Do not invent future audit totals. Merge remains an explicit author decision; post-merge CI is separate evidence.

## 15. Explicit non-goals

No automatic general Exact-GR discovery; new application standard; paper revision; empirical causal identification; arbitrary external rational realizations; infinite-state results; real/irrational executable kernels; interval uncertainty; continuous or unlisted intervention optimization; stationary-distribution optimizer; feedback/Bellman optimizer; guaranteed polynomial-time reference evaluator; or formally verified Python/JSON implementation.

C10 may return exact numeric results when baseline certification is missing. It may not relabel those results as PR certification.

## 16. Definition of done

For the original frozen six-state typed protocol, one reproducible run computes baseline and every listed intervention's bottom classes, exact absorption probabilities, eventual-observation probabilities, original constitutive margins, worst-case starts, global optimum and ties. Lean connects those values to the actual original path-law property and checks the emitted receipt. The existing original baseline proof supplies the separate PR gate. Half and tiny become formal exact numerical theorems, not just rational fixtures.

For arbitrary valid finite rational inputs in the declared computational scope, the reference evaluator is total and its receipts are accepted by the proved checker. Input reflection must construct valid `RationalMarkovMatrix`/menu objects before the proof-carrying evaluation. A positive margin without a genuine baseline GR certificate stays **uniform constitution established / PR unverified**; a zero margin refutes the listed original uniform PR even when the baseline certificate is missing.

**C9 establishes that the best listed original margin exists. C10 must compute it and certify what the computed number means.**