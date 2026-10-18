# A2-P02 v2 — exact next-build specification

**Document ID:** `Permansson.A2P02.v2`  
**Prepared:** 18 October 2026  
**Authority:** the original Q-LOCAL contract and the PR79 Round 2 finding; the concrete source and hypotheses in this kit.  
**Implementation status:** source reviewed, compiler pending. This is not a newly accepted Lean release.

## 1. Fixed base and change boundary

Repository: `HMarcusWH/PermanssonLean`. Base commit: `674c1b557d99ab080afb65a797a99cb5840eab62`. Base tree: `b391f32f503f07bcfd7b29d8c24c1f9ad61eb19f`. Research root blob: `13dafb1d5fe1930a2f7ed875c333179eaea07250`. The connected repository read during this recheck still returned that main commit. The installer rechecks its exact Git objects and all baseline bytes; a later main must not be silently reset or overwritten.

Lean is `leanprover/lean4:v4.34.0`; mathlib is exact commit `5ed2965256430c3649e86755f9576b54eca72435`. The existing lake manifest pins the remaining eight dependencies. Preserve `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, the original core, historical research providers, application, paper, accepted release and all existing workflows.

The patch is **12 new repository files plus one modified root**. There are no deletions, dependency updates, default-target changes, old acceptance-record rewrites, new application versions or GitHub settings changes. Output receipts stay outside the checkout.

## 2. Mathematical target

Let the true canonical typed strategic-world model be M, with baseline induced kernel K and admissible strategic intervention J giving K_J. Let the existing `PrimitiveModelPair M F J` provide the approximate model, approximate family and approximate admissible intervention. It proves equality of the named component and target constructor. Each intervention preserves its own model's physical kernel P; the approximate model's P need not equal M's P. Cross-model P error is model error, not an additional strategic intervention.

Keep the original nonempty `ConstitutiveComparisonSet` B1. Do not use an observed subset, a set of minimizers, or a newly selected domain. For each y in B1 the true laws start at y. The approximate computations may instead start from separately declared probability distributions nu_0(y), nu_J(y), with uniform point-to-distribution TV bounds eps_0 and eps_J.

Fix T transitions, recording coordinates 0 through T, and the existing measurable `FinitePathProperty Y T` with score f in [0,1]. Its `toRegimeProperty` is the original full-path property. Denote its true baseline/intervention outputs by z_0(y), z_J(y). Their original constitutive margin is

```
kappa = inf_{y in B1} |z_0(y) - z_J(y)|.
```

The supplied real-valued reporting profile r_0,r_J has its existing `perturbedConstitutiveMargin` over the same B1. It is not renamed as the true margin or automatically as the exact margin of another model.

### 2.1 Derive actual visit budgets

For side a in {0,J}, choose a measurable good-history set E_{a,n}. On every history in that set, bound the two corresponding row measures' **event TV** by eta_{a,n}, with 0 <= eta <= 1. Outside the set use the explicit upper bound one, valid for probability rows. Define

```
d_{a,n}(w) = eta_{a,n} if w is in E_{a,n}, else 1.
```

This is a constructed measurable bounded majorant, not a caller's potentially unbounded raw error function. Its expected value under the actual TRUE side-a history distribution mu_{a,n} obeys

```
Integral d_{a,n} d mu_{a,n}
  = eta_{a,n} * mu_{a,n}(E_{a,n}) + mu_{a,n}(E_{a,n}^c)
 <= eta_{a,n} + v_{a,n},
```

provided mu_{a,n}(E_{a,n}^c) <= v_{a,n}. The source uses an extended nonnegative integral; it does not require an unjustified real Bochner integral. The proof only needs the displayed upper inequality, so no exact integral identity is exported as a separate theorem.

The intervention schedule is evaluated under K_J's true prefix law, not under K, not under the approximate model, and not under an empirical visitation estimate without its own certified upper bound. Row assumptions cover every good history, including histories not visited under the baseline.

The generic helper permits time-varying kernels on a declared common history type and a measurable append map. The canonical model adapter specializes the actual stationary model kernels while permitting history- and time-dependent good sets and budgets. Do not describe that specialization as an arbitrary nonstationary typed-model adapter.

### 2.2 Connect to canonical finite prefixes

`finitePrefixLaw_tv_le_averaged` proves its induction using the existing `finitePrefixLaw_succ` identity. The hybrid compares K and its approximation under K's actual prefix distribution, then moves the history distribution through a common approximate kernel. No projected process is assumed Markov.

`canonicalPrefixKernel K T` packages the existing `partialTraj`/`singletonPrefix` construction as a measurable kernel of its initial state. `mixedFinitePrefixLaw K nu T` is its explicit mixture, formed by compProd and projection. The source proves its probability property, reduction at a Dirac input, and initial-law TV contraction. This is a mixture of actual canonical finite paths. No additional theorem equating a separately defined infinite mixed path law is claimed.

Combining localized point-start error with the fixed approximate kernel's initial-law contraction gives

```
TV(true finitePrefixLaw_{a,y,T}, approximate mixedFinitePrefixLaw_{a,nu_a(y),T})
 <= B_a(T),

B_a(T) = min(1, eps_a + sum_{n<T} (eta_{a,n} + v_{a,n})).
```

The epsilon term is inside the cap and remains present at T=0. It does not move the true starting point or shrink B1. For normalized f, expectation error is at most B_a(T), with factor one, not an unhalved L1 distance.

This is the requested conservative additive bound. It is not claimed to be the smallest possible bound for each model. A separately derived sharper majorant or coupling bound can improve constants in a later change without modifying the original margin.

### 2.3 Reporting errors and original margin

Require independent uniform bounds

```
|approximate actual expected f under nu_a(y) - r_a(y)| <= b_a.
```

Construct the ORIGINAL `HasConstitutiveOutputErrors` with e_0=B_0+b_0 and e_J=B_J+b_J, using the actual baseline and intervened `toRegimeProperty` equalities. Apply the ORIGINAL `constitutiveMargin_perturbation_abs_le` to obtain

```
|kappa_reported - kappa_true| <= E,
E = (B_0 + b_0) + (B_J + b_J).
```

No reporting error is hidden inside the definition of kappa_true. Do not cap b_0 or b_J at one; reporting values can be outside [0,1]. Both strict-positive directions are included:

```
kappa_reported > E  => kappa_true > 0,
kappa_true     > E  => kappa_reported > 0.
```

For `|reported - true| <= E`, report-to-true uses `(abs_le.mp ...).2`; true-to-report uses `.1`. Equality with E does not prove strict positivity.

### 2.4 Exact scope and hypotheses retained

The record requires good-row and visit premises for all natural n, although its result sums only n<T. This is an explicit stronger interface, not an unmentioned all-time conclusion. A finite certificate can be extended beyond T using empty good sets, eta=0 and v=1, but this kit does not include an automatic padding constructor. The independent finite oracle checks only its finite schedule and does not claim to discharge Lean's all-n fields.

The concrete original-margin adapter uses normalized real-valued prefix scores. A metric-valued TV-Lipschitz property requires an additional bridge carrying its genuine Lipschitz constant; no factor-one result for an arbitrary such property is asserted here. A score merely bounded in absolute value by one has oscillation two, not one.

Initial distributions are supplied pointwise in y. The margin is a pointwise infimum and no measurable kernel in y is needed or promised by that reporting record. All relevant distributions themselves are genuine probabilities.

A positive finite margin does not establish persistence, Exact GR, full PR, a QSD, empirical identification, forecasting skill, or a larger-policy optimizer. The old X1 negative Exact-GR result and the separate positive economic example are unchanged.

## 3. Files being created

All paths below are repository-relative. Code is supplied in full, not as placeholder signatures.

| New file | Purpose and principal exports |
|---|---|
| `PermanssonResearch/Probability/GoodHistoryVisit.lean` | Explicit majorant, measurability/bounds, extended-integral visit estimate, generic time-varying history error |
| `PermanssonResearch/Probability/LocalizedFinitePrefix.lean` | Canonical prefix induction; localized score bound; actual initial mixture, Dirac reduction and initial-error transport |
| `PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixError.lean` | `LocalizedProtocolErrors`; two budgets; original output-error/margin bridge; both strict-positive consequences |
| `PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean` | Matched typed pair; reported 4/5, total error 1/5, certified true lower bound 3/5; zero-horizon initial-law counterexample |
| `verification/research/localized_prefix_support.py` | Shared source contract, exact-baseline byte checks, manifest/path/import guards, source patch generation |
| `verification/research/localized_prefix_gate.py` | Real compiler/dependency/source/signature/axiom/positive-control/mutation gate; fresh external receipts |
| `verification/research/test_localized_prefix_exact.py` | Independent Fraction arithmetic, exact-law, schedule, report, domain and invalid-input tests |
| `verification/research/test_localized_prefix_integrity.py` | Source and wiring checks; no claim of Lean proof |
| `verification/research/test_localized_prefix_gate.py` | Failure-policy tests; explicitly labelled mock transcript/control-flow tests |
| `verification/research/test_localized_prefix_compiler.py` | Mandatory real compiler gate discovered by existing Research CI; no skip path |
| `research/paper_closures/post_merge_79/A2_P02_BUILD_SPEC.md` | This exact specification |
| `research/paper_closures/post_merge_79/A2_P02_ACCEPTANCE_MATRIX.json` | Twenty explicit obligations with pending formal/remote acceptance |

The compiled library will have 632 direct research modules only if these four are applied to the specified 628-module base and compilation succeeds. This preparation has not observed that future build.

## 4. Existing files being modified and checked

**Modified:** `PermanssonResearch.lean` only. Add these four direct imports immediately after the existing `PermanssonResearch.X1.ExactMatrixTables` import:

```lean
import PermanssonResearch.Probability.GoodHistoryVisit
import PermanssonResearch.Probability.LocalizedFinitePrefix
import PermanssonResearch.ConstitutiveQuasi.LocalizedPrefixError
import PermanssonResearch.ConstitutiveQuasi.LocalizedPrefixExamples
```

The context patch and full patch must agree byte for byte with the installer-generated diff. Do not add imports after a docstring in an arbitrary location or duplicate an import.

**Reused and inspected:**

| Provider | Reason it is checked, not rewritten |
|---|---|
| `Probability/LocalizedHistoryTV.lean` (Research) | First-law averaged compProd inequality and generic history induction |
| `Probability/EventTVCalculus.lean` (Research) | TV triangle, map and compProd contraction |
| `Probability/SummablePathScores.lean` (Research) | Factor-one normalized score integral estimate |
| `Quotient/ApproxPrefix.lean` (Research) | Actual append map and canonical finitePrefixLaw recursion |
| `Probability/FinitePrefixTV.lean` (original core) | Original stationary prefix kernel, point-start law and probability instances |
| `ConstitutiveQuasi/Definition.lean`, `PathOutput.lean`, `PropertyErrors.lean` | Original normalized property and actual full-path output identifications |
| `Perturbation/PrimitiveModelPair.lean` (Research) | Matched component/target; each intervention preserves own P; cross-model P allowed |
| `Regime/Perturbation.lean`, `Regime/ConstitutiveMargin.lean` (original core) | Original effect/margin and both-sided output-error API |
| `ConstitutiveQuasi/CertificateExamples.lean`, `Examples/ConstitutiveNoninvariance.lean` | Existing four-state Bool-by-Bool model, admissible intervention and genuine two-start comparison set |
| `lean-toolchain`, `lakefile.toml`, `lake-manifest.json` | Exact compiler/dependency/default-target pins |
| `.github/workflows/research-lean.yml` and existing integrity workflows | Actual test discovery, global audit, source/event binding and preservation routing |

The installer additionally compares **every baseline tracked file** to its Git blob and checks executable modes on POSIX. This extends beyond only the selected providers. It does not replace the repository's existing source-bound preservation/export/archive gates.

Kit-only tools, unit tests, documentation, evidence and integration patches are enumerated separately in `FILE_OPERATIONS.csv`. They are not silently copied into the repository.

## 5. Wiring and build order

```
Existing LocalizedHistoryTV + EventTVCalculus
    -> GoodHistoryVisit
Existing finitePrefixLaw + ApproxPrefix recursion
    -> LocalizedFinitePrefix (also bounded-score provider)
Existing PrimitiveModelPair + original CQ PropertyErrors
    -> LocalizedPrefixError
Existing typed CertificateExamples
    -> LocalizedPrefixExamples
All four -> PermanssonResearch.lean -> existing Research build/global axiom audit
Installed test_localized_prefix_compiler.py -> installed localized_prefix_gate.py
    -> exact source/dependency preflight
    -> Research build + four explicit final-source elaborations
    -> 40 named declaration signatures/transitive axioms
    -> same-source positive fixture -> four actual semantic mutants
    -> source/dependency postcheck -> receipt and raw logs
```

The `full` command-line mode additionally builds the original default target. Existing CI's mandatory test invokes `focused`, because the workflow already runs the original default target separately. Neither gate invokes the full unittest discovery command, so the compiler integration test cannot recurse into itself.

## 6. Exact verification gate

The gate must distinguish success from inability to execute. It must not accept missing Lean, a syntactic error in a mutant, an import error, a timeout or a missing axiom record as intended negative evidence.

It checks the real `lean-toolchain`, exact Lean release version, each dependency checkout revision and cleanliness, baseline source bytes, allowed new surface, exact import wiring and no forbidden proof shortcuts. It requires the full expected set of 40 named declaration records. This explicit census includes definitions, instances and the record type; it is **not** a count of forty new theorems. The unchanged CI performs the broader transitive axiom audit of the full Research root.

The only permitted axioms are `propext`, `Classical.choice` and `Quot.sound`. Universe-annotated printer output is parsed without treating `Quot.sound.{u}` as an extra axiom. Missing, duplicate or unexpected records fail.

The gate first recompiles the unchanged positive fixture with the same imports as the mutants. It then edits exactly one registered occurrence for each of these four cases:

| Mutation | Why the source remains meaningful and false |
|---|---|
| Baseline report budget 1/10 -> 0 | Actual report remains 9/10 while true baseline output is 1 |
| Treated report budget 1/10 -> 0 | Actual report remains 1/10 while true treated output is 0 |
| Actual reported-effect theorem 4/5 -> 3/4 | Both defined report outputs remain unchanged |
| Actual zero-horizon initial gap 1 -> 0 | Same trajectory kernel, two legal opposite initial Dirac laws and an actual time-zero score |

These are source-level compiler tests. The literal mutation edits and failure-policy unit tests have been exercised here; **actual Lean acceptance of the positive fixture and rejection of these four mutants remain pending**. A resource or interface failure blocks acceptance and must be repaired without weakening the theorem.

Logs contain full argv, return code, elapsed time and raw output hashes. Receipts include actual local HEAD/tree, worktree status, a manifest/digest of all checked source, dependency revisions before/after, named declarations and mutant source hashes. Evidence output must be outside the source tree and fresh/empty. Source changes invalidate the result. `LOCAL_KERNEL_CHECKED__CI_ACCEPTANCE_PENDING` is a local compiler classification, not a GitHub event attestation.

## 7. Acceptance sequence

1. Verify package manifest and run `tools/run_kit_checks.py` into a new outside directory.
2. Create an isolated feature branch at the exact base; run installer dry-run, then explicit apply.
3. Prepare the real pinned dependency environment without changing pins. Run `tools/verify_lean_closure.py ... --mode full`.
4. Review theorem types and concrete premises against this specification. Read the actual positive and negative compiler diagnostics.
5. Run all original/research/executable/application tests and required preservation/export/archive workflows at the actual PR source.
6. Record actual H/B/S identities and exact-head review; after merge record actual M and post-merge workflow results. Do not relabel a local or synthetic-fixture observation as one of those events.
7. Add a separate final acceptance observation only after every required row is satisfied. Retain this preparation's pending record as historical provenance.

The current environment has no compiler and no full repository checkout. Therefore steps 2–6 on the real repository have not been performed in this correction pass. Synthetic installer and mocked driver tests are explicitly labelled and are only software QA.

## 8. What follows this change, not bundled into it

This kit does not purport to implement the whole eleven-item PR79 residual roadmap. The next distinct units remain: canonical post-merge evidence reconciliation; stronger X1/product-TV/multi-agent fixtures; projected time-varying/mismatched-start and discounted transport; broader measurable two-player recovery where claimed; solver/grammar information-boundary fixtures; a separately versioned supported C10-to-proof application slice followed by C11; defensible wider asymptotic objective/policy theorems; actual specialized or sequential-causal source identification; prospective empirical validation; and publication/operational governance gates.

In particular the unreconciled historical `EconomicWitness/ConstitutionCore.lean` owner-receipt hash from Round 2 is **not repaired by A2-P02**. Preserve old receipts; a separate evidence change must reconcile or explicitly retire that binding. This kit also does not promote the source-labelled Iran/Hormuz/Russia–Ukraine studies to certified regimes.

## 9. Stop conditions for the coding agent

Stop and report the actual diagnostic if the source base is different, any preserved byte changes, a dependency pin differs, a theorem requires an unplanned premise, a positive fixture fails, a false semantic mutant compiles, an axiom falls outside the allowlist, or a required workflow is skipped/failed. No automatic merge is authorized. Compilation fixes must update the source hash, patch, manifest, tests, specification and evidence; stale 43-test or interrupted-build records cannot certify revised files.
