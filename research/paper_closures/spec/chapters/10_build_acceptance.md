# Implementation contract and proof acceptance

## The actual delivery unit

This package supplies paper theorems and derivations for explicit targets corresponding to every atlas ID. It does not supply a compiling replacement repository. The coding agent's work is to formalize the stated definitions, bridges and proofs, and demonstrate acceptance on the actual pinned source. It must not weaken a target merely to achieve a green build.

The registry `registries/closure_contracts.json` is the per-atlas routing table. Its `paper_status`, `formal_status` and `residual_scope` fields are independent. `PAPER_DERIVATION` means the derivation appears here; **every new formal status starts as `NOT_LEAN_VERIFIED`**. `SCOPED_DERIVATION` or `CONDITIONAL_TRANSFER` must remain visible after a narrower theorem compiles.

## Existing source interfaces to reuse

The source register records exact local canonical blob hashes for the inspected providers. The following are important anchors, not permission to assume a missing theorem:

| Source | Reuse |
|---|---|
| `X1/TypedModels.lean` | Actual action/world/update kernels, `inducedKernel_atom_entry` |
| `X1/Comparison.lean` | `Jaction`, `Jupdate`, `Jjoint`, `comparisonSet`, negative Exact-GR theorem |
| `X1/FiniteOutputs.lean` | `baselineProperty_eq_kernelTerminal`, `constitutiveEffect_eq_finiteEffect`, `constitutiveMargin_eq_finiteInf` |
| `X1/MPECertificate.lean` | Both-player Bellman and pure/real-mixed one-shot inequalities |
| `X1/OccupationTargets.lean` | Rational-to-actual baseline atoms and Poisson target identification |
| `MultiAgent/Protocols.lean` | Strict action/update key factorization and exogenous common update |
| `ReverseSolver/ResidenceEvent.lean` / `ResidenceValue.lean` | Literal event, finite-history probability and existing full-history optimum |
| `ReverseSolver/C11ClassStationaryCertificate.lean` / `C11StationaryFamily.lean` | Exact stationary and complete-family checkers |
| `MultipleLimit/FiniteClassInvariantMeasure.lean` | Finite-class invariant probability existence/uniqueness |
| `Probability/KantorovichDual.lean` / `KantorovichTV.lean` | Existing dual predicate and bounded-diameter conversion |
| `Perturbation/ContractiveOccupation.lean` | Exact global dual contraction predicate, four-process margin theorem |
| `Quotient/ApproxPrefix.lean` / `ApproxMargin.lean` | Existing linear defect bounds and typed comparison interfaces |
| Frozen `Probability/CommonPartKernel.lean` | Measurable common subkernel where its exact typeclass premises hold |

Relative research paths in this table are under `PermanssonResearch/`; the last row is under `PermanssonLean/`. The source-register validator must check the actual filenames: a near-matching theorem title is not a usable import. Provider APIs have to be inspected in the pinned environment before committing new declarations.

## X1 target interface: no ambiguity about the final object

Within namespace `PermanssonResearch.X1`, add an explicit finite type `NumericalVariant` with constructors baseline/action/update/joint. Define its actual model by returning `model m` or the existing `Jaction/Jupdate/Jjoint m` applied model. Define `rationalEntry : Mode -> NumericalVariant -> Y -> Y -> Rat` from X-ATOM, not by taking an opaque real matrix's rational approximation.

The new declarations must establish these exact mathematical signatures:

```text
rationalEntry_nonneg:
  forall mode variant y z, 0 <= rationalEntry mode variant y z

rationalEntry_sum:
  forall mode variant y, sum_z rationalEntry mode variant y z = 1

actualKernel_atom_eq_rationalEntry:
  forall mode variant y z,
  (actualModel mode variant).inducedKernel y {z}
    = ENNReal.ofReal (Rat.cast (rationalEntry mode variant y z))

rationalTerminal_eq_actual:
  forall mode variant n y,
  ENNReal.ofReal (Rat.cast (rationalTerminal mode variant n y))
    = kernelTerminal (actualModel mode variant).inducedKernel n y

checkedTable_equals_rationalTerminal:
  for the declared checked table, every t in {0,1,2,3} and y,
  table[mode,variant,t,y] = rationalTerminal mode variant t y
```

For each of the six constants $c$ in X-MARGIN, the final declaration concludes, using the **existing** definitions and objects:

```text
constitutiveMargin
  (model m) (specification m) (family m) property (comparisonSet m) (Jkind m)
    = (c : Real)
```

These are interface specifications, not precompiled Lean snippets. Do not leave `sorry`, a custom axiom, a Boolean `accepted=true` field, `native_decide`, or an external numerical oracle in their place. Normal kernel-checked rational reflection and theorem application are permitted. A table-check theorem should reduce to finite exact equations and inequalities, followed by a general soundness theorem linking it to the actual kernel and original margin.

The candidate table is `certificates/x1_exact_tables.json`. Its serialized content has 8 matrices, 576 horizon values and 54 effect entries. The JSON decoder is not itself trusted mathematical evidence. A generator may emit Lean literals; the resulting terms and equations must be checked by Lean, including mutations of already-emitted literals.

## Generic interface records: fields the agent may not omit

**Action trace.** Finite state/action spaces; initial law; explicit player index; full observed alternating histories; nonanticipating behavioral own-action kernel; independent fixed opponent action kernel conditional on current state; actual conditional world/update law; reward, discount and bounds; exact state-marginal bridge.

**Finite monitor.** Finite state and control sets; nonempty permitted controls; stochastic rows; fixed original deadline; monitor initializer, time-indexed update, terminal reward; history summary recursion; actual history-law pushforward; policy information. Risk and hidden-state variants add their own fields rather than overloading a Boolean goal flag.

**Quotient shared mass.** Fine/coarse spaces, measurable quotient, baseline and coarse Markov kernels, every-row defect, common subkernel, jointly measurable density/lift theorem, matched starts/initial common mass. Any countably-generated or standard-Borel premise appears in the exported theorem.

**Contractive model.** Metric and Borel compatibility; Markov kernel; exact source `IsW1Contraction` or an explicitly different first-moment restriction; finite initial dual gap; invariant probabilities or a theorem generating them; both row-error budgets; explicit property and all four actual factorizations. A `P1`-only Lipschitz functional cannot be passed to the existing all-probability-law predicate without an extension theorem.

**Strict autonomy.** The original `TwoPlayerGenerator` product structure, common-update exogeneity, own-key factors, baseline initial law, baseline support/AE occupation at every time, supported action and update agreement, common treated mechanism and physical world. A support agreement on a single output is not mechanism agreement.

**Stationary family.** Positive state count, actual rational matrix, genuine bottom classes, canonical class enumeration, explicit rational determinant solver, full-state nonnegativity/normalization/support/balance, and original C11 typed identification.

**Specialized transfer.** The finite algebraic spaces and maps; exact symmetry/conjugation convention; every sign, rank, dimension, range, continuity or nonzero denominator assumption; and an actual model-to-feature identity. The adapter must expose an unmet model hypothesis instead of constructing a certificate from a filename.

## Proof-oriented build sequence

The following are work units, not promised GitHub PR numbers. Dependencies shown are mathematical, not chronological obligations to finish every preceding row.

| Unit | New proof content | Entry condition |
|---|---|---|
| U01 | X-ATOM and rational kernel typing | Existing X1 source read and unchanged |
| U02 | X-DP, exact table checking, X-MARGIN | U01 |
| U03 | S-TRACE, S-VERIFY, S-X1 | Existing MPE conditions; independent of U02 |
| U04 | M-AUTONOMY, M-CLOSURE, finite M-NOSEPARATION | Exact strict/support hypotheses reviewed |
| U05 | D-MONITOR and behavioral law bridge | Existing D1/D2 law interfaces |
| U06 | D-RESIDENCE, D-FIRST, D-AVOID | U05 |
| U07 | C11-REFERENCE/NULL/CHECK | Existing C2/C10/C11 foundations |
| U08 | Q-LIFT and Q-GEOMETRIC | Common-kernel/RN instance audit |
| U09 | A-CONTRACT and A-FACTOR-FIN | Existing dual calculus and C2 |
| U10 | Finite KR and invariant construction | Finite linear-algebra/transport records |
| U11 | A-KR-POLISH/COMPLETE, larger factorization | Analytic dependencies checked individually |
| U12 | D-LP and robust stage games | U05 and exact polytope constructor |
| U13 | D-BELIEF and D-SAFETY | Separate hidden-state and infinite-event specifications |
| U14 | F-SWAP, F-N, F-CLOCK, F-FEAS, F-LUMP, F-CORR | Exact permitted information per target |
| U15 | B-OVERLAP/LOCAL-ORDER and D-BLOCK/CLASS | Existing grammar, U05; C11 for class outputs |
| U16 | C-CLUSTER/RANDOM/FAMILY | Compactness, conditional law and ergodic APIs |
| U17 | XPLUS model and original grounded PR | U03 plus existing GR/grounded constructors |
| U18 | Specialized finite algebra and adapter contracts | Each source-specific hypothesis approved |

F-CAUSE is separately reviewed as an SCM identification/nonidentification target and is not inserted into the protocol-distance theorem. Q-LOCAL/DISCOUNT/REGIME and A-PRIMITIVE are wrappers after their stated input lemmas, not additional universal assumptions.

## Independent acceptance obligations

For every theorem, report the exact statement, source file, declaration name, hypotheses, reused declarations, proof method, new test methods and residual nonclaims. The supplied `registries/acceptance_tests.json` lists required adversarial objectives. At minimum:

- **X1:** all eight actual kernel mappings, all 18 states, all nine comparison starts, all six original margins; changed world/update timing, horizon, denominator, omitted start, mislabeled intervention and corrupted emitted Lean literal must be rejected for the intended reason.
- **Strategies:** a nonstationary allowed policy and exact finite telescoping identity including terminal value; exclude current-opponent/future-noise access; test both indexed players and all starts.
- **Autonomy:** positivity/support closure, stochastic anchors, update agreement and exogenous common coordinate; a reactive counterexample must fail a hypothesis, not be counted as strict MA2.
- **Quotients/metrics:** non-Markov projection, every-row defects, zero/one error boundaries, nontrivial horizons, unbounded-distance TV failure, and one missing member of the four-process factorization.
- **Solvers:** literal-word event equivalence, time zero and $m=0$, retries, danger precedence, hidden monitor state, randomization when risk demands it, nonrectangular nature, and finite versus infinite survival.
- **Stationary/grammar/specialized:** periodic classes, complete class lists, singular matrices, source dimension/coupling consistency, incompatible overlapping patches, nonmonotone positivity and rank-two rather than rank-one seam defects.

Fixture tests do not replace a generic theorem. A negative test must be rejected by the claim it attacks: invalid JSON is not evidence that the Lean checker rejects a false arithmetic theorem. A resource timeout is not a mathematical counterexample or impossibility proof.

## Formal integration and protected history

Use additive files under `PermanssonResearch/`, direct root imports and separately named executable tests. Existing protected historical files, manuscript/export bytes, application schema and dependency pins stay unchanged. Do not rewrite a frozen calculation receipt to mark a new theorem proved; issue new versioned evidence and update only the appropriate nonfrozen current crosswalk.

The exact-source acceptance process remains: current head and genuine synthetic-merge build; original and research Lean targets; transitive axiom allowlist; source placeholder scan; full executable/application/integrity checks; appropriate new theorem-level adversaries; independently reviewed statement scope; and explicit user-controlled merge. The one-time no-Lean-change condition from maintenance PR #77 does **not** apply to new research PRs; the permanent frozen-source boundary still does.

A new focused workflow can interact with the hardening contract's reviewed workflow inventory. Do not bypass that checker. Prefer the existing full research discovery/import/audit path until a separate reviewed workflow-profile change is genuinely required.

## Honest completion labels

A paper derivation here can become a Lean theorem in exactly its selected scope. The five optional specialized rows cannot become universal GR/PR results merely because their linear algebra compiles. General-state rows cannot lose tightness/Borel/moment premises, and risk or robust rows cannot lose policy/nature order.

Final closure of any broader atlas goal requires listing the residual question and either proving it, producing a valid impossibility theorem, or retaining it as open. This package makes the coding contract exact; it does not turn broad research phrases into unqualified existence claims.
