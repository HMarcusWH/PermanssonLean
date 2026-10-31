# Lean ApplicationBridge — finite α/P/U and observation-first receipt (candidate)

**Status:** Part of draft PR #115; not an accepted scientific/Lean receipt
and not a release claim. This page describes the first two bridge modules
(`FiniteWorldInput`, `BeliefReceipt`) and the unified candidate CLI. All 24
bridge families and their live replays are listed in
[`ACCEPTANCE_STATUS.md`](ACCEPTANCE_STATUS.md) and
[`CAPABILITY_SCOPES.md`](CAPABILITY_SCOPES.md). Application receipts keep
`lean_status=NOT_EXECUTED` and `scientific_claims_verified=false`, because
the application never runs or authenticates the compiler.

## Mathematical scope

- `PermanssonResearch/ApplicationBridge/FiniteWorldInput.lean` represents
  finite rational α(a|s,x), P(x'|s,x,a), U(s'|s,x,a,x') with independent
  positivity and row-sum certificates and the state-specific feasibility
  predicate. It proves nonnegativity and normalization of the full induced
  joint row and creates a genuine Markov kernel with matching one-step atoms.
- All three primitive rows are formally total. On **infeasible actions**, any
  P/U entries are normalized completion rows rather than source-identified
  transition data. α must have zero mass on those actions. A downstream
  observed-policy certificate must prove common-menu feasibility at all
  positive-posterior hidden states; arbitrary completed rows are not legal
  controls.
- `PermanssonResearch/ApplicationBridge/BeliefReceipt.lean` uses the actual
  successor chronology: **current-state observation → observation-dependent
  control → P world transition → U strategic update**. It proves observation
  normalization, Bayes cancellation including zero-probability branches,
  posterior-forward-value equality and normalized controlled successors. The
  controller is represented as `Fin no → Fin na`; no hidden joint state is
  passed into its action selector. `LegalObservedChoice` additionally requires
  common feasibility on all reachable positive-posterior states.
- The existing `ReverseSolver.Belief` library uses the *different* chronology
  action → transition → observation. No unproved equivalence between these
  models is introduced. `BeliefTreeReceipt.lean` instead constructs an
  explicit Research model with a one-step time shift (identity transition at
  time 0, reflected α/P/U rows afterwards) and states its theorems for that
  model's chronological law; see `BELIEF_LEAN_BRIDGE.md`.

## Proof boundaries

These are **universal Lean-level algebraic theorems conditioned on typed,
proved source premises**, not evidence that a supplied JSON request has been
faithfully parsed and compiled. They do not establish a general multistage
policy-tree optimality theorem, complete intervention admissibility, the
original-regime predicates, global PR/GR constitution, empirical identification,
independent mathematical CERT or an authorized application release.

The existing frozen `PermanssonLean/` implementation, previously accepted
artifacts, paper version, 25 active workflow definitions, and Lean toolchain
pin remain unchanged. The additions are under a new `PermanssonResearch`
submodule and its explicit root imports only. The pinned toolchain is Lean
v4.34.0 with mathlib v4.34.0 (see `lean-toolchain` and `lakefile.toml`).

## One CLI for every family

`permansson-app lean-emit` and `permansson-app lean-recheck` dispatch to the
emitter and the byte/semantic recheck of each family
(`proof/lean_candidates.py`): `finite-world` (model only), `lp`, every family
of `proof/control_source_check.FAMILIES`, and `exit`, which also takes
`--region`. Neither command runs Lean, and both keep
`lean_status=NOT_EXECUTED`.

```bash
permansson-app lean-emit --family private-stage request.json receipt.json --output cand
permansson-app lean-recheck --family private-stage request.json receipt.json --candidate cand
lake env lean cand/ReifiedPrivateStage.lean   # from the repository root, pinned toolchain
```

## Evidence status

Done for bounded instances:

1. `lake build PermanssonResearch` builds every bridge module at the PR
   head. Exact-head Research Lean CI also runs the research axiom audit and
   the no-placeholder and root-import gates. Local Python tests are not a
   substitute.
2. Externally supplied rational inputs are reified **as Lean constants**:
   α/P/U rows, observation matrices, priors, legal action supports, policies,
   payoff tables and certificates. `lean-recheck` binds the candidate bytes to
   the original request and receipt bytes.
3. Instance-specific theorems are emitted and replayed with a transitive
   axiom audit (`verification/research/test_application_*_live_lean.py`).
4. Single-line semantic mutations must fail inside the targeted theorem.

Not done: authenticated compiler receipts that would allow an individual
output to report `lean_status=VERIFIED`, and independent review of the
bridges. The application explicitly does **not** promote any output.

Historical archive-reproducibility `E_TOOLING_CLOSURE` is a separate existing
trust-profile issue. No workflow changes or bypasses are part of this bridge.
