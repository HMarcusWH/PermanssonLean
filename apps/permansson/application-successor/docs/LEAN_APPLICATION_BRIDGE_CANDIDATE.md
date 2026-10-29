# Lean ApplicationBridge — finite α/P/U and observation-first receipt (candidate)

**Status:** Source candidate under PR #115, not an accepted scientific/Lean
receipt and not a release claim. Existing numeric application receipts must
continue to report `lean_status=NOT_EXECUTED` and
`scientific_claims_verified=false` until a *specific caller-supplied instance*
has been reified into Lean and replayed with authentic compiler evidence.

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
  models is introduced.

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

## Evidence and remaining work

1. Build `lake build PermanssonResearch` at an exact PR commit, with the
   research axiom audit and the no-placeholder / root-import gates. Local
   syntax inspection and Python tests are **not** substitutes for that build.
2. Reify each externally supplied rational α/P/U row, observation matrix,
   prior, legal action support and selected policy **as actual Lean constants**;
   verify byte/semantic identity and source labels. Reject any mismatched
   rational, missing/duplicated row or infeasible selected action.
3. Emit instance-specific proof terms and replay actual receipt statements,
   including the complete horizon-specific policy tree, not just the generic
   one-step identity. Audit transitive axioms and bind theorem type to request
   digest, compiler/toolchain identity and exact source H/S.
4. Add positive and adversarial mutation evidence before marking an
   individual receipt as `lean_status=VERIFIED`; the present application
   explicitly does **not** do that.

Historical archive-reproducibility `E_TOOLING_CLOSURE` is a separate existing
trust-profile issue. No workflow changes or bypasses are part of this bridge.
