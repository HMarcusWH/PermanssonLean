# Approximate equilibrium and regime transport — research addendum v0.1.0

**Status: research implementation candidate, 25 November 2026.** This addendum is subsequent to the reviewed v2.0.1 manuscript; it is not a replacement edition, independent mathematical acceptance, or a new application release. Proof source and generated replay tests are supplied; deductive claims are conditional on successful compilation and the axiom audit for the exact revision. See [PR #132](https://github.com/HMarcusWH/PermanssonLean/pull/132) for observed checks.

## 1. Question and contribution

An equilibrium solver selects or certifies a strategic policy. Permansson describes the process induced by a strategic generator and a separate world kernel, then evaluates persistence, occupation and intervention-relative constitution. An approximate equilibrium does not itself imply any of those properties.

Google Research / Cogentic, [*An Exact Polynomial-Time Algorithm for 1/5-Approximate Nash Equilibria in Bimatrix Games*](https://github.com/google-research/google-research/blob/4a7bc8ab0bc7/cogentic_research_papers/bimatrix_nash_equilibrium/paper.pdf), 25 November 2026, PDF Git blob ace37421def2812d90c437ad80d2cfaeb91f2294, presents a new finite bimatrix algorithm. The local kite conversion is used here as motivation for an independently specified certificate interface, not as a trusted global solver or complexity theorem. Our arithmetic audit is [separate external evidence](../../../verification/external/cogentic/2026-11-25/README.md).

The added layer is **verification**, not general equilibrium search. It connects static regret certificates, discounted continuation residuals, and *conditional* policy and path-law perturbation budgets.

## 2. Static and discounted certificates

For each player use an own-action-first payoff matrix; transpose the column player's matrix from conventional joint-action order. For a fixed opponent, let v(a) be the expected score of pure action a under that opponent. The one-player regret is max_a v(a) − E_p v. Checking every pure-action gain bounds every mixed unilateral gain by linearity. Rational simplex checks are reflected into real rows. Python inputs for the static and kite modes use payoffs in [0,1].

The local s-kite repair mixes one player toward an attaining best response, or retains the supplied profile if already within the target. The mathematical statement is about real rows; the bounded executable returns rational rows and independently checks them. It does not implement the entire MaximinKiteNE trajectory or its polynomial-time guarantee.

For a finite discounted game and candidate value V, let Q_V be the continuation score, including the supplied opponent and transition kernel. If at every state and history the candidate policy has continuation-game regret at most ε and its absolute Bellman evaluation residual is at most ρ, with 0 ≤ β < 1, the proposed bound against arbitrary behavioral deviations is

    J(σ) − J(π) ≤ (ε + 2ρ)/(1 − β).

The two residuals account for both candidate evaluation and deviation. They are checked separately for each player and every state, not averaged over the visited states. With exact evaluation ρ = 0. If a continuation score was affinely normalized using width w, its regret in original units is w times the normalized regret; a constant score has zero regret. No iterative fixed-point or convergence guarantee is implied.

## 3. From regret to process bounds — extra hypotheses

A strictly positive gap g between maximizing and nonmaximizing actions at a fixed opponent gives nonbest mass at most ε/g. Moving that mass onto an attaining best action gives a best-response-supported row within min(1, ε/g) in total variation. Ties among best actions remain admissible. The projected rows need not jointly be an equilibrium: rechecking at the changed opponent is essential.

For independent product action rows with individual TV bounds δ₁ and δ₂, common mass yields a joint bound δ₁ + δ₂ − δ₁δ₂. Correlated or history-conditioned policies require their own verified kernel bound. In the typed generator G = (α,U), use separate uniform primitive errors for α, P and U; composition supplies

    d = 1 − (1 − δα)(1 − δP)(1 − δU)
    E_T(d) = 1 − (1 − d)^T.

These are bounds, not claims that each error equals its upper bound. Baseline and matched intervention budgets are distinct. On a common finite-prefix observable in [0,1] and the transported full comparison set, the original constitutive margin difference is bounded by E_T(d_baseline) + E_T(d_intervention). The lower bound is the original margin minus that sum. A strictly positive lower bound certifies only that finite-horizon margin, subject to the hypotheses. It does not establish Exact GR, stationary occupation or infinite-horizon PR.

## 4. Counterexamples and positive finite example

Use two safe states and one absorbing exit; either player's action true causes exit, and the physical transition and trivial update remain fixed. In a coordination game two exact strict equilibria choose the safe and exiting actions respectively. In a game where false is strictly dominant, a unique equilibrium chooses false for both players. Perturb only the first player's action to true with rational probability e>0. Its static regret is e; survival through T steps from either safe state is (1−e)^T, and survival forever is zero for each e>0, while at e=0 it is one. Small regret is therefore insufficient even with a unique exact equilibrium and arbitrarily small one-step error.

For e=1/10 and T=3, the baseline finite survival is 1, approximate survival is 729/1000, and the same action-selection intervention forces exit in both models. The comparison set contains both safe starts. The exact finite margin drops from 1 to 729/1000, matching the scalar geometric budget 271/1000. The Lean candidates evaluate the actual original killed-kernel law and original margin, rather than identifying a surrogate numerical matrix with that law without proof. The general product-budget composition and the concrete margin equality are separate declarations; an explicit instance transporting the entire primitive-budget record through that general theorem is a remaining strengthening.

## 5. Source crosswalk

| Item | Lean candidate source | Scope |
| --- | --- | --- |
| AE-01 | [BimatrixRegret](../../../PermanssonResearch/Games/BimatrixRegret.lean) | Pure/mixed equivalence, rational checks and real reflection |
| AE-02 | [KiteMixing](../../../PermanssonResearch/Games/KiteMixing.lean) | Local repair, not global solver |
| AE-03 | [ApproximateDiscounted](../../../PermanssonResearch/Games/ApproximateDiscounted.lean) | Full-history bound, original payoff scale |
| AE-04 | [ProductActionError](../../../PermanssonResearch/Perturbation/ProductActionError.lean) and BimatrixRegret | Fixed-opponent gap, projection, product-row and measure errors |
| AE-05 | [EquilibriumRegimeTransport](../../../PermanssonResearch/Games/EquilibriumRegimeTransport.lean) | Primitive product budget and original finite-prefix margin, separate errors |
| AE-06 | [RegretRegimeCounterexample](../../../PermanssonResearch/Games/RegretRegimeCounterexample.lean) | Exact equilibria, unique dominant case, leakage, actual margin |
| Receipts | [EquilibriumReceipt](../../../PermanssonResearch/ApplicationBridge/EquilibriumReceipt.lean) | Static and discounted rational input reflection |

The frozen mathematical definitions remain unchanged. This layer reuses the existing ActionTrace, DiscountedVerification, PrimitiveMargin, PrimitiveProductTV, constitutive-quasi, and original intervention and persistence interfaces.

## 6. Executable checks

From the repository root, use the repository's Python environment. The [research-only package](../../../verification/research/approx_equilibrium/) has no application-registry entry. Static inputs permit rectangular games up to 16 actions per player. Discounted inputs permit 1–6 states and two actions per player; transport inputs permit 2–6 states, two actions per player and 0–16 steps, with shared physical rows, trivial update and a fixed matched joint-action intervention. All numeric inputs and outputs are exact rational strings, under existing resource bounds. The transport comparison set is explicit and has at least two distinct states. Candidate calculation and receipt reconstruction are separate functions. Receipts bind the canonical input identity.

Extract the supplied matching-pennies fixture, produce and verify its receipt:

```bash
python -c 'import json; print(json.dumps(json.load(open("verification/research/approx_equilibrium/fixtures.json"))["matching"]))' > /tmp/ae-input.json
python -m verification.research.approx_equilibrium regret /tmp/ae-input.json > /tmp/ae-output.json
python -c 'import json; print(json.dumps(json.load(open("/tmp/ae-output.json"))["receipt"]))' > /tmp/ae-receipt.json
python -m verification.research.approx_equilibrium check /tmp/ae-input.json /tmp/ae-receipt.json
```

The other fixture keys are kite, x1 (discounted), and transport; use the matching command. Numeric receipt verification reports exact rational status, not automatic Lean execution or original regime certification. The generated static and discounted Lean checks run separately.

```bash
python -m unittest discover -s verification/research -p 'test_approx_equilibrium*.py' -v
lake build PermanssonResearch
```

The existing Research Lean workflow supplies the pinned toolchain, build, real receipt replay, semantic mutation checks and axiom audit. A test present in the tree is not evidence of a pass. The [regression matrix](../../../verification/research/test_approx_equilibrium.py) includes 30 numbered cases plus receipt tampering and resource adversaries; [integration](../../../verification/research/test_approx_equilibrium_integration.py) and [Lean replay](../../../verification/research/test_approx_equilibrium_lean.py) are separate. General transport is verified via theorem source; executable transport receipts do not yet emit their own generic Lean model bridge.

## 7. Evidence and limitations

This is not a proof of the external algorithm, a general rational Nash solver, a Markov-perfect equilibrium construction, or an empirical certificate. It introduces neither a new GR/PR definition nor a 27th application profile. The existing manuscript, guide, release hashes, certification inventories and earlier acceptance statuses retain their exact identities. Do not promote this candidate into a published edition until exact-head compiler, regression, replay, transitive axiom and preservation checks have passed and the mathematical interfaces have been reviewed.
