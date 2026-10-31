# Observe-then-act belief trees — source-bound Lean bridge candidate

**Development scope:** OPT-07 (belief trees), `feature/application-successor-full`,
PR #115. `finite-belief-tree` observes the current joint state `(s, x)` through
`Q(o | x)`, chooses an action from the observation/action history that is
admitted at every hidden state still carrying mass, and then applies P and U;
the terminal reward is paid on the final joint state. `one-step-belief` is its
horizon-1, single-strategic-state case. `receipts.belief_tree` and
`receipts.belief` independently recheck the receipts.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/BeliefTreeReceipt.lean`, over the
observation input of `BeliefReceipt` and Research's `ReverseSolver.Belief`:

- `observe`, `advance` — unnormalized forward vectors (no Bayes division is
  trusted); `Legal` — an action is admitted at every hidden state with
  nonzero forward mass; `value` — the optimal unnormalized value, a maximum
  over admitted actions; `treeValue`, `treeLaw`, `treeLegal` — value,
  terminal vector and admissibility of a deterministic observation tree
  (Research's `Belief.Tree`); `seqValue`, `seqLegal`, `blindValue` — the same
  for observation-independent action sequences.
- `checkBeliefTree` / `checkBeliefTree_sound` and `checkBlind` /
  `checkBlind_sound` — decidable checks of the optimum, the selected tree's
  value, admissibility and terminal law, and of the blind sequence.
- `model` — Research's chronology selects a control, transitions and then
  observes. The application's observe-first chronology is embedded with a
  one-step time shift: at time `0` the transition is the identity and the
  control is ignored, so the first observation is of the initial state; at
  every later time the transition is the reflected fixed-action α/P/U row
  (`model_transition_succ`) and the observation is `Q` of the new world
  component (`model_observation`). `H` application transitions are `H + 1`
  Research steps. This is an explicit construction, not an assumed
  equivalence of the two chronologies.
- `checked_observation_optimum` — every real behavioral observation-history
  policy (`Belief.Behavioral`) whose actions are admitted on the hidden
  support (`RootLegal`) has actual expected terminal reward, under Research's
  `chronologicalLaw`, at most the checked value; the receipt's tree is such a
  policy and attains it.
- `checked_terminal_law` — under the selected policy the actual probability
  that the final joint state is `z` is the checked law entry.
- `checked_blind` / `checked_value_of_observation` — the blind sequence is an
  admitted observation-independent policy with actual value `B`, no admitted
  observation-independent sequence does better, and `B ≤ D`.

Posterior values and per-action scores reported by the receipt are not
restated in Lean. Hidden-state controllers, unrestricted POMDPs and empirical
observation models are not claimed.

## Source emission and replay

`proof.belief_emit` accepts both request formats, runs the matching
independent checker, reflects the model (`input_definition`) with admitted
actions exactly the feasible ones (`options_exact`), and emits the likelihood
and prior with their own stochasticity theorems, the selected tree (an
unreachable observation is filled with action 0: its forward vector is zero,
every action is admitted there and it contributes nothing), the optimum and
the terminal law; `receipt_checked`, `observation_optimum` and one
`terminal_law_<y>` per joint state. When the receipt reports a blind baseline
the emitter recomputes the best blind sequence by the Lean recursion and emits
`blind_checked`, `blind_baseline` and `value_of_observation`; a baseline whose
maximum runs through an empty admitted set (valued 0 in Lean) is refused.
Scope: the shared literal reflection bound, horizon 1..3.

```bash
python3 -B -m permansson_app finite-belief-tree request.json --output /tmp/tree
python3 -B -m permansson_app.proof.belief_emit request.json \
  /tmp/tree/belief_tree_receipt.json --output /tmp/permansson-belief-instance
python3 -B -m permansson_app.proof.control_source_check --family belief \
  request.json /tmp/tree/belief_tree_receipt.json /tmp/permansson-belief-instance
lake env lean /tmp/permansson-belief-instance/ReifiedBelief.lean
```

`verification/research/test_application_belief_live_lean.py` compiles the
packaged one-step and two-step requests and a horizon-3 fixture with two
strategic states where the admitted actions depend on the hidden support
(`tests/fixtures/belief_tree_restricted.v1.json`) and a dead-end fixture
(`tests/fixtures/belief_tree_dead_end.v1.json`), audits axioms, and requires
single-line mutations to fail at the falsified obligation: an overstated
optimum, a strictly worse admitted action, an inadmissible action whose
extension row equals the admitted one (same value and law; only admissibility
rejects it), a swapped terminal law (all at `receipt_checked`), an overstated
or inadmissible blind baseline (`blind_checked`), a non-stochastic observation
row (`likelihood_sum_one`), an unnormalized prior (`prior_sum_one`) and a root
action with no complete legal continuation (`receipt_checked`).

An action is scored only if some complete admitted continuation follows it. In
the dead-end fixture, `risk` splits the hidden support into joint states whose
menus are disjoint. It is listed in `available_actions` but never appears in
`action_scores`, and a request with no complete admitted policy at all is
refused with `BELIEF_TREE_COMMON_MENU`. The same fixture has equal observed
and blind values (2 = 2), which exercises the equality case of
`value_of_observation`.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
