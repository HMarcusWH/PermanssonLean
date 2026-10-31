# One-stage private-control saddle — source-bound Lean bridge candidate

**Development scope:** OPT-06 (robust control, private-stage route),
`feature/application-successor-full`, PR #115. `finite-private-stage` computes
the private-control value with a two-sided rational saddle certificate (see
`NUMERIC_PRIVATE_STAGE.md`); `receipts.private_stage` checks it
independently.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/PrivateStageReceipt.lean`, over
Research's `ReverseSolver.PrivateControlStage` (nature draws its parameter
after seeing the mixture `p`, before the private control draw: `stageLaw p η`):

- `SaddleChecks Q p q v` — decidable: `p` and `q` are rational simplex
  vectors, `v ≤ Σ_c p(c) Q(θ, c)` for every θ and `Σ_θ q(θ) Q(θ, c) ≤ v` for
  every `c`. `PureChecks Q r` — decidable: every pure control is held to `r`
  by some θ, and some pure control guarantees `r` against every θ.
  `checkPrivateStage` / `checkPrivateStage_sound` combine both.
- `checked_isGreatest` — `v` is the greatest `privateValue` over **all real**
  mixed controllers (`IsGreatest (Set.range (privateValue Q)) v`), attained by
  the certified rational row `controllerRow`.
- `checked_private_saddle` — on the actual stage law, the certified
  controller guarantees `v` against every real nature row, and the certified
  nature row `natureRow` holds every real controller to `v`.
- `checked_solver_value` — Research's executable rational vertex solver
  `solvePrivateStage` returns exactly `v`. The proof combines
  `returned_isGreatest` with uniqueness of the greatest element, so the solver
  is never evaluated.
- `checked_pure_controls` — under private timing every pure control is worth
  at most `r`, and one is worth exactly `r`.
- `checked_revealed_control` — in the different experiment where nature
  observes the realized control (`p.map (fun c => (f c, c))`), some response
  holds every real controller to `r`, and some pure control earns `r` against
  every response.

No minimax theorem or LP duality hypothesis is used: both bounds come from
the literal certificate. Not claimed: multi-stage private games, committed
nature, learning or empirical identification.

## Source emission and replay

`proof.private_stage_emit` runs the independent checker and emits the payoff
table, both mixtures, `v` and `r` as literal rationals, with
`receipt_checked` (`decide +kernel`), `hs`, `hp`, `value_greatest`,
`private_saddle`, `solver_value`, `pure_controls` and `revealed_control`.

```bash
python3 -B -m permansson_app finite-private-stage request.json --output /tmp/ps
python3 -B -m permansson_app.proof.private_stage_emit request.json \
  /tmp/ps/private_stage_receipt.json --output /tmp/permansson-private-stage-instance
python3 -B -m permansson_app.proof.control_source_check --family private-stage \
  request.json /tmp/ps/private_stage_receipt.json /tmp/permansson-private-stage-instance
lake env lean /tmp/permansson-private-stage-instance/ReifiedPrivateStage.lean
```

`verification/research/test_application_private_stage_live_lean.py` compiles
the packaged 3×2 game, a 1×1, a single-parameter and a 4×4 instance and
audits axioms. It then requires single-line mutations to fail at
`receipt_checked`:

- an overstated value;
- an understated value, where nature's certificate no longer holds;
- a pure controller mixture;
- a non-holding nature mixture;
- an overstated pure-control value;
- a changed payoff entry.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
