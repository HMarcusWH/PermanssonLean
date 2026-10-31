# Adaptive admitted-block control — source-bound Lean bridge candidate

**Development scope:** OPT-09 (adaptive grammar control),
`feature/application-successor-full`, PR #115. `finite-adaptive-grammar`
computes the exact adaptive optimum over the admitted blocks of a patch grammar
(see `NUMERIC_ADAPTIVE.md`); `receipts.adaptive` checks it independently.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/AdaptiveBlockReceipt.lean`:

- `blockSystem` — the admitted blocks as the controls of a
  `FiniteControlSystem`, each available at every joint state; control `i`
  moves by block `i`'s rows. A whole block is selected before each
  α → P → U stage and the history may select another next time, which is the
  timing of Research's `AdaptiveGrammarControl`.
- `regionMonitor` — Research's `FiniteMonitor.Monitor` with one Boolean flag,
  "every observed state so far lies in the region", rewarding survival or
  exit at the horizon.
- `MonitorTableChecks` / `checkMonitorTable` — decidable, generic in the
  control, monitor and memory types: the table starts at the reward and every
  layer is the max-over-admitted-controls `score` of the previous layer at
  chronological time `N − r`.
- `checked_table_eq_value` — a checked table is Research's `FiniteMonitor.value`.
- `checked_adaptive_optimal` — via `monitor_optimal_and_attained`: every real
  full-history behavioral controller (`BehavioralPolicy`) is bounded by the
  table value on the actual chronological trace law (`traceExpectation`), and
  one attains it.

Per instance, the emitted source reflects the baseline and every admitted
block as a `FiniteWorldInput`. It uses the grammar bridge's per-block
theorems: feasibility and P are held fixed, and the block is the baseline with
exactly its declared α/U patch rows. Control `i`'s matrix is `inducedMatrix`
of block `i`. Research's `CertifiedMenu` route through overlap-model atom
certificates is not used. Frozen-block comparisons stay numeric, and
downward closure and empirical identification are not claimed.

## Source emission and replay

`proof.adaptive_emit` runs the independent checker and emits the block inputs
with their theorems, `members`, `sys`, `region`, `M`, `horizon` and the
literal table. The theorems are `receipt_checked` (`decide +kernel`) and, for
every start state `y`, `adaptive_optimal_y`. Lean emission is limited to
horizon 0..6.

```bash
python3 -B -m permansson_app finite-adaptive-grammar request.json --output /tmp/ad
permansson-app lean-emit --family adaptive request.json /tmp/ad/adaptive_receipt.json \
  --output /tmp/permansson-adaptive-instance
permansson-app lean-recheck --family adaptive request.json /tmp/ad/adaptive_receipt.json \
  --candidate /tmp/permansson-adaptive-instance
lake env lean /tmp/permansson-adaptive-instance/ReifiedAdaptive.lean
```

`verification/research/test_application_adaptive_live_lean.py` compiles the
packaged example (adaptive 9/16 against a best frozen 3/8) and an exit
instance with a single block, and audits axioms. It requires single-line
mutations to fail at `receipt_checked`:

- an overstated adaptive value;
- a claim that no block helps;
- a dropped block;
- a shrunk region;
- the exit objective for a survival table;
- a longer horizon.

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
