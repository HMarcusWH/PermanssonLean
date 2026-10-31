# Finite metric contraction — source-bound Lean bridge candidate

**Development scope:** ROB-02 (metric robustness), `feature/application-successor-full`,
PR #115. `finite-metric` computes exact W1 transport certificates, the
contraction factor, row defects and invariant laws (see `NUMERIC_METRIC.md`);
`receipts.metric` independently validates every certificate.

## Mathematical contract

`PermanssonResearch/ApplicationBridge/MetricReceipt.lean`:

- `IsFiniteMetric d` (decidable: zero diagonal, symmetry, positivity, triangle
  inequality); `Pt d` is `Fin n` carrying the genuine `MetricSpace` built from
  `d`, the discrete σ-algebra and singletons measurable.
- `law d μ` — the PMF law of a rational probability vector; `kernel d K` — the
  Markov kernel whose rows are the rows of a rational Markov matrix `K`.
- `coupling_test_bound` / `coupling_w1DualLE` — a coupling of `μ` and `ν` with
  cost `c` bounds every 1-Lipschitz test, so `W1DualLE (law μ) (law ν) c`.
- `checkMetricReceipt` / `checkMetricReceipt_sound` — the metric axioms;
  couplings of every ordered baseline row pair with cost `≤ ρ d(x, y)` and
  `0 ≤ ρ < 1`; couplings of every baseline row with the perturbed row with
  cost `≤ δ`; both declared laws stochastic and invariant; a coupling and a
  1-Lipschitz potential for the invariant laws with equal value `w`.
- `checked_row_contraction` — Research's `IsW1Contraction (kernel d K) ρ`
  (against every pair of probability laws) via
  `isW1Contraction_of_test_images`.
- `checked_invariant_metric_bound` — Research's `ContractivePerturbation`
  is assembled (invariance through `law_invariant`) and `w1_le` gives
  `W1DualLE (law π) (law π̃) (δ / (1 − ρ))`.
- `finite_transport_certificate_sound` — `W1DualLE (law π) (law π̃) w` and no
  smaller bound holds: the potential is a Kantorovich–Rubinstein test that
  attains `w`. A coupling alone gives only the upper bound.

Not claimed: Polish-space moment and invariance arguments, occupation-margin
transport (`FiniteMetricProtocol`), a contraction of the perturbed kernel, an
empirically identified metric.

## Source emission and replay

`proof.metric_emit` runs the independent checker, emits only strictly
contractive receipts, reflects the baseline and perturbed models
(`K`/`Kt := inducedMatrix`), emits the metric with `metric_checked` (a theorem,
then the `Fact` instance), every coupling (the reverse pair is the transpose,
the diagonal pair keeps the row in place), both invariant laws and the
invariant potential, and states `receipt_checked`, `row_contraction`,
`invariant_metric_bound` and `exact_invariant_transport` with exact rationals.
Scope: the shared literal reflection bound (at most four joint states).

```bash
python3 -B -m permansson_app finite-metric request.json --output /tmp/metric
python3 -B -m permansson_app.proof.metric_emit request.json \
  /tmp/metric/metric_receipt.json --output /tmp/permansson-metric-instance
python3 -B -m permansson_app.proof.control_source_check --family metric \
  request.json /tmp/metric/metric_receipt.json /tmp/permansson-metric-instance
lake env lean /tmp/permansson-metric-instance/ReifiedMetric.lean
```

`verification/research/test_application_metric_live_lean.py` compiles the
packaged request, audits axioms and requires single-line mutations to fail at
the falsified obligation: an understated contraction factor, a non-strict
factor 1, an understated defect, an overstated invariant distance, a feasible
but non-optimal (product) coupling, a perturbed world row that differs from
the reflected source (all at `receipt_checked`) and a distance table that is
not a metric (`metric_checked`).

## Trust boundary

Emission and source rechecks report `lean_status: NOT_EXECUTED`. A compiler
pass is not an authenticated proof receipt, independent mathematical
certification, empirical identification or release approval.
