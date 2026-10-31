# Packaged examples and their limits

Every packaged example lives in `src/permansson_app/data/examples/`. Each one
validates against its request schema, runs through its command, passes its
independent checker and, where a bridge exists, compiles as a Lean candidate
in the live replays. The examples are small, distinguishing models chosen to
make one effect visible. They are not data and say nothing empirical.

## Examples added for the newest profiles

| Example | Command | What it shows |
| --- | --- | --- |
| `private_stage.v1.json` | `finite-private-stage` | a 3×2 payoff table: private randomization over *calm*/*boost* is worth 1, the best pure control (*hold*) only 1/2; nature's certificate is (3/5, 2/5) |
| `adaptive.v1.json` | `finite-adaptive-grammar` | two row-local α patches, each admitted alone: adapting the block to the strategic state survives two steps with 9/16, the best frozen block only 3/8, without assuming the unadmitted joint block |
| `risk_infeasibility.v1.json` | `one-step-risk-infeasibility` | from *safe* (mass 3/4) the least achievable next-step risk is 7/16, so a cap of 1/4 is infeasible for every randomized policy |
| `cq1_transport.v1.json` | `finite-cq1-transport` | a CQ-1 certificate (margin 8/25) transported to an approximate pair at row distance 1/50: transported margin 301/1250; the pair's own margin 729/2500 respects it |

The earlier examples are described in each profile's `NUMERIC_*.md`
document, including [`NUMERIC_FOUNDATIONS.md`](NUMERIC_FOUNDATIONS.md).

`scripts/end_to_end.py` runs every packaged example. Four of them exceed
their family's Lean reflection bound and are reported as numeric-only:
`finite_safety.v1.json`, `finite_perturbation.v1.json`, `residence.v1.json`
and `robust_nature.v1.json`. Those bridges are exercised by in-bound
fixtures in their live replays.

## Limits that apply everywhere

- **Bounded and exact.** Dimensions, horizons and rational bit sizes are
  capped per profile (see each registry `scope` and
  [`CAPABILITY_SCOPES.md`](CAPABILITY_SCOPES.md)). Lean reflection often has
  a smaller horizon cap than the numeric profile.
- **One whole-run budget.** Every exact profile command runs in a child
  process under one budget for parsing, computation, the independent check
  and the outputs (`permansson_app.budget`). The limits are:

  | Limit | Default |
  | --- | --- |
  | Wall clock (the process group is killed) | 300 s |
  | CPU | 240 s |
  | Address space | 2 GiB |
  | Output, per file and in total | 32 MiB |
  | Captured stdout and stderr | 1 MiB |

  Exhaustion fails with `BUDGET_TIMEOUT`, `BUDGET_CPU`, `BUDGET_MEMORY`,
  `BUDGET_OUTPUT` or `BUDGET_STREAM` and exit status 2. The outputs are
  written to private staging and published only after success, so an
  exhausted run leaves no output directory or receipt.
  `PERMANSSON_RUN_BUDGET` (a JSON object) may lower these limits but never
  raise them. The packaged examples use under 1 s of CPU, 30 MiB of memory
  and 11 KB of output. `lean-emit` and `lean-recheck` are development tools
  outside the release scope and are not budgeted. Native C10/C11 `run` has
  its own bounded runner.
- **Linux only for this release.** The budget relies on Linux process limits.
  Other platforms are refused with `PLATFORM_UNQUALIFIED`. Python 3.12 and
  3.13 are qualified on Linux.
- **Declared models only.** Inputs are taken as given; nothing is estimated
  or identified from observations.
- **Finite statements.** Finite-horizon survival, one-step occupancy,
  one-stage games and finite constitutive certificates are not Exact GR/PR,
  QSD or long-run statements unless a document says otherwise.
- **No silent widening.** Planned items that are not implemented are listed
  as such in `IMPLEMENTATION_MANIFEST.json` and in
  [`ROADMAP.md`](ROADMAP.md).
