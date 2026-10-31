# Foundational exact numeric profiles

These profiles were the first additions to the successor application. Each
has an independent exact checker and a source-bound Lean candidate family
for bounded instances (see [`CAPABILITY_SCOPES.md`](CAPABILITY_SCOPES.md)).
The commands below use the packaged examples; run
`permansson-app resources --full --output <dir>` to export them, or use
`src/permansson_app/data/examples/` directly.

## Finite α/P/U kernel — `finite-kernel`

```bash
permansson-app finite-kernel examples/finite_world.v1.model.json --output out/finite-kernel
```

Validates finite strategic, world and action spaces, the admissible actions,
exact rational stochastic `α/P/U` rows, and the induced joint transition
kernel in the order **α → P → U**. The independent checker recomputes the full
kernel. Lean family `finite-world`
([`FINITE_WORLD_LEAN_REIFICATION_V1.md`](FINITE_WORLD_LEAN_REIFICATION_V1.md)).
Rows of infeasible actions are explicit mathematical completions, not source
data. Nothing claims identification of the factors from external data.

## Exact LP certificates — `lp-propose`, `lp-check`

```bash
permansson-app lp-propose examples/lp.v1.model.json --output out/lp
permansson-app lp-check examples/lp.v1.model.json <receipt.json> --output out/lp-check
```

`lp-propose` enumerates bounded exact vertices and proposes a primal/dual
certificate. The separate `lp-check` verifies a supplied primal/dual
certificate or a Farkas infeasibility witness without invoking a producer.
An unlocated vertex returns `NO_CERTIFICATE_FOUND`, not a theorem of
infeasibility. The checked value does not identify the controller that
another solver happens to return. Lean family `lp`
([`LP_CERTIFICATE_LEAN_BRIDGE.md`](LP_CERTIFICATE_LEAN_BRIDGE.md)): weak
duality, matching optima and Farkas infeasibility over all real feasible
vectors of the normalized LP.

## Killed-kernel survival — `finite-survival`

Compares a held-fixed strategic intervention with a baseline using an exact
killed-kernel recurrence and a complete declared comparison set. It checks
every horizon row and the minimum absolute finite difference. Lean family
`survival` ([`MENU_LEAN_BRIDGE.md`](MENU_LEAN_BRIDGE.md), survival tables).
This does not establish Exact GR/PR, infinite-horizon persistence, QSD
uniqueness or empirical transition probabilities.

## Recurrent classes and occupation — `finite-occupation`

Computes all bottom recurrent classes, exact stationary laws and
start-specific absorption weights. `expected_limit_laws` are explicitly the
**means of random limiting class laws**, not the law realized on every sample
path. The checker reconstructs the `α → P → U` kernel and uses separately
computed communication and reachability sets with exact stationarity and
harmonic equations. Lean family `occupation`
([`OCCUPATION_LEAN_BRIDGE.md`](OCCUPATION_LEAN_BRIDGE.md)).

## First exit and never-exit mass — `finite-exit`

```bash
permansson-app finite-exit examples/finite_world.v1.model.json examples/finite_region.v1.json --output out/finite-exit
```

Takes an explicit region and finite horizon. It checks every survival value
and first-exit-by-destination vector, and keeps never-exit mass without
renormalization. Lean family `exit`, which also binds the region file
([`EXIT_LEAN_BRIDGE.md`](EXIT_LEAN_BRIDGE.md)). Eventual exit is an exact
finite-state Markov property; it does not establish an equilibrium, a
constitutive intervention or an Exact GR.

## Frozen-menu optimization — `frozen-menu`

Computes the exact finite-horizon survival or exit objective for each
*explicitly listed* feasible α/U intervention (1–8 entries), checks every
choice independently and reports every tied optimum. It never claims that the
menu exhausts all feasible policies. Lean family `menu`
([`MENU_LEAN_BRIDGE.md`](MENU_LEAN_BRIDGE.md)).

## Fully observed hitting Bellman — `finite-bellman`

Implements the finite-horizon hitting recurrence. A goal state has terminal
value one and a forbidden state value zero. Elsewhere, the value with `h+1`
transitions remaining is the maximum over permitted actions of the expected
`h`-table value. The controlled transition is recomposed exactly from
**P then U**, holding the physical model fixed and optimizing over declared
actions instead of treating baseline α as optimal. The checker validates the
entire time/state table and **all** tied optimizers. Lean family
`control-table` ([`CONTROL_TABLE_LEAN_BRIDGE.md`](CONTROL_TABLE_LEAN_BRIDGE.md)).

## Almost-sure safety core — `finite-safety`

Computes the greatest almost-sure controlled invariant subset of a declared
safety region by finite descending pruning. The receipt records every
pruning iterate and an admissible stationary witness. **Being outside the
core does not mean zero survival probability**, only that almost-sure
protection is unavailable from that state. Lean family `safety-core`
([`SAFETY_CORE_LEAN_BRIDGE.md`](SAFETY_CORE_LEAN_BRIDGE.md)). The packaged
example exceeds the reflection bound and stays numeric-only; the live replay
uses in-bound fixtures.

## Finite-horizon perturbation — `finite-perturbation`

Compares two typed finite models with the same ordered joint-state inventory
and two declared initial laws. It computes exact killed-process survival
through horizon `h`, every row total-variation discrepancy, the initial-law
TV and the bound `min(1, TV(initial laws) + h · max_row_TV)`. Lean family
`perturbation` ([`PERTURBATION_LEAN_BRIDGE.md`](PERTURBATION_LEAN_BRIDGE.md)).
These are finite-time error bounds, not long-run stability or statistical
identification. The packaged example exceeds the reflection bound and stays
numeric-only.
