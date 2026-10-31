# Exact one-step risk-constrained occupancy — numeric profile

The `one-step-risk` command binds a strict input to the actual finite strategic-world model `(α,P,U)`. A controller may choose a randomized admissible action at the observed initial joint state `(s,x)`. Only one transition is optimized. The *controlled* transition for action `a` is reconstructed from the original physical and strategic-update kernels:

\[
K_a((s,x),(s',x'))=P(x'\mid s,x,a)\,U(s'\mid s,x,a,x').
\]

For the declared initial distribution `µ`, the nonnegative occupancy/flow variables are `q(y,a) = µ(y)π(a|y)` on **every declared feasible state-action pair**. Exact mass equations enforce `Σ_a q(y,a)=µ(y)`. The linear objective maximizes the expected *one-step terminal reward*. A separate exact constraint enforces that the next-step probability of the *declared* risk region does not exceed the declared risk cap. This makes the policy search genuinely randomized when the best feasible policy needs a fractional risk budget.

A bounded exact LP candidate generator proposes a primal vector and dual-optimality certificate. An **independent checker** reconstructs all controlled `P/U` rows, mass/flow constraints, objective and risk coefficients from the original input and verifies the primal/dual certificate. It reconstructs the returned behavioral policy and next-state distribution directly from the **certificate's primal**, not from the LP producer's preferred optimal vector. Multiple tied optimizers can therefore receive the same objective certificate without claiming to be the same policy. For zero-initial-mass states, the first declared feasible action is used as an explicitly recorded legal default; it does not change the actual flow.

The bundled exact example has an initial *safe* state, actions **stay** and **gamble**, a risk cap of `1/2`, and terminal reward `1` only in the dangerous state. The checked policy gambles with probability `1/2`, achieving both reward and risk probability `1/2`. Changing the dual certificate, flow, original transition or input risk bound causes independent rejection. A bounded proposal that cannot find an optimum **does not** provide a Farkas infeasibility proof and is reported as `RISK_NO_CERTIFICATE`.

**Limits and nonclaims.** At most four joint states and five occupancy variables; fully observed, one time step; no history-dependent, multistage or private-information optimization; no semantic equivalence to a separate reference solver's *chosen* controller; no general conclusion about empirical intervention effects or Exact GR/PR; no certified application release. Bounded source-bound Lean candidates exist for the optimum (`FlowReceipt`, family `flow`; [`FLOW_LEAN_BRIDGE.md`](FLOW_LEAN_BRIDGE.md)) and for cap infeasibility (`FlowInfeasibilityReceipt`; [`RISK_INFEASIBILITY_LEAN_BRIDGE.md`](RISK_INFEASIBILITY_LEAN_BRIDGE.md)); the numeric commands never run Lean. Nine scientific certificate dimensions are retained separately and remain unassessed.

## Proved infeasibility of the cap (`one-step-risk-infeasibility`)

The optimum route above never presents a failed bounded search as a Farkas
proof. A separate command takes the same request and certifies infeasibility
exactly:

```bash
permansson-app one-step-risk-infeasibility request.json --output <new-directory>
```

For every joint state the floor `v(y)` is the least next-step risk
probability over the declared feasible actions, computed from the actual
P·U row's mass on the risk set. The receipt lists every action attaining it.
The least risk mass of any fully observed randomized policy from the initial
law is `Σ_y μ(y) v(y)`, attained by a pure floor policy. The cap is
infeasible exactly when that total exceeds it, and then `(v, 1)` is a
normalized Farkas ray of the occupancy program. The command refuses with
`RISK_CAP_FEASIBLE` when some policy meets the cap.

`receipts.risk_infeasibility` re-reads the original model without importing
either producer or the LP encoder. It checks that every admitted action's
risk is at least its state's multiplier, that each multiplier is attained,
and that the initial-law total exceeds the cap.

The packaged example `risk_infeasibility.v1.json` starts in *safe* with mass
3/4. There **stay** risks 1/4 and **gamble** risks 1, and *danger* is
absorbing. Under a cap of 1/4 the least achievable risk is 7/16, a shortfall
of 3/16.
