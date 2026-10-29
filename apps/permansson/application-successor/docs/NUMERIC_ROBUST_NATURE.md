# Finite rectangular versus committed nature — numerical profile v1

**Source:** `PermanssonResearch/ReverseSolver/RectangularFiniteGame.lean`,
`RectangularGameLaw.lean`, and `CommittedVsRectangularPathFixture.lean`.
This application module is a bounded exact-rational implementation **without**
a new application-to-Lean correspondence theorem. Do not infer a theorem-backed
receipt or independent certification from this document.

## Actual model, timing, and decision scope

Run `permansson-app finite-robust-nature <input.json> --output <new-directory>`.
The input supplies a complete typed finite strategic-world `α/P/U` model with
one feasible-action menu at each joint state `(s,x)`, and a nonempty, explicitly
listed set of alternative **complete physical P kernels**. Every alternative
uses the same strategic states, world states, actions, feasible sets, `α`, and
strategic update `U`. No external equilibrium, causal factorization or
estimated physical transition law is identified by this input.

The profile computes three **different** objects, with a predeclared rational
terminal state reward and finite horizon `H`:

1. `rectangular_optimal`: the Bellman value `V_r(y)=max_{a∈A(y)}
   min_{θ∈Θ} Σ_z K_{a,θ}(y,z) V_{r−1}(z)`, where nature observes the
   realized action and can select a new `θ` at every chronological node.
   The controller class is fully observed, remaining-horizon-dependent
   deterministic Markov control, and the output includes **all ties**.
2. `fixed_policy_rectangular`: the analogous rowwise nature minimization for
   the **specific user-declared** time-homogeneous deterministic policy.
3. `fixed_policy_committed`: for that exact same fixed policy, nature must
   commit to a **single complete** `P_θ` at time zero, used throughout the
   trajectory. Every scenario's whole-horizon value is retained before the
   worst-case minimum. **This is not an optimization over controller policies
   in a committed-nature game** and cannot be substituted for that game.

For every comparison start `y`, the computed fixed-policy values obey:

`fixed_policy_rectangular(y) <= fixed_policy_committed(y)`.

This is a consequence of the different admissible nature-chronology classes,
not a proof of a particular empirical strategic or causal mechanism. The
separate rectangular controller optimum is at least the rectangular value of
the fixed controller, but it need not be the solution to a committed game.

## Discriminating exact example

The installed `examples/robust_nature.v1.json` has two complete P models,
`go` and `safe` controls, and four world states. Under the **fixed** `go`
policy, each model committed for two transitions reaches terminal success:
committed minimum `1`. A nature permitted to switch between its two models
selects `start -> mid` under one model, then `mid -> bad` under the other:
rectangular fixed-policy value `0`. A controller that may choose `safe`
under fully observed rectangular timing can secure value `1`.

The receipt includes the entire per-horizon rational value tables,
per-action minimizing nature IDs and all maximizing controller ties. Its
consumer checker **does not import the numerical producer**; it recomposes
all action-conditioned `P*U` rows and verifies each table/identity/choice.

## Boundaries and distribution

- 1–12 finite joint states, 1–6 explicitly given nature models and 0–12
  transitions, with exact rational operands and resource bounds.
- A single fixed state-feedback policy is used for committed comparisons.
  Private randomization, incomplete information, history-dependent controller
  policies and unrestricted randomized optimality are **unsupported**.
- The baseline `α` is retained as a frozen typed input, **not** asserted to
  be an equilibrium or optimized policy. Optimized controls are explicitly
  chosen from each state's feasible action set.
- The scientific report's nine original dimensions remain unassessed.
  `lean_status=NOT_EXECUTED`, scientific verification is false, and empirical
  identification is not established.
- No active GitHub Actions workflow, Lean pin, frozen theory core, historical
  application root, or independent mathematical CERT condition is modified.
