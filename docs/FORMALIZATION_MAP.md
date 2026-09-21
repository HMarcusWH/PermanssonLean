# PermanssonLean formalization map

This repository formalizes the mathematical core of **Permansson Regimes v0.1.7** in Lean 4.

## Claim firewall

Status labels are used strictly:

- **PROVED** — accepted by Lean on the pinned toolchain.
- **SCAFFOLDED** — definitions/types exist, theorem not yet formalized.
- **OPEN** — not yet represented in Lean.
- **EMPIRICAL / OUT OF SCOPE** — depends on data, scientific identification, or literature priority rather than pure formal derivation.

Green CI means only that the checked Lean declarations compile. It does not upgrade OPEN or empirical claims.

## Dependency DAG

| Layer | Paper object | Lean target | Status |
|---|---|---|---|
| 0 | Measurable spaces / kernels | mathlib | PROVED upstream |
| 1 | Joint state Y = S × X | `JointState` | SCAFFOLDED |
| 1 | Action-selection kernel α | `StrategicGenerator.action` | SCAFFOLDED |
| 1 | Strategic-update kernel U | `StrategicGenerator.update` | SCAFFOLDED |
| 1 | World-transition kernel P | `StrategicWorldModel.world` | SCAFFOLDED |
| 2 | Induced joint kernel K_{G,P} | `StrategicWorldModel.inducedKernel`, `inducedKernel_isMarkov` | PROVED |
| 2 | Paper-level setwise / indicator semantics | `inducedKernel_apply`, `inducedKernel_apply_indicator` | PROVED |
| 3 | Path law / Ionescu–Tulcea | path-law module | OPEN |
| 4 | GR specification and exact persistence | regime modules | OPEN |
| 5 | Killed-kernel finite persistence | persistence module | OPEN |
| 6 | Typed interventions | intervention grammar | OPEN |
| 7 | PR constitution | constitution module | OPEN |
| 8 | Uniform constitutive margin | robustness module | OPEN |
| 9 | Intervention-family signatures | equivalence module | OPEN |
| 10 | Quotient preservation theorem | quotient module | OPEN |
| 11 | EGR → GR embedding | compatibility module | OPEN |
| 12 | QSD subclass | optional QSD module | OPEN |
| X | Scalar-defect / finite-detection / first-bad / singular lane | research modules | OPEN |

## First proof milestone — induced joint kernel

The induced kernel

\[
K_{\mathfrak G,P}(E\mid s,x)
=
\int_A\int_X\int_S
\mathbf 1_E(s',x')\,
U(ds'\mid s,x,a,x')\,
P(dx'\mid s,x,a)\,
\alpha(da\mid s,x)
\]

is implemented by `StrategicWorldModel.inducedKernel`.

The formalization explicitly preserves the dependency order
`α → P → U`: it uses `Kernel.compProd` rather than an independent product,
reassociates the retained history before applying `U`, and drops the realized
action only after the strategic update has consumed it.

The following are checked on the pinned Lean/mathlib toolchain:

- `inducedKernel_isMarkov`: the construction is a Markov kernel on `S × X`;
- `inducedKernel_apply`: the setwise law expands in the exact `α → P → U` order;
- `inducedKernel_apply_indicator`: the construction agrees with the paper's
  displayed triple-indicator integral.

The next dependency boundary is the trajectory/path-law construction from this
stationary one-step kernel.
