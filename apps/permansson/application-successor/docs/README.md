# Successor application documentation

Start with [`IMPLEMENTATION_OVERVIEW.md`](IMPLEMENTATION_OVERVIEW.md) for how
a request becomes a checked numeric result and, optionally, a source-bound
Lean candidate. Reviewers should read
[`REVIEWER_GUIDE.md`](REVIEWER_GUIDE.md) first.

## Orientation

- [`IMPLEMENTATION_OVERVIEW.md`](IMPLEMENTATION_OVERVIEW.md) — pipeline, package layout, bridges
- [`REVIEWER_GUIDE.md`](REVIEWER_GUIDE.md) — reproducing the evidence and reviewing one profile end to end
- [`CAPABILITY_SCOPES.md`](CAPABILITY_SCOPES.md) — every profile, its command, checker and Lean family
- [`EVIDENCE_AND_RECEIPTS.md`](EVIDENCE_AND_RECEIPTS.md) — receipt fields and the separate levels of evidence
- [`NATIVE_PROOF_REPLAY.md`](NATIVE_PROOF_REPLAY.md) — replaying Lean candidates on the pinned toolchain
- [`EXAMPLES_AND_LIMITS.md`](EXAMPLES_AND_LIMITS.md) — packaged examples and global limits
- [`ROADMAP.md`](ROADMAP.md) — execution plan, status and what is out of scope
- [`ACCEPTANCE_STATUS.md`](ACCEPTANCE_STATUS.md) — gate-by-gate status and the bridge table
- [`ARCHITECTURE.md`](ARCHITECTURE.md) — trust boundary and deliberately limited scopes
- [`ACCEPTANCE.md`](ACCEPTANCE.md), [`RELEASE_ACCEPTANCE.md`](RELEASE_ACCEPTANCE.md) — release-side criteria (not met by this branch)
- [`SEMANTIC_DIGEST_PROFILE.md`](SEMANTIC_DIGEST_PROFILE.md) — request identity hashing
- [`DOMAIN_IMPORTS.md`](DOMAIN_IMPORTS.md), [`FEDERATION_CONTRACT.md`](FEDERATION_CONTRACT.md) — envelopes for external data

## Numeric profiles

- [`NUMERIC_FOUNDATIONS.md`](NUMERIC_FOUNDATIONS.md) — kernels, LP certificates, survival, occupation, exit, menus, Bellman, safety, perturbation
- [`NUMERIC_ADAPTIVE.md`](NUMERIC_ADAPTIVE.md) — adaptive admitted-block control
- [`NUMERIC_ALGEBRA.md`](NUMERIC_ALGEBRA.md) — rational real-algebra witnesses
- [`NUMERIC_BELIEF_CONTROL.md`](NUMERIC_BELIEF_CONTROL.md) — one-step observation-conditioned control
- [`NUMERIC_CQ1.md`](NUMERIC_CQ1.md) — CQ-1 finite certificates and their transport
- [`NUMERIC_GRAMMAR_QUOTIENT.md`](NUMERIC_GRAMMAR_QUOTIENT.md) — patch grammars and typed quotients
- [`NUMERIC_METRIC.md`](NUMERIC_METRIC.md) — W1 contraction and invariant-law perturbation
- [`NUMERIC_MULTIAGENT.md`](NUMERIC_MULTIAGENT.md) — two-player protocols
- [`NUMERIC_MULTISTAGE_BELIEF.md`](NUMERIC_MULTISTAGE_BELIEF.md) — observation-history trees
- [`NUMERIC_PRIVATE_STAGE.md`](NUMERIC_PRIVATE_STAGE.md) — one-stage private-control robust value
- [`NUMERIC_RESIDENCE_NONLINEAR.md`](NUMERIC_RESIDENCE_NONLINEAR.md) — residence monitors and nonlinear objectives
- [`NUMERIC_RISK_OCCUPANCY.md`](NUMERIC_RISK_OCCUPANCY.md) — one-step risk occupancy and cap infeasibility
- [`NUMERIC_ROBUST_NATURE.md`](NUMERIC_ROBUST_NATURE.md) — rectangular versus committed nature

## Lean bridges

- [`LEAN_APPLICATION_BRIDGE_CANDIDATE.md`](LEAN_APPLICATION_BRIDGE_CANDIDATE.md) — overview and the unified `lean-emit` / `lean-recheck` CLI
- [`FINITE_WORLD_LEAN_REIFICATION_V1.md`](FINITE_WORLD_LEAN_REIFICATION_V1.md) — finite α/P/U input
- [`LP_CERTIFICATE_LEAN_BRIDGE.md`](LP_CERTIFICATE_LEAN_BRIDGE.md) — LP certificates
- [`CONTROL_TABLE_LEAN_BRIDGE.md`](CONTROL_TABLE_LEAN_BRIDGE.md) — Bellman control tables
- [`SAFETY_CORE_LEAN_BRIDGE.md`](SAFETY_CORE_LEAN_BRIDGE.md) — almost-sure safety core
- [`RESIDENCE_LEAN_BRIDGE.md`](RESIDENCE_LEAN_BRIDGE.md) — residence monitors
- [`MENU_LEAN_BRIDGE.md`](MENU_LEAN_BRIDGE.md) — frozen menus and killed-kernel survival
- [`OCCUPATION_LEAN_BRIDGE.md`](OCCUPATION_LEAN_BRIDGE.md) — recurrent-class occupation
- [`EXIT_LEAN_BRIDGE.md`](EXIT_LEAN_BRIDGE.md) — first-exit routing
- [`NONLINEAR_LEAN_BRIDGE.md`](NONLINEAR_LEAN_BRIDGE.md) — nonlinear classwise objectives
- [`PERTURBATION_LEAN_BRIDGE.md`](PERTURBATION_LEAN_BRIDGE.md) — finite-horizon TV perturbation
- [`QUOTIENT_LEAN_BRIDGE.md`](QUOTIENT_LEAN_BRIDGE.md) — typed quotients
- [`GRAMMAR_LEAN_BRIDGE.md`](GRAMMAR_LEAN_BRIDGE.md) — patch grammars
- [`ADAPTIVE_LEAN_BRIDGE.md`](ADAPTIVE_LEAN_BRIDGE.md) — adaptive admitted-block control
- [`FLOW_LEAN_BRIDGE.md`](FLOW_LEAN_BRIDGE.md) — one-step risk flow optimum
- [`RISK_INFEASIBILITY_LEAN_BRIDGE.md`](RISK_INFEASIBILITY_LEAN_BRIDGE.md) — risk-cap infeasibility
- [`ROBUST_LEAN_BRIDGE.md`](ROBUST_LEAN_BRIDGE.md) — rectangular robust nature
- [`PRIVATE_STAGE_LEAN_BRIDGE.md`](PRIVATE_STAGE_LEAN_BRIDGE.md) — private-stage saddles
- [`BELIEF_LEAN_BRIDGE.md`](BELIEF_LEAN_BRIDGE.md) — observe-then-act belief
- [`CQ1_LEAN_BRIDGE.md`](CQ1_LEAN_BRIDGE.md) — CQ-1 finite certificates
- [`CQ1_TRANSPORT_LEAN_BRIDGE.md`](CQ1_TRANSPORT_LEAN_BRIDGE.md) — CQ-1 certificate transport
- [`METRIC_LEAN_BRIDGE.md`](METRIC_LEAN_BRIDGE.md) — finite metric contraction
- [`ALGEBRA_LEAN_BRIDGE.md`](ALGEBRA_LEAN_BRIDGE.md) — rational algebra witnesses
- [`MULTIAGENT_LEAN_BRIDGE.md`](MULTIAGENT_LEAN_BRIDGE.md) — two-player protocols
