# X1 — same-world commons equilibrium incentives and learning

This scoped implementation continues the committed `docs/handover/x1/` candidate
from reference branch `claude/zen-einstein-ub8zgr-handover` at
`87a2d57d627fc60872d24f08503b69309e692056`; that reference branch
is not merged. Normative mathematics is integration-spec §8–8.1. All new source
lives in `PermanssonResearch/X1/`; historical core, paper, toolchain, manifest,
provenance and application schema are unchanged.

## Registered mathematical instance

Both generators inhabit exactly `Memory = Fin 3 × Fin 3`, `X = Bool`, and
`Action = Bool × Bool`. `true` means replete for the world and extract for an
action. The shared world is literally the same kernel, with clipped probability
`pRep(x,a) = min(1,max(0,r_x - (a₁+a₂)/4))`, `r₀=1/4`, `r₁=9/10`.
Payoffs are `v_x aᵢ - (193/211)aᵢaⱼ - (1/10)(1-x)`, with `v₀=0`, `v₁=1/2`;
both discounts are `9/10`.

E extracts with probability 0 when depleted and 1/2 when replete, independently
for each player, and holds memory. L extracts with probability
`(9/10)(qᵢ/2)+1/20`, and implements the exact bounded reinforcement rule using
reference payoffs `b(false)=-1/20`, `b(true)=1/20`. The update occurs after the
physical draw but reads the **old** world and realized action; it ignores `x'`.
The memory state records all variables needed by L; none is hidden outside the
Markov state.

The substantive region is `B = Memory × {true}`, and `h(q,x)=g(q,x)=x` on the
whole space. The registered pointwise start is `y₀=((1,1),true)`. The declared
property is `ψ = P(X₃=true)`. It allows exit and re-entry. Killed persistence is
reported separately as `P(X₀=...=X_L=true)`; hitting is never substituted for it.

The three typed strategic interventions are fixed as all-restrain action
replacement, memory reset to `(1,1)`, and their simultaneous joint replacement.
They leave P literally fixed. Reset changes the **next** memory, not the action
already drawn in the current step.

## Transparent prospective comparison-design correction

The first pointwise scenario used singleton `B₀=B₁={y₀}`. Independent review
found that it cannot satisfy the frozen original `pathLawNontrivial` gate,
which requires two starts with different full path laws. Stochasticity of a
single law does not satisfy that condition. The source preserves this negative
fact as `singleton_starts_not_pathLawNontrivial`.

**Design v2 was explicitly revised before any infimum output:** `B₀=B₁=B`, all
nine replete memory starts. This takes the whole previously declared region,
not an outcome-selected subset. It is an exploratory correction, not a claim
that the original singleton design was valid or that v2 was preregistered.
`region_pathLawNontrivial` reuses the existing time-zero path-law separation
theorem; `comparisonSet` constructs the actual original comparison-set object.
The equality of h at time zero over this basin does not establish the separate
descriptor-nondegeneracy or confirmatory gates.

## Theorem-to-source crosswalk

| Declaration | Exact scope |
|---|---|
| `pRep_bounds`, `learnerExtract_bounds` | Probabilities of the selected finite rational instance are valid. |
| `world_replete`, `identical_world` | The P used by both typed models has the very `pRep` used by incentives; literal kernel equality. |
| `action_product`, `update_dirac`, `update_ignores_new_world` | Actual conditional-product action laws and exact deterministic memory updates in α→P→U order. |
| `inducedKernel_atom_entry` | Every atom of each actual typed induced kernel equals the explicitly derived finite transition expression. No assumed matrix correspondence. |
| `bellman_equation` | Bellman equality separately for every indexed player and world state. |
| `no_pure_deviation`, `no_mixed_deviation`, `no_real_mixed_deviation` | Both players, both states, both pure actions, and every rational/real one-shot mixed probability in [0,1]. |
| `support_equality`, `depleted_strict` | Equality on every positive-support action; depleted extraction loses 9/211 for each player. |
| `interventions_world_fixed` | Every admissible intervention of the declared three-component family retains P. |
| `singleton_starts_not_pathLawNontrivial`, `region_pathLawNontrivial`, `comparisonSet` | Original singleton fails; prospective whole-region comparison inhabits the original gate. |
| `targetReplete_ne` | Distinct recorded rational target masses, not one shared ν label. |
| `replete_one_step_leaks`, `replete_not_exactGR` | At y₀ both actual kernels retain 13/20 of B mass; no spec with this B can be an Exact GR for either generator, irrespective of target/convergence choice. |
| `baselineProperty_eq_kernelTerminal`, `primitiveTerminal_eq_kernelTerminal` | Actual canonical ψ equals finite-kernel evaluation; baseline evaluation uses primitive-derived atoms. |
| `survivalProbability_eq_kernelTerminal_killed`, `survivalProbability_one` | Original finite-path staying equals the recurrence with the frozen killed kernel at every horizon, for starts in B; exact one-step survival is 13/20 for both. |
| `constitutiveEffect_eq_finiteEffect`, `constitutiveMargin_eq_finiteInf` | ORIGINAL effects/margin equal finite-kernel expressions on the genuine v2 comparison object; specific external numerical fractions still need arithmetic reflection. |
| `physicalRandomLimit_ae`, `observedRandomLimit_ae`, `original_empirical_randomLimit_ae` | Both actual models have a.s. random recurrent-class occupation limits under arbitrary initial laws, including the original empirical sequence; no deterministic target identification assumed. |
| `OccupationNumerics.poisson_identity`, `actual_poisson_identity`, `canonical_occupation_target_ae` | Distinct deterministic descriptor occupation targets under the actual typed laws, for every initial probability, via an exact Poisson identity on all 18 actual states including transients; no stationarity or irreducibility assumed. |
| `observedRandomLimit_full_law` | Complete class-selection-weighted law on observed probability measures under the actual typed path law. |

All eight source modules compiled with the exact pins, and the focused
transitive audit accepted 135/135 named declarations. Full exact-head and
synthetic-merge CI remain required before integration. Bellman/incentive conditions are not
promoted to an independently formalized infinite-history discounted strategy
verification theorem. That general bridge remains open.

## Exact finite calculations and independent reconstruction

`verification/research/x1_commons.py` emits the deterministic research-only
[calculation receipt](x1/commons-calculation.json). It is separate from the
unchanged application schema. A separate mathematical reviewer reconstructed
the models without importing this implementation and confirmed the fractions
below. Tests compare complete finite path enumeration with matrix iteration,
and verify every stationary equation exactly.

| Output at registered y₀ | E | L |
|---|---|---|
| Replete stationary-law mass | `5/12` | `44984685451641390245/355006278148174557117` |
| Reachable state count | 2 | 16 |
| Killed persistence L=1 | `13/20` | `13/20` |
| Killed persistence L=2 | `169/400` | `257/800` |
| ψ baseline | `227/500` | `8381459/32000000` |
| ψ after action or joint replacement | `3171/4000` | `3171/4000` |
| ψ after memory reset | `227/500` | `41417/128000` |

The stationary vectors satisfy the finite invariant equations. `Occupation.lean`
reuses the existing finite-chain strong law on the **actual** typed models to
obtain a.s. random recurrent-class occupation limits for every initial law,
with the original empirical-sequence bridge. `OccupationTargets.lean` then
identifies their descriptor images with the separately registered deterministic
targets. Independent unchanged
C11 calculation tooling also accepted E's two-state input and L's eleven-state
player-swap quotient. It correctly rejected the direct sixteen-state L input
against its unchanged twelve-state budget. A formal quotient/actual-kernel
occupation bridge is not assumed; a quotient calculation alone is not a
source-typed occupation theorem.

`OccupationNumerics.lean` and `OccupationTargets.lean` prove a direct
alternative to quotient transport: certify the Poisson equation
on every actual state, connect every rational entry to `inducedKernel_atom_entry`,
cancel against any invariant probability, then identify the descriptor law of
the actual random occupation limit. This route requires no global uniqueness
of the physical invariant law. Both modules passed pinned compilation;
the four additional independent tests check every row, wrong-target mutations,
transient-state bias corruption, and E's nine distinct physical invariant laws.

For v2, every one of the nine starts is evaluated and retained in the receipt:

| Finite-matrix absolute-effect infimum on all B | E | L |
|---|---|---|
| Action replacement | `271/800` | `3010663529/6400000000` (at q=(0,0)) |
| Memory reset | `0` | `1244820951/25600000000` (at q=(2,2)) |
| Joint replacement | `271/800` | `3010663529/6400000000` (at q=(0,0)) |

These are exact **finite-matrix calculation infima**. `FiniteOutputs.lean`
connects canonical horizon-3 output and original `constitutiveMargin` to actual
finite-kernel evaluation and its infimum. Kernel-checked arithmetic reflection
of the particular rational fractions in this table remains open; the table is
not yet a formal numerical κ certificate. Exact GR already fails, so neither
positive effects nor prospective positive infima establish substantive PR.

## Falsifiers and categorical status

Tests reject zero-congestion or wrong-P incentive certificates, missing learner
memory, confusing the old world with x', reset before the current action,
equating generators from their identical 13/20 next-world observations,
equating whole laws from equal selected ψ, and hiding distinct stationary
targets. Killed persistence and terminal repletion differ after two steps.
Every B row has retention at most 9/10, and finite killed recursions respect the
corresponding geometric bound; no periodicity/nonconvergence claim is made.

The receipt records nine categorical fields: validity (exact finite calculations,
Lean evidence separate), epistemic mode (constructed example), selection
(handover candidate and exploratory v2 correction), identification (stipulated,
not empirical), statistics (exact, not sampled), provenance (committed candidate
and independent reconstruction), substantive PR (not certified; B leaks),
direction (per property/intervention), and uniform gap (no formal certificate).
None is a numerical score or empirical institutional claim.

## Verification and remaining dependencies

Run the focused exact suite, pinned builds of `PermanssonResearch.X1.FiniteOutputs`
and `PermanssonResearch.X1.OccupationTargets`,
`x1_axiom_audit.py`, then the full research/default builds and original checks.
The completed local focused verification passed all eight source modules,
16/16 exact tests, and the 135-declaration transitive audit (119 declarations
use only the three allowed axioms; 16 are axiom-free).
The focused workflow does not replace synthetic-merge CI or PR-only C10
source-bound evidence. All eight new modules are imported directly by the
research root. The source does not require the broader F1 state-feedback witness.

Outstanding scientific/formal bridges: unrestricted discounted strategy
verification; exact arithmetic reflection for the horizon-3 output/margins;
confirmatory descriptor
and grounding gates. The invalid replete Exact-GR claim is explicitly rejected.
The separately versioned manuscript/release kit must preserve these boundaries.

## Accepted integration - 17 October 2026

Source `54babeeefd980c83fd7373f7429e028e5fa574e6`, base
`bc7617e15084673aa6053ab58282260226344c2b`, actual checked synthetic merge
`f1da869c9558faa9935e57042afba04b22eb3e00`, main merge
`5822cdff0fc360d9e368e10ff5f7576c3141a1b3`.
Research run `39041222836`, job `117420952984`, passed with 5248 audited
declarations, 810 exact regressions, 395 direct imports and PR-only C10
generation/independent source binding. Original/default core, D0 goldens,
source firewall, all required workflows and both application OS jobs passed.
Fresh exact-head review found no major issues; no unresolved threads remain.
Focused run `39041222796` compiled all eight modules, passed all 135 audited
declarations (16 axiom-free), and ran 16 exact tests successfully.

`canonical_occupation_target_ae` is now verified on the actual typed models
for both modes and every initial probability law. It uses the all-state
Poisson bridge, not a quotient assumption or global physical invariant-law
uniqueness. Original finite-output/margin transport and the killed-path event
bridge are also verified; the particular numerical margin fractions remain
computational results pending arithmetic reflection.

In addition to the formal leakage obstruction, `h=x` is constant on replete
B. Direct inspection of the original definitions therefore also rejects
Assumption 4.1's raw descriptor nontriviality clause. The all-nine-start
comparison revision supplies the separate path-law comparison gate only.
The [separately versioned research manuscript and kit](../release/v0.2.0/README.md)
retain this limit, the exploratory selection history and all OPEN obligations.
