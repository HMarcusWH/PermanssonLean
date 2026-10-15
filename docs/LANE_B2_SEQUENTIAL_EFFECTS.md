# Lane B2 — Four-corner sequential strategic effects (PR #65)

**Research status:** draft; implementation results must be evaluated on the exact
source head and GitHub synthetic merge. This document does not certify a new
v0.2.0 paper or supersede the frozen v0.1.8 proof/paper. Main baseline:
`a9d914520c68741a23cda89357499f3cf3f1500a` (merged A2 / PR #64).

## Scientific target

Freeze one original strategic-world model `M=(α,P,U)`, one original
`ConstitutiveComparisonSet M spec` (nonempty, in the original basin and with
two distinct point-initialized original path laws), one `ψ : path law → Z`,
and one *family of separately admitted strategic interventions*. Three actual
intervened typed models generate the outputs:

| Corner | Action | Update | World |
| --- | --- | --- | --- |
| 00 original | α | U | P |
| 10 action-only | α' | U | P |
| 01 update-only | α | U' | P |
| 11 joint | α' | U' | P |

All four corner property values are computed by evaluating the *same ψ* on
the canonical point-started α→P→U path law. `SequentialEffects.FourCornerProtocol`
contains three independent admissibility certificates and equations about the
resulting kernels; every world P equality is inherited from the core
`AdmissibleStrategicIntervention.world_eq`.

For `z00,z10,z01,z11`, define `a=d(z00,z10)`, `u=d(z00,z01)`,
`j=d(z00,z11)`, `cu=d(z10,z11)`, `ca=d(z01,z11)`. For each original
comparison state:

```text
|a - cu| <= j <= a + cu
|u - ca| <= j <= u + ca
```

The *false* direct claim `j <= a + u` is defeated by the compiled Boolean
original-path-law joint-only example (j=1, a=u=0).

For original `B₁`, the conditional uniform margins use the literal
`sInf (conditionalEffect '' B₁.states)`. If `a(y) <= εα` for every
`y∈B₁`, `κcu >= κjoint - εα`. Likewise
`κca >= κjoint - εU` under pointwise `u(y) <= εU`.
No suprema without an explicitly finite bound, and no zero-infimum-to-strong
singleton null implication. If both singleton effects are **pointwise zero**
throughout `B₁`, then both conditional margins equal the joint margin;
strict positivity is a separate corollary.

The only newly defined comparison-to-comparison quantities are **conditional
diagnostics**, not original PR certificates. `jointMargin`, `actionMargin`,
and `updateMargin` alone are proved definitionally identical to their
original `RegimeSpecification.constitutiveMargin` evaluations on the original
baseline. No claim that `B₁` is certified relative to an intervened corner.

For normed additive outputs (not arbitrary metric spaces), define

```text
I = z11 - z10 - z01 + z00
||I|| <= cu + u
||I|| <= ca + a
```

The real `sSup ||I||` is used only with an upper-bound proof. It is not the
scalar `j-a-u`, nor an identified causal interaction.

## Lane B grammar compatibility: the required repair

`PartitionGrammar.allowed` is not downward-closed. A component can contain
both physical action and update atoms (the existing `coarse` grammar does).
Consequently an admitted joint block does **not** automatically admit an
action-only or update-only block.

`SequentialBlockBridge.fromAllowed` therefore accepts **three** explicit
`AllowedBlock Γ` witnesses `Da,Du,Dj` and four *physical atom* equations:

```text
actionAtoms(Da) = actionAtoms(Dj)
updateAtoms(Da) = empty
actionAtoms(Du) = empty
updateAtoms(Du) = updateAtoms(Dj)
```

These imply the required actual kernel equalities by `patchedAction`,
`patchedUpdate`, and existing model construction, without asserting
decomposability of arbitrary admitted semantic blocks.

## Reused original witness and adversaries

- `BooleanPersistence.lean` already proves exact baseline GR, singleton
  survival effects zero, joint margin one, original uniform generalized PR.
- `BooleanEffects.lean` already proves the OR/AND/XOR original path-law
  behavior. B2 transports it, not claims a first proof.
- `SequentialAdversaries.lean` uses a true **two-time path-law cylinder**:
  `Y1=jointDest OR (Y0=q1 AND Y1=actionDest)`. On the original two-state
  comparison set, both singleton infima are zero, joint margin is one, but
  conditional-update margin is zero and action effect is one at q1. This
  refutes the stronger false uniform inference, rather than only illustrating
  a nonzero singleton at an isolated state.
- The vector adversary uses weighted genuine next-state cylinder-event
  probabilities with `(z00,z10,z01,z11)=(0,1,-1,2)`: `I=2` while
  `j-a-u=0`; conditional leg magnitudes are unequal (1 versus 3).
- Existing AND incomparable minima, XOR nonmonotonicity, invalid
  margin-preserving relabeling, and different banks with identical baseline
  remain regression obligations; no new theorem of arbitrary operation order.
- `verification/research/test_lane_b2_sequential_effects.py` contains
  independent exact-`Fraction` executions of the finite α→P→U process.

## Verification and release

Run `lake build PermanssonResearch.GrammarRobust.SequentialAdversaries`,
`lake build PermanssonResearch`, independent `test_lane_b2_sequential_effects.py`,
transitive axiom and source-placeholder audits, and all four mandatory workflows
(Original Lean, Research Lean, Executable verification, Application contract)
on **the exact head and GitHub synthetic merge**. A green older SHA cannot
certify later edits. The original v0.1.8 core, pinned toolchain, TeX/PDF/hash
manifests, and application certification schemas are immutable in this PR.

Excluded: causal identification, arbitrary sequential noncommuting software
mutations, uniqueness/upward monotonicity of minimal blocks, automatic exact
GR/PR from positive conditional margins, A3 contractive long-run transfer,
and a new paper release. Author approval is required before merging.
