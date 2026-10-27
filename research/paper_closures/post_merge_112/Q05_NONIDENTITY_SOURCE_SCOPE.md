# Q-05 — nonidentity source witness: exact numerical candidate

**Status:** `EXACT_RATIONAL_CANDIDATE_NOT_LEAN_CERTIFIED`. This is a
constructive numerical regression for the original Q-05 obligation, not a
replacement for the original whole-path `ConstitutiveComparisonSet`,
`RegimePropertyMap`, or original `constitutiveMargin` theorem.

## Typed fixture (frozen numerical target)

- Fine strategic/world/action spaces: `Bool × Bool` and Boolean action.
- Coarse strategic/world/action spaces: `Unit × Bool` and Boolean action.
- Compression `q(s,x)=((),x)` drops strategic memory and is non-injective.
- The physical kernel **in all four source models** is literally
  `x_next = action`. No within-model strategic intervention alters it.
- Fine action true probabilities: baseline `1/10` for `s=false`,
  `1/5` for `s=true`; intervention `7/10` and `4/5`.
- Coarse action true probabilities: baseline `3/20`, treatment `3/4`.
- Baseline fine strategic update writes `s_next=false); intervention
  writes `s_next=true`; coarse update remains `()`.
- Original comparison candidate, fixed before evaluation:
  `B₁={(false,false),(false,true)}`.
- Discount `β=1/3` and score
  `Φ(w)=(1−β)∑ₙ βⁿ 1{world(wₙ)=true}`.

## Executed-in-Python rational equalities

The independent finite-chain resolvent regression
`verification/research/test_q05_nonidentity_source_fixture.py`
evaluates the actual typed finite transition order and yields:

| Original start | Fine baseline | Fine treatment | Coarse baseline | Coarse treatment |
|---|---:|---:|---:|---:|
| `(false,false)` | `1/30` | `11/45` | `1/20` | `1/4` |
| `(false,true)` | `7/10` | `41/45` | `43/60` | `11/12` |

The fine original effect is `19/90` at both starts; coarse effect
`1/5` at both compressed starts; margin difference `1/90`.
The baseline output error is `1/60`, treatment error `1/180`.
Every fine row has projected common mass `19/20`, with
`η=1/20`. The exact discounted envelope on each side is
`βη/(1−β+βη)=1/41`; hence `1/90 ≤ 2/41`.

The treatment reaches `s=true` from either original comparison start;
the baseline never does. A baseline-only row audit therefore omits a
genuinely treatment-reachable strategic state. The negative regression
also modifies that row while preserving probability normalization and
verifies that its defect exceeds `η`.

## Required Lean integration not claimed here

1. Construct actual typed fine/coarse `alpha`, fixed physical `P`,
   baseline/treatment `U`, and verify their induced atoms.
2. Prove type-respecting nonidentity compression, both legal strategic
   intervention constructors, and the required source `PointWitness`
   common-subkernel/row-domination hypotheses on all reachable rows.
3. Supply **original** predeclared `B₁` with nonempty measurable
   two-start path-law nontriviality; a singleton random path is invalid.
4. Bind the score to the original whole-path `RegimePropertyMap`,
   actual canonical path laws and both uniform original-margin
   comparison sets (`B̄₁=q(B₁)` exactly).
5. Verify all exported theorem types/axioms and semantic false-mutant
   tests against one genuine frozen H/S source and independent case
   review. No empirical, exact-GR, or all-time invariance promotion.

**Preservation:** Existing Q-04 localized bridges, Q-02 projected
common-mass machinery, frozen original `PermanssonLean/`, and the old
negative X1 exact-GR result are reused unchanged. This fixture neither
supersedes nor proves them.


## Conditional original-API integration

The concrete research module
`PermanssonResearch/Quotient/Q05ActualOriginalMarginAdapter.lean`
now constructs `sourcePointWitness` for the genuinely typed baseline and
treatment models **conditional on** `VerifiedSourceDomination`. That record
states two required kernel inequalities for **each** side: the common
subkernel is dominated by the actual fine induced kernel, and its
type-respecting projection is dominated by the actual coarse induced kernel.

The module also supplies a fixed measurable Bool-world score, separate
admitted intervention world-fixity, and a conditional
`original_margin_of_verified_source_domination` using the genuine original
`constitutiveMargin` on the entire two-start `B₁`. The exact
`1/41 + 1/41 = 2/41` envelope comes from the source finite-retention
kernel, not an assumed numerical TV error.

**NOT CLOSED:** `VerifiedSourceDomination` must be proved from the
actual `alpha -> P -> U` induced kernels, and the standalone rational
values `19/90` and `1/5` must still be identified with the two
whole-canonical-path original constitutive margins. Until those proofs
compile with exact-head provenance and receive independent review, the
conditional theorem is not a complete Q-05 acceptance certificate.


## Current-source reconciliation (27 October 2026)

The historical checklist predates PermanssonResearch/Quotient/Q05ActualAtomClosure.lean. The current source contains fine_induced_singleton, coarse_induced_singleton, fine_actual_atom_domination, coarse_actual_atom_domination, original_verified_atom_domination, original_point_witness, and actual_original_B1_margin_bound. These implement typed alpha -> P -> U singleton identities, all-state domination and a 2/41 bound for the original whole-path margin difference over the two-start B1. Thus actual atom domination is not merely postulated, although compilation and independent statement review remain distinct.

The bound does NOT establish exact 19/90 or 1/5 whole-path constitutive margins. Those must be individually located in Lean and authenticated, or recorded as remaining mathematics. No empirical/Exact-GR or unrestricted policy-class claim follows.
