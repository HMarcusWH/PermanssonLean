# Lane C10 — Executable exact absorption and original constitutive margins

**PR:** [#61](https://github.com/HMarcusWH/PermanssonLean/pull/61) (draft; do not merge until release gates).
**Frozen acceptance spec:** [C10 v1.1 audited](PR61_C10_Exact_Constitutive_Execution_Spec_v1.1_AUDITED.md), 13 October 2026.
**Parent:** merged C9 `main@b4989fc4fc633601197cdfa733fbce3f5c9ea2c8`.
**Status on 14 October:** the previous fully verified C10 source checkpoint
`6601e9f90a01b036a6ba6720ccea257af31148bd` passed all four workflows
on synthetic merge `218d8df33ecb561bdee72c1978d24d644551692a`.
[Research Lean #38593687268](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38593687268)
compiled **4,013 jobs**, audited **3,540** transitive declarations within
`propext`, `Classical.choice`, `Quot.sound`, ran **489/489** exact-rational
tests, verified **306/306** direct imports and the generated Lean receipt,
and passed D0-F golden plus source firewall. Original Lean, executable
verification, Ubuntu and Windows application contracts passed that exact
synthetic merge as well.

**Verified source-bound release checkpoint:** source head
`f3831cfef167846c213d1e9232ba0c3982eb04e7` passed
[Research Lean #38602351380](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38602351380)
and all other three workflows on the exact synthetic merge
`f495fe579efa10f872c2455fa6b8b574c44c07d6`.
The run reports **512/512** exact research tests, **3,540** audited
declarations in the three-axiom allowlist, **306/306** research imports,
D0 golden and source firewall PASS. The generated *original six-state*
input/margin Lean bridge compiled, and both independent C10 provenance
verification and a fresh Lean replay passed. The separate C10 artifact
`11913649704` was uploaded with 30-day retention and archive
SHA-256 `5f330802c139932070c593a191636c7a440c1dfce386c3e85e798b72248d7813`.

**Verified mathematical corollary checkpoint:** source head
`27621f74e781a38ff75832432b7b7e93b7fb2f43` passed
[Research Lean #38605559315](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38605559315)
and all other workflows on synthetic merge
`c355e6708d7f7dc1544a104d38b2e4c0a77d5e1c`.
`C10ReleaseCorollaries.lean` explicitly composes C8 source-specific
positive representative reachability and C10 Cramer absorption and
C7 `pointGoodMass`: its theorems **compiled**. The run audited **3,546**
declarations under the three allowed axioms, imported **307/307**
modules, and passed **512/512** research regressions. Documentation-only
source head `1e51c302c01f8a76cf4c09fbbbf98b7933e80df8`
also passed all four workflows, including
[Research Lean #38606274298](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38606274298)
on exact synthetic merge `4a6d1fa8f2428a4c466b60f061dcab327b4d18dd`.

**Post-Codex P1/P2 source-changing remediation — pending new CI:**
the new `C10ReleaseRegimeEquivalences.lean` supplies original
relative PR iff positive exact receipt margin **only with an actual
original Exact GR proof**, plus exact C9 original opposing-support
eligibility iff positive margin under hGR and literal
`almostSureWeak` mode. Under literal mode it also gives the
one-way support-ineligible ⇒ not PR result even without hGR.
Evidence verification now checks every documented file, including
`verification_summary.txt` against its fixed required content,
and rejects unexpected files. The new metamorphic suite checks
state-relabeling probability/effect transport and menu-permutation
tie ordering. **These post-review source changes are not certified
by the previous green checkpoints**; the next final-head build,
research tests, source-bound Lean replay and review must pass.
PR #61 is ready for review, still unmerged.

## Frozen object and semantics

For each separately checked rational Markov matrix `K` and the ONE frozen Boolean descriptor `h`, the evaluator computes the genuine infinite-path eventual-true probability

`f_K(x) = P_x({w : ∃ N, ∀ t ≥ N, h(w t) = true})`.

Each member `i` has its own BSCC decomposition, its own class absorption weights, and its own genuinely typed alpha-only intervention under the D0 `Unit × Fin n` construction. Over **all** states of the originally frozen nonempty comparison set `B₁`, compute

`Δ_i(x)=|f_K0(x)-f_Ki(x)|; κ_i=min_(x∈B₁) Δ_i(x); κ*=max_(i in frozen menu) κ_i`.

The optimizer is `max_i min_x`, not `min_x max_i`, and is restricted to the **listed frozen menu**. This is NOT D0's finite-horizon hitting objective. Matrix shape or support equality does not identify an arbitrary external strategic-world model.

## Executable and mathematical implementation inventory

| Boundary | Source and formal claim |
|---|---|
| Exact checked input | `CheckedRationalInput.lean` constructs rational nonnegative row-stochastic proof-carrying matrices, complete descriptor, positive dimensions and nonempty comparison/menu; JSON parsing is outside Lean trust. |
| Exact graph | `RationalSupportGraph`, `RationalGraphCorrectness`, `RationalGraphCompleteness`, `RationalBSCC`, `RationalBSCCNative`, `RationalBSCCPartition` establish Floyd–Warshall positive-edge closure, complete bottom communicating classes and native class-set correspondence. |
| Rational Dirichlet | `RationalRecurrentAccess`, `RationalDirichletUniqueness`, `RationalDirichletDeterminant`, `RationalCramerEquations`, `RationalCramerBounds`, `RationalCramerPartition`, `RationalCramerCertification`, `RationalCertificateUniqueness` prove boundary access/uniqueness, determinant nonzero, exact equations, probability bounds, partition and universal reference check acceptance. |
| Total reference | `RationalAbsorptionSolve`, `C10ReferenceReceipt` produce a Cramer/adjugate finite rational solution and a total per-menu certificate passing the Lean checker for each checked nonempty finite rational input. |
| True infinite path | `TypedStoppedClassEvent`, `TypedStoppedClassLimit`, `TypedStoppedRecurrentLimit`, `TypedStoppedClassAbsorption`, `TypedStoppedClassSelection`, `TypedObservedCramerCorrespondence` connect exact finite stopping recursions and the genuine path law to Cramer class selection and eventual Boolean truth. |
| Checked path value | `CheckedRationalEventValue` identifies any accepted rational class table with the actual original infinite-path probability using uniqueness and the genuine native correspondence. |
| Full original margin | `TypedOriginalMenuMargin` equals exact rational pointwise effect and finite minimum to the untouched original `constitutiveMargin` for the *entire* original `B₁`, subject to full global descriptor/index correspondence. |
| End-to-end status | `ConstitutiveEndToEndCertificate`, `C10ReceiptSemantics` distinguish exact zero-margin PR exclusion (no baseline GR premise) from positive-margin PR promotion (requires actual original Exact GR evidence). |
| Full receipt | `RationalConstitutiveMargin`, `ExecutableConstitutiveSelection`, `ConstitutiveCertificateCheck`, `C10FullReceipt` prove full-menu maximum, complete ties, deterministic worst-case states, exact per-state values and sound input-bound checker. |
| Six-state witness | `ComputableSixStateFixtures`, `ExactSixStateBOnly`, `ExactSixStateC10Execution`, `C10SixStateBridge` reify earlier kernels with entrywise equality, keep P/U fixed, prove numerical half/tiny/full values and connect them to original typed margins. |

These are committed **source statements**. A theorem in a module not yet reached successfully by Research Lean is not recorded as compiled solely because its proof text exists. The latest completed run and commit identity govern certification.

## Rational executor, independent checker and proof artifact

- `verification/research/c10_exact_execution.py`: strict canonical rational strings, normalized menu/comparison, exact positive support and separate BSCC/Dirichlet calculations; exact fractions, per-start effects, margins, ties and SHA-256 of normalized input.
- `verification/research/c10_verify_receipt.py`: separate DFS SCC implementation and exact boundary/harmonic, probability partition, class labels, event, full-menu margin, tie, order and input-fingerprint checks. It does not reuse the producer's inverse or event solver; it is **Python numerical verification**, not a Lean theorem.
- `verification/research/c10_golden.py`: deterministic full/half/tiny/identity/U-only/B-only six-state output. Expected exact margins: `1`, `1/2`, `1/1000`, `0`, `0`, `0`.
- `verification/research/c10_emit_lean_receipt.py`: verifies JSON and reifies the full **normalized** input/receipt into Lean literals; kernel checks `checkFullReceipt`, not Python or cryptographic validity. `c10_emit_golden_bridge.py` appends a **six-state-only** literal-data/true-original-margin equality proof, leaving the generic emitter unchanged.
- `verification/research/test_lane_c10_lean_receipt.py`: tampering rejection and a generated original-six-state bridge compiled with the Lean kernel and audited for allowed axioms.

**Trust boundary:** the Lean theorem covers the exact decoded/reified numeric values and the D0 typed construction under its real adapter hypotheses. It does NOT prove arbitrary JSON parsing, the Python program, SHA-256 cryptography, real-world parameter estimation, all possible strategic generators, or a prospective predictive claim.


## V1.1 mathematical-claim coverage (source-hypothesis review)

The theorem names below specify exactly what the research library proves,
without adding numerical event values as assumptions:

| Original acceptance obligation | Proved source interface and guard |
|---|---|
| Complete positive-edge graph and finite bottom SCC collection | `RationalGraphCompleteness`, `RationalBSCCNative.bottomClasses_native_iff`; an actual `RationalMarkovMatrix n` is required |
| Unique rational class absorption and total accepted reference | `RationalDirichletDeterminant`, `RationalCramerCertification.referenceDirichlet_check_true`, `C10ReferenceReceipt.referenceReceipt_check_true`; nonempty state dimension derives from checked input |
| Positivity of a class weight exactly when a class is reachable | C8 `FiniteObservedSupportReachability.selected_weight_nonzero_iff_reachable` plus C10 `TypedStoppedClassSelection.cramerWeight_eq_canonical_selected_class` and C9 `RationalTypedSupportBridge.rationalTyped_reachable_iff`; the exact theorem `C10ReleaseCorollaries.cramerWeight_real_pos_iff_class_reachable` has compiled on the verified mathematical corollary checkpoint |
| True infinite eventual-observation event | `TypedObservedCramerCorrespondence.cramer_eventValue_eq_canonical_probability`, `CheckedRationalEventValue.checked_eventValue_eq_actual_path`; the C7 `TypedObservedEventConstitution.pointGoodMass_eq_event_probability` gives the original good-class semantics. `C10ReleaseCorollaries.cramer_goodClass_eq_native_pointGoodMass` has compiled on that checkpoint |
| Original complete B₁ and fixed descriptor | `TypedOriginalMenuMargin.realized_numeric_menu_margin` requires explicit global `hDescriptor` and complete `hComparison`; `sixDescriptor_frozen` and `sixComparison_complete` discharge the original six-state witness only |
| Exact entire finite-menu maximin and ties | `ExecutableConstitutiveSelection.selected_dominates`, `ConstitutiveCertificateCheck.checked_receipt_global_max`, `C10FullReceipt.checkedFullReceipt_worstStart`; no optimization over unlisted interventions |
| Original regime proof boundary | `C10ReceiptSemantics.checkedFullReceipt_zero_excludes_uniformPR` and `checkedFullReceipt_all_zero_listed_not_uniformPR` do not require baseline Exact GR; `checkedFullReceipt_positive_plus_exactGR` **does**. The new `C10ReleaseRegimeEquivalences.checkedFullReceipt_positive_iff_original_uniformPR_of_exactGR` adds the original iff requiring genuine hGR; `checkedFullReceipt_positive_iff_support_of_exactGR_literalMode` and `checkedFullReceipt_originalPR_iff_exactGR_and_support_of_literalMode` preserve the separately required literal-mode gate. This additional module is pending fresh CI. |
| Concrete original six-state release witness | `C10SixStateBridge.sixOriginalMargins_exact`, `sixOriginalFull_is_global_max`, `six_original_baseline_exactGR` plus generated `reifiedGolden_data_contract`, `reifiedGolden_numeric_margins`, `reifiedGolden_original_margins`; the latter are six-state-only, kernel checked |

**Scope:** Every indexed numerical matrix is realized by the constructed D0
alpha-only `Unit × Fin n` family, not an arbitrary identified empirical
world. An external parser, a receipt status string, and a hash do not
create a mathematical model equivalence or an Exact GR proof. The C10 Cramer-positive/reachability and C7 point-good-mass corollaries
have compiled and passed the research transitive audit at the verified
corollary checkpoint. The new hGR-gated PR/support iff module is a
separate final-head compiler/review obligation.

## Source-bound release evidence follow-on

[Reproduction guide](C10_RELEASE_EVIDENCE.md) details the new
`c10_release_evidence.py` and `c10_verify_release_evidence.py` entry
points. Their separate `Permansson.C10.release-evidence.v1` manifest
does **not** change the frozen numerical receipt
`Permansson.C10.rational-margin.v1`.

On a trusted GitHub PR checkout, the generator binds the *actual raw Git
synthetic merge object* (first parent = independent PR event base, second
parent = independent PR event head), the unchanged audited v1.1
specification bytes, original raw input and independently normalized input,
numerical receipt, the generated six-state Lean source, and compiler
transcript hashes. The verifier independently repeats the numeric
certificate, regeneration and actual Lean compilation with the allowed
axioms. No self-reported SHA or Boolean status can confer original Exact GR.

The PR-only CI step uploads a separate `c10-release-evidence` artifact
with 30-day retention; D0-F artifact generation and all historical
workflows remain intact. The artifact's source identifiers are calculated
after checkout and never baked into their own tracked source commit.
On `push` and `workflow_dispatch`, the artifact step is intentionally
skipped because there is no trusted PR synthetic-merge event. See the
guide for other execution contexts and scope limits.

## Six-state exact release target

| Typed intervention | Event probability at `u` | Event probability at `a0` | Full original `B₁` margin |
|---|---:|---:|---:|
| Identity | 1 | 1 | 0 |
| U-only | 0 | 1 | 0 |
| B-only | 1 | 1 | 0 |
| Tiny | 0 | 999/1000 | 1/1000 |
| Half | 0 | 1/2 | 1/2 |
| Full | 0 | 0 | 1 |

Class absorption and original-margin equality are separate proof layers; the six-state `sixReference` table must be accepted and identified with the generic total reference via certificate uniqueness. Preserve the original independently proved `observedExactGeneratedRegime` when promoting full/half/tiny from positive strategic constitution to original relative PR. The zero-margin cases are negative without needing `hGR`.

## Research CI gates and run commands

```sh
lake build PermanssonResearch
python3 -m unittest discover -s verification/research -p 'test_*.py' -v
python3 verification/research/c10_golden.py /tmp/c10-golden
python3 verification/research/c10_verify_receipt.py /tmp/c10-golden/receipt.json
python3 verification/research/c10_emit_lean_receipt.py /tmp/c10-golden/receipt.json /tmp/C10ReifiedGolden.lean
lake env lean /tmp/C10ReifiedGolden.lean
lake build
```

The previous frozen-source release checkpoint passed **489/489**
research regressions; the verified six-state source-bound release and
mathematical-corollary checkpoints passed **512/512** (one golden
bridge and 22 provenance adversaries added). Post-Codex remediation
adds **3** evidence-summary tampering tests and **7** state-relabeling /
menu-permutation metamorphic tests, yielding **522 expected discovered
tests**. This is a test-count forecast, **not a passing result** until
new exact-head Research Lean CI finishes. Source-bound evidence now
hashes `verification_summary.txt` and checks its exact content;
unexpected files cause a fail-closed rejection.

Release requires a successful Research Lean build, its root transitive axiom audit limited to `propext`, `Classical.choice`, `Quot.sound`, independent complete rational tests and D0-F golden, root direct-import coverage, proof-placeholder and custom-axiom source firewall, frozen original default `lake build`, original Lean, executable verification, and application contracts Ubuntu+Windows. Verify the **same final source head and GitHub synthetic merge**, reconcile docs, obtain final-head code review, and reserve merge for explicit author approval.

All C10 source must remain under the separate research library or its verification/docs. Frozen original `PermanssonLean/`, paper, application, compiler/manifest, pre-C10 theorem modules and schemas remain unchanged.

## Known boundaries and non-goals

- Positive rational margin by itself does not certify an original Permansson regime; an independent **original Exact GR** proof is required.
- Zero actual original margin refutes **uniform strategic constitution** and therefore original uniform relative PR, with no Exact GR premise; it does not exclude unlisted interventions.
- All-true recurrent classes count for eventual truth, even if periodic. Mixed-label classes contribute zero, even if their true occupation share is positive.
- Reaching an abstract graph class is not an empirical causal counterfactual. Every intervened rational matrix uses the D0 constructed typed alpha-only model with fixed world/update kernels.
- Computable reference Cramer arithmetic need not be polynomial-time. Unsupported external JSON schema, size limits, or resource exhaustion are distinct from mathematical failure.
- No `sorry`, `admit`, custom axioms, native-decision proof oracle, relaxed comparison set, or unproved baseline-certificate Boolean is acceptable.

**Release status:** READY FOR REVIEW / UNMERGED. The source-changing P1/P2 follow-on requires fresh four-workflow CI and Codex reassessment before author-controlled merge.
