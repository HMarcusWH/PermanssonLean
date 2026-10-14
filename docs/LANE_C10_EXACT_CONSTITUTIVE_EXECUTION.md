# Lane C10 — Executable exact absorption and original constitutive margins

**PR:** [#61](https://github.com/HMarcusWH/PermanssonLean/pull/61) (draft; do not merge until release gates).
**Frozen acceptance spec:** [C10 v1.1 audited](PR61_C10_Exact_Constitutive_Execution_Spec_v1.1_AUDITED.md), 13 October 2026.
**Parent:** merged C9 `main@b4989fc4fc633601197cdfa733fbce3f5c9ea2c8`.
**Status on 14 October:** implementation sources committed; CI still pending final-head full verification. This ledger records source obligations, not a claim of final certification. Every later code/document commit needs a fresh exact-head CI and synthetic-merge audit.

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
- `verification/research/c10_emit_lean_receipt.py`: verifies JSON, reifies the full **normalized** input and receipt into Lean literals, invokes the executable `checkFullReceipt` proof, and displays axioms. The source SHA is a provenance identity, not proof of correctness.
- `verification/research/test_lane_c10_lean_receipt.py`: tampering rejection plus an integration test compiling the actual reified six-state receipt with `lake env lean`, when the toolchain is present.

**Trust boundary:** the Lean theorem covers the exact decoded/reified numeric values and the D0 typed construction under its real adapter hypotheses. It does NOT prove arbitrary JSON parsing, the Python program, SHA-256 cryptography, real-world parameter estimation, all possible strategic generators, or a prospective predictive claim.

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

At this checkpoint, the source defines **171** C10 tests: 72 fixed + 64 exact two-state + 27 deterministic three-state + 6 golden + 2 JSON-to-Lean integration tests. The inherited C9 suite counted 317, yielding **488 expected discovered tests**; only the completed CI log may establish an actual passing total.

Release requires a successful Research Lean build, its root transitive axiom audit limited to `propext`, `Classical.choice`, `Quot.sound`, independent complete rational tests and D0-F golden, root direct-import coverage, proof-placeholder and custom-axiom source firewall, frozen original default `lake build`, original Lean, executable verification, and application contracts Ubuntu+Windows. Verify the **same final source head and GitHub synthetic merge**, reconcile docs, obtain final-head code review, and reserve merge for explicit author approval.

All C10 source must remain under the separate research library or its verification/docs. Frozen original `PermanssonLean/`, paper, application, compiler/manifest, pre-C10 theorem modules and schemas remain unchanged.

## Known boundaries and non-goals

- Positive rational margin by itself does not certify an original Permansson regime; an independent **original Exact GR** proof is required.
- Zero actual original margin refutes **uniform strategic constitution** and therefore original uniform relative PR, with no Exact GR premise; it does not exclude unlisted interventions.
- All-true recurrent classes count for eventual truth, even if periodic. Mixed-label classes contribute zero, even if their true occupation share is positive.
- Reaching an abstract graph class is not an empirical causal counterfactual. Every intervened rational matrix uses the D0 constructed typed alpha-only model with fixed world/update kernels.
- Computable reference Cramer arithmetic need not be polynomial-time. Unsupported external JSON schema, size limits, or resource exhaustion are distinct from mathematical failure.
- No `sorry`, `admit`, custom axioms, native-decision proof oracle, relaxed comparison set, or unproved baseline-certificate Boolean is acceptable.

**Release status:** DRAFT / UNMERGED until every exact-head gate reports success.
