# Lane C10 — Exact finite rational execution and constitutive-margin checking

**PR:** [#61](https://github.com/HMarcusWH/PermanssonLean/pull/61)
**Base:** merged C9 `main@b4989fc4fc633601197cdfa733fbce3f5c9ea2c8`, four post-merge gates passed.
**Source spec:** `docs/PR61_C10_Exact_Constitutive_Execution_Spec_v1.1_AUDITED.md`.
**Status:** DRAFT / IMPLEMENTATION IN PROGRESS. Do **not** merge until final-head CI and full theorem coverage are independently checked.

## Frozen mathematical target

For one predeclared Boolean descriptor `h`, compare the **same** infinite-path eventual-true property of every baseline/intervened canonical kernel:

`E_h = {w : ∃ N, ∀ t ≥ N, h(w t) = true}`.

The numerical query computes exact rational class-absorption values and
`f_K(x) = P_x(E_h)`, then calculates `κ_i = min_(x in BR) |f_K0(x)-f_Ki(x)|`
for **each** listed candidate `i`, with one fixed candidate over the entire original `B₁` comparison set, and `max_i κ_i`. This is not D0's finite-horizon hitting objective. Competing matrices each get their own BSCC/absorption decomposition.

The original Lean predicate is `RegimeSpecification.constitutiveMargin` on the already frozen typed `ConstitutiveComparisonSet`, regime descriptor, and `eventuallyObservedProperty`. The goal of C10 is to prove equality with that **original** real number, then produce an algorithmic optimizer with exact input-bound proof artifacts. Zero original margin refutes original uniform relative PR without an Exact-GR proof; a positive margin proves uniform strategic constitution only, until a separate original Exact-GR certificate is supplied. C9's support-only iff retains its literal convergence-mode condition.

## Existing verified substrate (unchanged)

- Original `PermanssonLean/`, original predicates, frozen paper v0.1.8, application schemas, pinned toolchain and old research modules are unmodified.
- D0: exact finite-prefix rational and genuine typed `Unit × Fin n` alpha/P/U realization, with fixed P/U and finite-menu semantics.
- C2–C8: actual finite canonical class-selection/occupation/event and original relative PR/support proofs.
- C9: finite-menu support certificates and **noncomputable mathematical** maximum over original margins; graph-only rational/typed adapter.

## New numerical Python implementation

- `verification/research/c10_exact_execution.py`: rejects untrusted noncanonical rational strings, floats, invalid/empty/non-stochastic matrices, incomplete descriptor and comparison sets, inconsistent repeated indices. Outputs deterministic normalized input, exact rational BSCC sets, complete absorption class weights, eventual-true event probabilities, candidate pointwise effects, full comparison minima, attaining starting states, ties, deterministic first-listed global winner, and an input SHA-256. Strict-positive edges are preserved with no threshold.
- `verification/research/c10_verify_receipt.py`: **separate** DFS SCC/BSCC enumerator and exact boundary/harmonic equation checker. Validates mass partition, class-good flags, all event and original `BR` values, every candidate, the whole maximin, tie completeness, input provenance fingerprint, and status. It does not trust the producer's inversion or graph list. It is an independent Python numerical check, **not a Lean formal proof**.
- `verification/research/c10_golden.py`: reproducibly emits the six-state exact rational input and receipt in temporary output. The original C6/C8/C9 matrix patterns are independently re-expressed as frozen exact tables, with full/half/tiny/identity/U-only/B-only margins `1`, `1/2`, `1/1000`, `0`, `0`, `0`.
- `test_lane_c10_exact_execution.py` and `test_lane_c10_golden.py`: >100 new cases including omitted classes, corrupted Dirichlet values, mixed-label cycles, exact tiny positive edges, complete-menu adversaries, complementary interventions where `max min=0 < min max=1`, tampering and deterministic golden reproduction.

Run from the repository root:

```sh
python -m unittest discover -s verification/research -p 'test_*.py' -v
python verification/research/c10_golden.py /tmp/c10-golden
python verification/research/c10_verify_receipt.py /tmp/c10-golden/receipt.json
```

This numerical status is deliberately **not** asserted as a Lean/PR theorem. `NUMERIC_ALL_LISTED_MARGINS_ZERO` is a computed status; original relative PR exclusion follows after the input-to-original typed margin bridge is proved, not from arbitrary JSON alone.

## New Lean research source (staged proof obligations)

- `CheckedRationalInput`: decidable construction of actual proof-carrying rational Markov rows from typed exact finite inputs. External JSON/bytes decoding is outside this proof.
- `RationalSupportGraph`, `RationalBSCC`: exact rational positive edges, executable Warshall graph, deterministic computed bottom-class proposals and checks. The generic graph-to-abstract-class completeness equivalence is a separate theorem.
- `FiniteAbsorptionDirichlet`, `RationalEventuallyObserved`: precise finite rational boundary/harmonic verification and all-true-class event sums. Algebraic soundness is distinct from true infinite-path absorption equality.
- `RationalConstitutiveMargin`, `ExecutableConstitutiveSelection`, `ConstitutiveCertificateCheck`: original comparison-set style maximin, exact rational checker and chosen-member dominance; no accidental max/min inversion.
- `RationalAbsorptionSolve`: total exact adjugate/determinant Cramer reference candidate; **a generic proof of nonsingularity and acceptance is still required**. Do not infer universal correctness from a terminating rational division by a possibly zero determinant.
- `ComputableSixStateFixtures`: reified C6/C8/C9 exact rational matrix data, entrywise equality, and a genuinely typed B-only alpha-only intervention preserving P/U.
- `ExactSixStateC10Execution`: proposed kernel-checked finite numerical instance using **kernel reduction** (`decide`, never `native_decide`) for exact half/tiny margins; this may require compilation-performance optimization. Its compiled status must be checked in CI.
- `ConstitutiveEndToEndCertificate`: original-definition theorems for zero/positive original margins and the independent exact-GR promotion gate. These do not discharge the numerical-to-native path-law equality by assumption.

## Dirichlet uniqueness: proposed full Lean proof target

Let `R` be the exact union of all bottom recurrent classes in a finite
stochastic graph and `T` its complement. Every state in `T` has a finite
strict-positive-edge path to `R`. For a real-valued function `d` satisfying
`d=0` on `R` and `d(x)=Σ_y K(x,y)d(y)` on `T`, take its global maximum `M`.
If `M>0`, any maximizer lies in `T`. The stochastic convex combination
identity forces *every positive-edge successor* of that maximizer also to
carry `M`; otherwise its average would fall below `M`. Propagating along
an existing positive path into `R` contradicts the zero boundary there.
Thus `M≤0`. Repeating with `-d` gives `d≥0`, hence `d=0` everywhere. The
Dirichlet solution is unique; the associated rational matrix is invertible
because its homogeneous kernel is zero on the finite-dimensional space.

Separately, the *actual* canonical infinite-path bottom-class selection
probabilities satisfy these Dirichlet equations by the genuine Markov
first-step law and almost-sure eventual bottom-class entry (already proved
in C2). Therefore uniqueness identifies exact rational Cramer solutions
with actual infinite-path absorption weights. C7 then identifies the
all-true-class sum with the fixed eventual-observation event probability.

**Audit status:** This is a valid paper-level argument and the required
formalization roadmap; it is **not** presently a compiled Lean theorem. Its
status must not be silently promoted by `checkDirichlet` accepting a table.

## Mandatory C10 completion gates

**Do not certify the full C10 claim unless all are present in actual compiled Lean source:**

1. Executable graph reachability iff rational `ReflTransGen`; complete BSCC enumeration ↔ the **actual** abstract finite-kernel recurrent classes.
2. Total exact rational Dirichlet reference solve, with a proof the determinant cannot vanish for every valid nonempty stochastic matrix, and a theorem that the reference certificate **always passes** the checker.
3. Native canonical infinite-path first-step/absorption characterization and a universal **numeric = genuine path-law** theorem, without assuming an external `exact_values` field or copying a baseline selector after intervention.
4. Original typed alpha/P/U **numerical** event-value correspondence for baseline and every listed intervention, complete descriptor/`B₁` index transport, actual original `constitutiveMargin` equality and deterministic global optimizer.
5. The original six-state test with separately proved exact half/tiny numeric margins and genuine B-only zero-margin typed proof.
6. Full exact-head and synthetic-merge Research Lean three-axiom audit, ≥417 cumulative independent tests, D0 golden and source firewall, Original Lean, executable verification, App contract (Ubuntu + Windows), complete direct research imports, exact-head Codex review, author-controlled merge.

**Known incomplete proofs must be reported by name.** Passing arithmetic Python tests, a computationally checked Dirichlet equation, or a green Original Lean workflow is not the same as full formalized mathematical closure. No external causal identification or independent scholarly peer review is claimed.

**Critical trust gate:** `native_decide` introduces `Lean.ofReduceBool` and violates the repository’s three-axiom allowlist. All new numerical proof terms must use kernel-checked reduction or algebraic tactics instead; native computation may produce candidate data but cannot certify it via `native_decide`.