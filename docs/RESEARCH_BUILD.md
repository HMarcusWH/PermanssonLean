# Building the separate Permansson research library

[Documentation index](README.md) ·
[Next-generation architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md) ·
[Current formalization map](FORMALIZATION_MAP.md) ·
[Research CI](../.github/workflows/research-lean.yml)

**Status (13 October 2026):** The separate research library has merged
CQ-1 (PRs #36–38), D0/D1 (PRs #39–50), finite partition-grammar Lane B
(PR #51), absorbing-class Lane C1 (PR #52), finite recurrent-class
occupation laws Lane C2 (PR #53), original finite Exact GR iff
classification Lane C3 ([PR #54](https://github.com/HMarcusWH/PermanssonLean/pull/54))
and exact six-state stationary coordinates/periodic marginals Lane C4
([merged PR #55](https://github.com/HMarcusWH/PermanssonLean/pull/55)).
C4 was verified on the final PR head and synthetic merge and again on
the actual main merge commit `68bbb8025c931d0519621e4a827a50250945ddb7`;
all four post-merge workflows passed (see PR #55).

**Merged C5:** [PR #56](https://github.com/HMarcusWH/PermanssonLean/pull/56)
formally proved the sharp finite *positive-atom* observed family, exact
coverage/no-spurious iff, positive basin witnesses, exact class-weight
aggregation and the conservative C3 singleton Exact GR bridge. Its
final verified PR head was
`916520de307694ee90e31b6c5e0ddf8ae3ef34a8`, and it merged to main
as `ea821bb253cd25d038a4454ee4d833232c8d7b19`. The proof-source
gate audited **2,760 declarations** with the standard 3-axiom allowlist,
**167/167 research regressions** and **240** direct imports; all four
final-head PR and post-merge main workflows passed. The review remains
assistant-conducted and is not independent scholarly peer review.

**Merged C6:** [PR #57](https://github.com/HMarcusWH/PermanssonLean/pull/57)
established an actual typed alpha-only observed-event disruption, margin 1 and
original uniform relative PR, together with the changed sharp observed limit
family. It merged at `b6e91f9badce1a2292a0ef6f1be8d7922c167cdf`
after all four final-head CI workflows passed, as did the post-merge workflows.
This does not amount to independent scholarly peer review.

**Merged C7:**
[PR #58](https://github.com/HMarcusWH/PermanssonLean/pull/58)
proves the canonical eventual-true event iff good recurrent-class selection
a.s. and the exact original finite typed PR criterion. Its last mathematical
head `24024033f034a9cf1693e24177a183fe0c29dc9c` passed all four workflows,
including [Research Lean #38397469362](https://github.com/HMarcusWH/PermanssonLean/actions/runs/38397469362)
and **217** independent exact rational regressions, the transitive axioms audit,
251 direct imports and source firewall. C7 merged into `main` as
`784aaa2b5a74efa1a827de2fcbf6b81b30d29de4`. The merge preserved the verified C7 commit history;
post-merge CI results must be reported separately, not presumed.

**C8 research draft / mathematical source not yet certified:**
[PR #59](https://github.com/HMarcusWH/PermanssonLean/pull/59) is the
research-only support-graph extension of C7, proposing exact positive-edge
G1–G7 classifications, genuine same-support typed intervention witnesses and
50 additional exact-rational regression cases. See the
[C8 support-graph ledger](LANE_C8_SUPPORT_GRAPH_CONSTITUTION.md) for precise
hypotheses, open proof gates and original v0.1.8 boundary. C8 now follows
merged C7, but remains independently unverified and draft. Neither formal
proof certification nor CI constitutes empirical identification.

See the [C4 verified ledger](LANE_C4_SIX_STATE_PRECISION.md),
[C3 ledger](LANE_C_EXACT_GR_CHARACTERIZATION.md),
[C2 ledger](LANE_C_RECURRENT_CLASSES.md), and
[Lane B ledger](LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md).

The complete mathematical v0.1.8 formalization and the original paper stay
frozen. Green Lean CI for a research PR means its stated theorem obligations
compiled and its proof dependencies passed the axiom audit; it does **not**
automatically complete additional release witnesses or independent review.

## Why there are now two libraries

The existing `PermanssonLean` is the established discrete v0.1.8 formalization.
`PermanssonResearch` is a separate, non-default Lean library for proposed future
proofs. It may **import** established declarations, but it must not rewrite,
replace, reinterpret or weaken any original theorem or the core's verification
boundary.

The default Lake target remains exactly `PermanssonLean`.
The companion research target must be named explicitly in the build command.
Both libraries share the same repository-level pinned Lean toolchain and mathlib
manifest: Lean 4.34.0 / mathlib v4.34.0. Do not run `lake update` for routine
builds or import the OpenAI Math fork, whose inspected toolchain differs, without
a separate compatibility and proof-verification plan.

The unchanged immutable source snapshot is
`c018f79ea4ce46f4f679ad5bca254509778fc53c`.
The live repository may receive additional documentation, verification and
research-library files; that does not retroactively modify the snapshot.

## Directory contract

```text
lakefile.toml
lean-toolchain
lake-manifest.json
PermanssonLean.lean                  # original root; unchanged
PermanssonLean/                     # existing proofs; unchanged
PermanssonResearch.lean             # explicit research-library root
PermanssonResearch/
  Compatibility.lean                # compile-time bridge to existing definitions
.github/workflows/lean.yml          # original core CI; unchanged
.github/workflows/research-lean.yml # separate research CI
```

The `Compatibility.lean` module imports original strategic-regime and
finite-prefix TV declarations. It checks their names and provides one short
**wrapper of the already-proved held-world-primitive fact**. The wrapper is a
compatibility smoke test, not a new mathematical assertion, an empirical model,
a solver, or the first CQ-1 theorem.

## Reproduce locally

From the repository root (the directory containing `lakefile.toml`), install
the pinned Lean toolchain with elan, then run:

```bash
lake env lean --version
lake exe cache get
lake build
lake build PermanssonResearch
```

The first build continues to compile the original default formalization;
the second compiles the research root and every module imported by it. A passing
`lake build` alone does **not** establish that the research library compiled.

The dedicated [Research Lean workflow](../.github/workflows/research-lean.yml)
runs on pushes to `main` and PRs targeting `main` as well as manually.
Its lean-action `build-args: PermanssonResearch` builds the non-default research
root **before** the `axiom-audit-root: PermanssonResearch` audit.

**Subtle implementation detail:** lean-action's axiom-audit helper itself runs
plain `lake build` before reading the compiled environment. Since the default
target remains `PermanssonLean`, configuring only `axiom-audit-root` would
not be sufficient: the explicit research build must precede the audit.

The workflow also:
- runs plain `lake build` as a separate original-core regression;
- rejects any new research Lean module omitted from the root imports;
- rejects source proof placeholders or custom axiom declarations in the research
  source directory;
- audits transitive dependencies using axiom-audit's configured allowlist
  (`propext`, `Classical.choice`, `Quot.sound`).

An import-checking rule requires every research `.lean` file to be imported
**directly** by `PermanssonResearch.lean`, even when submodule imports also
would reach it transitively. This is deliberately stronger than ordinary
compilation and prevents future untracked modules from escaping the research
build. When adding `PermanssonResearch/Foo.lean`, add its `import PermanssonResearch.Foo`
to the research root in the same PR.

The new workflow does not change the original `Lean` check or its evidence.
The two workflows should be assessed independently.

## How to add a mathematical extension

Before writing code:

1. Read the [master research architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md)
   and the specific PR milestone. Keep its theorem statuses *proposed*.
2. Inspect exact declarations in the existing `PermanssonLean/` files, checking
   universe parameters, typeclasses, measurable-space requirements and imports.
3. Freeze the requested theorem's assumptions, quantifiers, inputs/outputs and
   explicitly forbidden stronger conclusions. Attach minimal adversarial examples.
4. Create a scoped file under `PermanssonResearch/`, add it to
   `PermanssonResearch.lean`, then build both targets and audit axioms.
5. Add appropriate formal negative examples and executable regression fixtures.
   Compile success never substitutes for the mathematical or empirical claim
   review; report exact declarations added and their proved types.
6. Preserve the original paper, `PermanssonLean.lean`, existing proof sources,
   the application schema and historical release/verification artifacts unless
   a separately reviewed release migration explicitly authorizes changes.

The first CQ-1 mathematical slice is documented in the
[CQ-1 finite-path bridge](CQ1_FINITE_PATH_BRIDGE.md). It connects bounded
finite-horizon observables to the original canonical path and property interfaces;
it does **not** complete the quasi-regime certificate.

The CQ-1 finite-path property and TV bridge is implemented in merged PR #36.
The CQ-1 finite constitutive certificate is implemented in merged PR #37:
[CQ-1 Part 2](CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md).
The certificate-transport theorem is merged in PR #38:
[CQ-1 Part 3](CQ1_CERTIFICATE_TRANSPORT.md). D0-A and D0-B are merged in
PRs #39–40. The fixed-intervention-menu solver, current conditional
rational-to-typed boundary and D0-C's now-proved
finite rational/canonical correspondence are scoped in
[D0 frozen menu](D0_FROZEN_MENU.md).

## Pass/fail acceptance checklist

- [ ] `lake build` passes for the original library at the PR head.
- [ ] `lake build PermanssonResearch` passes with the existing lockfile.
- [ ] `Research Lean` has a successful axiom audit for the research namespace.
- [ ] Every research source file is a direct import of the research root.
- [ ] Source-level placeholder and custom-axiom scanner passes.
- [ ] `Lean` (original) CI remains green at the PR head.
- [ ] The PR diff contains no changes to `PermanssonLean/`, `PermanssonLean.lean`,
  `paper/`, `application/`, historical release metadata or verification records.
- [ ] The immutable commit and frozen release hashes retain their original meaning.
- [ ] No new mathematical or empirical theorem is represented as proved solely
  by the scaffold.

If CI fails, report the specific job, log, committed head SHA and correction.
Do not assert that all gates passed because an earlier commit was green.

D0-B finite exact-matrix and selection proofs are scoped separately from
the D0-A frozen typed-intervention menu; consult [D0 frozen menu](D0_FROZEN_MENU.md)
for the scope boundary. No executable output is certified as an induced
strategic-world optimum without the missing representation bridge.

PR #40 D0-B proves an independent exact rational finite-word/recursion
identity and computable finite-menu argmax. Typed menu selection remains
conditional on the separate exact-value correspondence; do not count the
numerical Python rechecker as a formal proof of the software implementation.
