# Building the separate Permansson research library

[Documentation index](README.md) ·
[Next-generation architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md) ·
[Current formalization map](FORMALIZATION_MAP.md) ·
[Research CI](../.github/workflows/research-lean.yml)

**Status:** Research library with CQ-1 Part 1 proofs merged in PR #36; CQ-1
Part 2 finite constitutive certificate merged in PR #37. CQ-1 Part 3
certificate transport remains a separate research candidate until CI passes.
Grammar-robust, multiple-limit and reverse-solver lanes remain proposed.
Nothing here changes the immutable v0.1.8 mathematical snapshot.

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

## How to add the first mathematical extension

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
The follow-on research work is the conditional certificate-transport theorem:
[CQ-1 Part 3](CQ1_CERTIFICATE_TRANSPORT.md). The D0 frozen fixed-intervention-menu solver is scoped in
[D0 frozen menu](D0_FROZEN_MENU.md) as an independent research lane.

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
