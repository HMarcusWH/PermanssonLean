# Native proof replay of Lean candidates

The application emits Lean *source candidates*; it never runs Lean itself.
This page describes how a candidate is replayed on the pinned toolchain and
what a successful replay does and does not establish.

## Requirements

- The repository checkout with its pinned toolchain (`lean-toolchain`,
  Lean v4.34.0) and Lake configuration, both unchanged.
- A built Research library: `lake build PermanssonResearch` (or at least the
  bridge module the candidate imports).

## Steps

```bash
permansson-app <profile-command> request.json --output run
permansson-app lean-emit --family <family> request.json run/<receipt>.json --output cand
permansson-app lean-recheck --family <family> request.json run/<receipt>.json --candidate cand
lake env lean cand/Reified<Family>.lean     # from the repository root
```

From the repository root,
`python apps/permansson/application-successor/scripts/end_to_end.py --lean`
compiles and audits each candidate emitted during the packaged walkthrough.
Examples outside a family's reflection bound are reported as numeric-only;
the separate native C10/C11 examples also run in numeric mode. The flag does
not turn those examples into compiler replays.

`lean-recheck` re-derives the candidate from the original bytes and compares
the metadata and the Lean bytes exactly. Changed or mismatched bytes fail
before any compiler is involved; identical deterministic regeneration from
the same request and receipt bytes passes. The exit family also needs
`--region`.

## What a passing compile shows

Every candidate ends with `#print axioms` for each instance theorem. A
replay is accepted only if every theorem depends on nothing beyond
`propext`, `Classical.choice` and `Quot.sound`. That rules out `sorry`,
`admit` and any custom axiom. The candidate's theorems then hold for the
literal data in the file. For example:

- the declared value is Research's optimum over every real policy;
- the stated certificate exists;
- the cap is infeasible for every admissible policy.

The live replays in `verification/research/test_application_*_live_lean.py`
compile their concrete, source-bound fixtures this way. For single-line
**semantic mutations**, the tests require a source-local error at the
falsified obligation and exclude their listed unrelated compiler-failure
categories. Examples are an overstated value, a dropped control, a wrong
budget or a changed model row.

The diagnostic boundary is specific to each test family. Suites using the
shared `application_bridge_replay.assert_semantic_rejection` harness require
an error inside the targeted theorem and permit additional errors only in
theorem proof blocks. The finite-world suite instead requires an error
within seven source lines of the selected reflected-input proof field or
induced-atom theorem, after excluding its listed unrelated failures. Its
structure-field tests do not use the shared theorem-only boundary.

## What it does not show

- **Authentication.** The application does not run or attest the compiler,
  so candidate metadata keeps `lean_status=NOT_EXECUTED` and scientific
  reports keep `kernel_checked_proof=NOT_EXECUTED`.
- **Correspondence beyond the reflected data.** The theorems are about the
  literal tables in the file, which the byte recheck ties to the request.
  Whether the request describes a real system is out of scope.
- **Independent certification, Exact GR/PR, empirical identification or
  release acceptance.** These stay separate gates; see
  [`EVIDENCE_AND_RECEIPTS.md`](EVIDENCE_AND_RECEIPTS.md).

The [Research Lean workflow](https://github.com/HMarcusWH/PermanssonLean/blob/09c4341c22dfb22c750bfb02d4eaa4486782b77d/.github/workflows/research-lean.yml)
runs on pushes to `main` and pull requests targeting `main`. It builds the
research library and discovers the research test suite, including 24 live
application test files with 182 test methods at the linked source. Those
tests execute real compiler replays, axiom audits and semantic mutations
for their declared fixture instances; for example,
[the finite-world live tests](https://github.com/HMarcusWH/PermanssonLean/blob/09c4341c22dfb22c750bfb02d4eaa4486782b77d/verification/research/test_application_finite_world_live_lean.py).

A successful run therefore supports the library and the concrete fixture
instances it executed at that commit. It does not authenticate an arbitrary
user-generated output, transfer to a later commit, or change that output's
`NOT_EXECUTED` status. Read a success claim with its exact workflow run and
commit identity.
