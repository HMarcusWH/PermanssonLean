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

`scripts/end_to_end.py --lean` performs these steps for every packaged
example, including the axiom audit described below.

`lean-recheck` re-derives the candidate from the original bytes and compares
the metadata and the Lean bytes exactly. A tampered or regenerated file
fails before any compiler is involved. The exit family also needs
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
compile each packaged example this way. They also require single-line
**semantic mutations** to fail inside the targeted theorem, with no
unrelated compiler error and no error outside a theorem block. Examples are
an overstated value, a dropped control, a wrong budget or a changed model
row.

## What it does not show

- **Authentication.** The application does not run or attest the compiler,
  so its outputs keep `lean_status=NOT_EXECUTED`.
- **Correspondence beyond the reflected data.** The theorems are about the
  literal tables in the file, which the byte recheck ties to the request.
  Whether the request describes a real system is out of scope.
- **Independent certification, Exact GR/PR, empirical identification or
  release acceptance.** These stay separate gates; see
  [`EVIDENCE_AND_RECEIPTS.md`](EVIDENCE_AND_RECEIPTS.md).

Exact-head GitHub CI (Research Lean) builds the bridge modules on every
push. A green run there is evidence for the library modules at that head,
not for any individual application instance.
