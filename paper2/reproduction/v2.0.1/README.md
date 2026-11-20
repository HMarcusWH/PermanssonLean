# New exact reproduction addendum for manuscript v2.0.1

[Publication hub](../../README.md) · [Reviewed edition](../../v2.0.1/README.md) · [Addendum manifest](REPLAY_MANIFEST.json) · [Observed results](REPLAY_RESULTS.json)

This separately identified addendum provides newly written programs for the
**43 quantitative and 20 specialized outputs** retained in the reviewed source
ZIP. It closes the missing-command gap while preserving the original PDF, ZIP,
result records, indexes and publication manifest. It does not recover the
missing original review programs or authenticate their original execution.

## Run the reproductions

Use Python 3.10 or later; only the standard library is required. From the
repository root:

```bash
python3 -B paper2/reproduction/v2.0.1/replay.py
```

The default archive path is resolved from the program's own location, so an
absolute path to `replay.py` works from another working directory. For a copied
addendum outside the repository, supply the exact reviewed source ZIP:

```bash
python3 -B /absolute/path/to/replay.py --archive /absolute/path/to/Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip
```

Use `--full` to print every computed value, comparison, source reference and
control. Use `--output /absolute/path/to/new-replay-results.json` to retain the
same complete JSON in a **new** file. The output's parent directory must exist;
an existing file is refused. The programs do not extract or alter the archive.

Exit status 0 means all retained-output comparisons and added controls passed;
1 means a calculation or control did not match; 2 means an identity, structure
or file precondition failed. The manifest records an observed run and source
hashes; a reader's new execution supplies its own result.

## What is calculated

| Program | Retained outputs | Calculation scope |
| --- | ---: | --- |
| [quantitative_replay.py](quantitative_replay.py) | 43 | Boolean and conditional destinations; dependent history laws and event TV; actual two-step Q04 orbits; four exact Q05 Bellman systems; row errors and discount budgets; retained mass and escaping-mass transport cost |
| [specialized_replay.py](specialized_replay.py) | 20 | Rational secular derivatives with normalization; three-moment legalization; Gram gaps, finite quadratic forms and a masking counterexample |
| [replay.py](replay.py) | Comparison runner | Archive/member identity, exact names/order, actual/expected comparisons and explicit evidence boundaries |

The two arithmetic modules use exact `fractions.Fraction` operations and do
not read archived answers. The runner first checks the ZIP's byte count and
SHA-256, then reads the two result members from those verified bytes and checks
their separate hashes. Every newly computed string must equal both the saved
`actual` and `expected` strings. Saved `passed` flags are reported but do not
determine the new outcome. Missing, extra, duplicated or reordered records are
rejected.

The **12 additional arithmetic controls** exercise deliberately incorrect
shortcuts or separate identities. They address state/patch confusion, lost
signed interaction, false history independence, a baseline-only treatment
budget, incorrect update chronology, initial mismatch, shell normalization and
scaling, moment signs, projection, positive-background masking and parallel
vectors. **Five additional runner controls** detect altered values and
missing, extra or duplicate records. These controls are separate from the
original 63 outputs; they do not increase the retained review count.

## Fixture provenance and limits

The reviewed quantitative formulas and fixtures appear in Appendix F, Section
13 and Appendices G, A and H. The newly selected endpoint witnesses use
β = 1/3 when η = 0, and η = 1/20 when β = 0; those free choices were not
preserved in the original result records. The single-unit-defect witness uses
one unit defect followed by a zero tail. These choices reproduce the stated
identities and do not identify missing historical inputs.

The specialized records likewise omit their original shell and Gram inputs.
This addendum declares new source-consistent rational fixtures: the shell uses
`T = [[0,2],[2,3]]`, the first-coordinate predecessor, `H = 0`, shift `−1`,
and shell vectors `(0,2)` and `(0,1)`; the Gram example uses `x = (1,2)`,
`y = (3,−1)`, `c = 2`, and background `P = 2c yyᵀ`. Its moment tuples are
encoded in the retained result names. Section 26 and Appendix M supply the
formulas. The code and full result JSON record these inputs explicitly.

Matching the 63 scalar/list outputs supplies a runnable finite reproduction.
It does not establish equivalence to an unavailable original implementation,
prove the general path-law or analytic theorems, compile Lean, identify an
empirical model, grant independent acceptance or approve a release.

## Artifact identity

The immutable source ZIP is
`Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip`:
**7,406,118 bytes**, SHA-256
`d66d9ac3a8e8dac1a15ecc5e7703569f5cbe3c29121a97d9cfe6d148546e8a18`.
Its first publication commit remains
[`5160a32eecec9d5f17713416f7f58ec2df67e744`](https://github.com/HMarcusWH/PermanssonLean/commit/5160a32eecec9d5f17713416f7f58ec2df67e744).

The [addendum manifest](REPLAY_MANIFEST.json) hashes the three programs, this
README and the retained new result. It also records the original ZIP/member
identities, the observed execution environment and validation scope. It does
not hash itself or assert its own unknown containing commit. The original
[publication checksum set](../../v2.0.1/SHA256SUMS) continues to identify the
ten reviewed artifacts/index copies independently of this later addendum.
