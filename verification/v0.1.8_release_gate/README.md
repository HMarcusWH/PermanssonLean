# Historical release-package gates

[Verification guide](../README.md) · [Release provenance](../../provenance/README.md)

## Read this before running a script

These are release-package audits, **not normal-clone setup tests**. The repository
keeps their inspectable source and summary records. It does not include all assets
needed to repeat the original executions. Use
[repository verification](../README.md#repository-integrity-gate) for an ordinary checkout.

## Run 34: editorial-final package

[Run 34 source](run34_editorial_final_release_gate.py) targets the final 30-page
editorial-clean package. The [preserved report](RUN_34_EDITORIAL_FINAL_RELEASE_GATE_REPORT.md)
records **58/58 PASS**; the [JSON summary](RUN_34_RESULTS.json) is not the complete
per-check ledger, which remains in the external release package.

Exact package name:

`Permansson_v0.1.8_SUBMISSION_FINAL_RELEASE_PACKAGE_2026-09-23_EDITORIAL_CLEAN_WINDOWS_SAFE.zip`

Verify it against the [release metadata](../../docs/releases/v0.1.8.json). A GitHub
source ZIP is not this package. After extraction, open the inner package root
containing `paper/`, `provenance/`, and `verification/`. It must retain the package's
original paper filenames, frozen/portable destructive ZIPs, v0.1.7 control TeX, and
prior-gate records. Install Python and the external tools `pdflatex`, `pdfinfo`,
and `pdftotext` so they are available on PATH, then run the **package's own script**:

```bash
python verification/v0.1.8_release_gate/run34_editorial_final_release_gate.py
```

The package's PDF name omits the repository's `EDITORIAL_CLEAN` suffix; the
identity is established by its hash. Do not rename repository files, copy a
current paper into an older control slot, or regenerate frozen reports merely
to make an archival gate pass. Run this on a working copy of the extracted package:
the gate writes result/report files. A fresh PDF compilation is tested for text
identity by the gate, not assumed to reproduce the distributed PDF's byte hash.

## Runs 31–33: earlier stages

The [prior-gates guide](prior_gates_31_33/README.md) explains their original-layout
requirement. They refer to the pre-editorial 31-page artifacts, not the final PDF.
Their source is preserved for inspection and syntax checks, not execution in its
relocated repository directory.

| Stage | Preserved summary |
|---|---|
| Run 31 | [42/42 report](prior_gates_31_33/RUN_31_RELEASE_GATE_REPORT.md) |
| Run 32 | [45/45 report](prior_gates_31_33/RUN_32_FIGURE_CORRECTION_GATE_REPORT.md) |
| Run 33 | [50/50 report](prior_gates_31_33/RUN_33_FINAL_FIGURE3_LAYOUT_GATE_REPORT.md) |

Normal repository CI executes neither these older gates nor Run 34 against the
current checkout. It runs the numerical suite and synchronization checks and
syntax-checks the preserved scripts. Historical records retain their own scope.
