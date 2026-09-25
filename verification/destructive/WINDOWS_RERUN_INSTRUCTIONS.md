# Windows-safe destructive-suite rerun

[Verification guide](../README.md) · [Python setup](../../docs/GETTING_STARTED.md#setup)

## Normal repository checkout

You do not need a ZIP to run the repository's suite. Set up Python 3.13, open a
terminal in the repository root, and run:

```powershell
python -m pip install -r verification/destructive/suite/requirements.txt
python verification/destructive/suite/run_all.py
```

When activation is unavailable on Windows, replace `python` with the direct
virtual-environment interpreter described in the setup guide. These same repository
commands work in a configured Linux/macOS shell.

Expect fourteen PASS lines for Runs 17–30 and exit 0. See the
[suite guide](suite/README_RERUN.md) for logs and the compact Run 30 source fixture.
Do not use archival `rerun_legacy_*.py` helpers as the normal entry point.

## Reproduce the packaged distribution instead

This is a separate task requiring an externally supplied release artifact:

`Permansson_TestSuite_v0.1.7_WINDOWS_SAFE.zip`

The byte-identical evidentiary archive is a different file:

`Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE_FROZEN.zip`

Both are identified in the [release metadata](../../docs/releases/v0.1.8.json) and
[provenance records](../../provenance/README.md); they are not duplicated Git blobs.
Check the supplied archive's hash before using it. A GitHub source ZIP is not either
of these release artifacts.

Extract the Windows-safe archive and open a terminal in its short `suite/` root:

```powershell
python -m pip install -r requirements.txt
python run_all.py
```

Expect Runs 17–30 to return **14/14 PASS**. Use the package's own requirements when
reproducing that distribution and record the environment; do not silently describe
a different environment as the CI-pinned repository run.

The Windows-safe derivative uses short paths and DOS-compatible ZIP metadata and
includes the exact v0.1.7 control TeX for the packaged source audit. The repository
uses a compact source-contract fallback unless that full control is supplied.
The frozen evidence archive remains unchanged; a packaging repair does not change
theorems, thresholds, mutation cases, or expected claims.
