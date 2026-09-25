# Runs 17–30 rerun instructions

[Verification guide](../../README.md) · [Windows/package instructions](../WINDOWS_RERUN_INSTRUCTIONS.md)

This directory is the repository mirror of the portable v0.1.7 post-proofread destructive suite.
The byte-identical frozen evidence archive and Windows-safe runnable ZIP remain
external release artifacts identified by [provenance records](../../../provenance/README.md).

<a id="requirements"></a>

## Run from the repository root

Use the [Python 3.13 environment](../../../docs/GETTING_STARTED.md#setup). Repository
CI pins NumPy 2.5.3 in [requirements.txt](requirements.txt).

```bash
python -m pip install -r verification/destructive/suite/requirements.txt
python verification/destructive/suite/run_all.py
```

Already in `verification/destructive/suite/`? The equivalent commands are:

```bash
python -m pip install -r requirements.txt
python run_all.py
```

Expect Runs 17 through 30 to report **PASS** and exit 0: fourteen numbered runs.
Fresh logs go to `logs/` and the runner summary to `results/v17_run_summary.json`,
both relative to this suite. The [historical report](POST_PROOFREAD_FULL_TEST_REPORT.md)
records **3240/3240 passing checks** under the strengthened post-proofread contract;
it is not a substitute for inspecting the results of a new execution.

## Repository adaptation

The release-package portable ZIP bundles the exact v0.1.7 control TeX used by historical Run 30. To keep the Git repository source-oriented, that historical full TeX is not duplicated here. Instead:

- `scripts/common.py` derives the suite root from its own location;
- `run_all.py` provides a one-command entry point;
- Run 30 uses the exact full v0.1.7 TeX when it is present under `inputs/`;
- otherwise Run 30 falls back to `inputs/V017_SOURCE_CONTRACT.txt`, which freezes only the exact source strings consumed by the historical Run 30 assertions;
- the frozen archive remains the authoritative evidentiary record for the historical full-source audit.

The mathematical tests, numerical thresholds, mutation cases, and expected claim boundaries in Runs 17–29 are unchanged. The repository adaptation to Run 30 changes only how historical source/control evidence is supplied to CI.
Read the [input-fixture boundary](inputs/README.md) before interpreting its source audit.

## Historical material

The legacy `rerun_legacy_*.py` utilities and `rerun_baseline_postproofread.py` are
archival helpers requiring historical source workpacks; `run_all.py` does not call
them. Compact records under `results/` are not reconstructions of missing sources.

[V0_1_7_SKETCH_SPEC.md](V0_1_7_SKETCH_SPEC.md) preserves an earlier candidate-upgrade
plan. It is not the current completion ledger. Use the
[final formalization map](../../../docs/FORMALIZATION_MAP.md) and
[current research roadmap](../../../docs/FUTURE_THEORY_ROADMAP.md) for those roles.
