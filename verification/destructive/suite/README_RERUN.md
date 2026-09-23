# Runs 17–30 rerun instructions

This directory is the repository mirror of the portable v0.1.7 post-proofread destructive suite.

The byte-identical frozen evidence archive and the Windows-safe runnable ZIP are release artifacts identified by SHA-256 under `provenance/v0.1.8/`.

## Repository adaptation

The release-package portable ZIP bundles the exact v0.1.7 control TeX used by historical Run 30. To keep the Git repository source-oriented, that historical full TeX is not duplicated here. Instead:

- `scripts/common.py` derives the suite root from its own location;
- `run_all.py` provides a one-command entry point;
- Run 30 uses the exact full v0.1.7 TeX when it is present under `inputs/`;
- otherwise Run 30 falls back to `inputs/V017_SOURCE_CONTRACT.txt`, which freezes only the exact source strings consumed by the historical Run 30 assertions;
- the frozen archive remains the authoritative evidentiary record for the historical full-source audit.

The mathematical tests, numerical thresholds, mutation cases, and expected claim boundaries in Runs 17–29 are unchanged. The repository adaptation to Run 30 changes only how historical source/control evidence is supplied to CI.

## Requirements

Python 3 and NumPy.

```bash
python -m pip install -r requirements.txt
python run_all.py
```

Expected result: Runs 17 through 30 all return **PASS** (14/14 numbered runs). The strengthened post-proofread suite records **3240/3240 passing checks**.

The legacy `rerun_legacy_*.py` utilities are archival helpers for rebuilding older v0.1.6 source executions and still require the historical source workpack. They are not invoked by `run_all.py`.
