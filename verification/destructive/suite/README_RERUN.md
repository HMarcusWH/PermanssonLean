# Portable rerun instructions

This archive is a portability-fixed derivative of the frozen v0.1.7 post-proofread destructive suite.
The original frozen evidence archive is preserved separately in the v0.1.8 release package.

## What was fixed

- `scripts/common.py` now derives the suite root from its own location instead of requiring `/mnt/data/Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE`.
- Run 30 reads the exact v0.1.7 control TeX bundled under `inputs/` instead of requiring `/mnt/data/_v017_build/...`.
- The exact control TeX was copied byte-for-byte from the v0.1.8 release package provenance folder.
- `run_all.py` provides a one-command entry point.

No mathematical test logic, numerical thresholds, mutation cases, or expected claims were changed.

## Requirements

Python 3 and NumPy.

```bash
python -m pip install -r requirements.txt
python run_all.py
```

Expected result: Runs 17 through 30 all return PASS (14/14 numbered runs; 3240/3240 checks in the frozen post-proofread suite).

The legacy `rerun_legacy_*.py` utilities are archival helpers for rebuilding the older v0.1.6 source executions and still require the historical source workpack that generated those records. They are not invoked by `run_all.py`; the required v0.1.6 control ledgers are already included in `results/`.
