# Permansson executable verification

This directory is the executable verification companion to the Lean formalization and the v0.1.8 paper.

The layers are intentionally separate:

- `destructive/suite/` — unpacked Python source for the destructive/regression suite used by numbered Runs 17–30.
- `destructive/Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE_FROZEN.zip` — byte-identical evidentiary archive retained from the v0.1.7 post-proofread release.
- `destructive/Permansson_TestSuite_v0.1.7_WINDOWS_SAFE.zip` — portable runnable derivative with the exact v0.1.7 control TeX and short Windows-safe archive paths.
- `baseline/` — earlier available Python validators and compatibility controls that fed the historical regression layer.
- `v0.1.8_release_gate/` — Runs 31–34. Runs 31–33 are historical release gates; Run 34 is the editorial-final v0.1.8 gate.
- `lean/` — paper-to-Lean crosswalk and immutable formalization provenance.
- `repository_gate.py` — repository-level synchronization/integrity check.

The Python tests provide executable falsification and regression evidence. They are not proof objects. The Lean development machine-checks the encoded mathematical claims inside its stated formal scope. Neither layer certifies empirical inputs, causal identification, source provenance quality, statistical adequacy, or literature priority.

## Reproduce the current destructive suite

```bash
python -m pip install -r verification/destructive/suite/requirements.txt
python verification/destructive/suite/run_all.py
```

Expected result: numbered Runs 17–30 return **14/14 PASS**.

## Reproduce the editorial-final release gate

Run 34 additionally requires `pdflatex`, `pdfinfo`, and `pdftotext`:

```bash
python verification/v0.1.8_release_gate/run34_editorial_final_release_gate.py
```

Expected result: **58/58 PASS**.

## Repository integrity gate

```bash
python verification/repository_gate.py
```

This checks the final PDF/TeX and destructive-suite hashes, source presence, version metadata, Appendix-E scope boundary, release-gate presence, and Python syntax.

## Historical source boundary

The exact v0.1.7 frozen archive records the historical v0.1.6/earlier execution ledgers and logs. Where source scripts are available in the project materials they are committed under `baseline/`. The repository does not reconstruct unavailable historical Python source from logs; the frozen archive remains the evidentiary record for those executions.
