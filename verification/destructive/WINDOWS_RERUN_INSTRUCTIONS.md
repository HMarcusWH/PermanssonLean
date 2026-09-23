# Windows-safe destructive-suite rerun

The byte-identical evidentiary archive remains a **release artifact** rather than a duplicated Git blob:

`Permansson_v0.1.7_POST_PROOFREAD_TEST_SUITE_FROZEN.zip`

For an executable rerun on Windows, macOS, or Linux use the companion **release artifact**:

`Permansson_TestSuite_v0.1.7_WINDOWS_SAFE.zip`

The Windows-safe derivative contains the same portable Runs 17-30 material and exact v0.1.7 control TeX used by the prior portability-fixed derivative, but its archive root is shortened to `suite/` and it is written with DOS-compatible ZIP metadata.

Recommended workflow:

1. Extract the Windows-safe archive.
2. Open a terminal in the extracted `suite` directory.
3. Run `python -m pip install -r requirements.txt`.
4. Run `python run_all.py`.

Expected result: Runs 17-30 return **14/14 PASS**.

No theorem, test threshold, mutation case, expected claim, paper file, Lean source, or frozen evidentiary archive was changed by this packaging repair.

The unpacked runnable source is committed in this repository under `verification/destructive/suite/`; use the ZIP only when reproducing the packaged Windows-safe distribution.
