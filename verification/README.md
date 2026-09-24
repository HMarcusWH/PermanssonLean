# Permansson executable verification

This directory is the executable verification companion to the Lean formalization and the v0.1.8 paper.

The final v0.1.8 editorial-clean PDF is committed under `paper/` and is checked by the repository synchronization gate against its frozen SHA-256. The frozen destructive-suite ZIPs and final release ZIP remain external release artifacts identified by the provenance records rather than duplicated Git blobs.

The layers are intentionally separate:

- `destructive/suite/` — unpacked Python source for the destructive/regression suite used by numbered Runs 17–30.
- The byte-identical frozen v0.1.7 evidentiary ZIP and the Windows-safe runnable ZIP remain release artifacts rather than duplicated Git blobs. Their exact SHA-256 identifiers are recorded under `provenance/v0.1.8/`, while the runnable source is unpacked here for inspection and CI.
- Historical v0.1.6 compatibility summaries and archival rerun helpers live under `destructive/suite/results/` and `destructive/suite/rerun_legacy_*.py`. The historical source workpack itself is not reconstructed from logs.
- `v0.1.8_release_gate/` — Runs 31–34. Runs 31–33 are historical pre-editorial release gates; Run 34 is the editorial-final v0.1.8 package gate.
- `lean/` — paper-to-Lean crosswalk and immutable formalization provenance.
- `repository_gate.py` — repository-level source/provenance synchronization check.

The Python tests provide executable falsification and regression evidence. They are not proof objects. The Lean development machine-checks the encoded mathematical claims inside its stated formal scope. Neither layer certifies empirical inputs, causal identification, source provenance quality, statistical adequacy, or literature priority.

## Reproduce the current destructive suite

Repository CI uses **CPython 3.13** with **NumPy 2.5.3** pinned in `requirements.txt`.

```bash
python -m pip install -r verification/destructive/suite/requirements.txt
python verification/destructive/suite/run_all.py
```

Expected result: numbered Runs 17–30 return **14/14 PASS**. The strengthened post-proofread contract contains **3240/3240 passing checks**.

## Repository integrity gate

```bash
python verification/repository_gate.py
```

This checks the committed final TeX hash, final artifact hashes recorded in metadata/manifests, Run 17–34 source presence, Appendix D/E scope separation, Lean snapshot identifiers, documentation synchronization, and Python syntax.

## Reproduce the editorial-final package gate

Run 34 is an exact **package-level** gate. It additionally requires the final PDF, the frozen and Windows-safe destructive-suite ZIPs, the v0.1.7 control TeX, `pdflatex`, `pdfinfo`, and `pdftotext` at the package-relative paths expected by the script.

From an extracted final release package:

```bash
python verification/v0.1.8_release_gate/run34_editorial_final_release_gate.py
```

Expected result: **58/58 PASS**.

The repository includes the final PDF but does not duplicate the frozen ZIP release artifacts, so Run 34 is preserved here for inspection and package reproduction rather than executed by normal repository CI. Repository CI instead runs Runs 17–30 plus `repository_gate.py`.

## Historical release gates

Runs 31–33 target the pre-editorial 31-page v0.1.8 artifacts and are preserved under `v0.1.8_release_gate/prior_gates_31_33/` together with their PASS records. They are historical evidence, not current-release gates. The relocated copies are inspection/syntax-preservation artifacts rather than in-place rerun entry points; see that directory's README for the original-layout requirement.

## Historical source boundary

The exact frozen v0.1.7 archive records the historical v0.1.6/earlier execution ledgers and logs. The repository does not reconstruct unavailable historical Python source from logs; compact compatibility summaries are explicitly labeled as summaries and the frozen archive remains the evidentiary record for those executions.
