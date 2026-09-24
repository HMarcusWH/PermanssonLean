# Paper verification manifest — Permansson v0.1.8

## Release identity

- Paper: **Permansson Regimes: A General Framework for Strategic Dynamics Beyond Equilibrium**
- Version: **v0.1.8 editorial-clean submission final**
- Date: **23 September 2026**
- Final PDF SHA-256: `24f7dd43c8996b6fc8bedf708704969ba2124e159783bbd2ded45db61525df54`
- Final TeX SHA-256: `8235f6140bca33e7e3f0e96b4fd3aa2431c476fbdaf7c5d86d6d0b703ea54ed9`
- Frozen v0.1.7 post-proofread test archive SHA-256: `7ab578c928a2918e09846b9f1c425f5a6c07b5b5dd0a0c8728662eebcb69a15a`
- Windows-safe runnable destructive suite SHA-256: `864e2fec88b345194b0a9dc4ce9431e6a9a754eb88adea75fb8835b6244f41c3`
- Final Windows-safe release ZIP SHA-256: `66a13d3d4ea6854d38a6a32fe8b7946cbc290c62484b654dc02e0317039faf25`

## Repository-hosted paper stack

The repository now hosts the final editorial-clean PDF under `paper/` together with the checked-in TeX source and the author's internal papers cited by v0.1.8:

- `paper/Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_EDITORIAL_CLEAN_2026-09-23.pdf`
- `paper/Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.tex`
- `paper/supporting/foundational/` — Hermansson (2026a), the Paper-I / EGR predecessor.
- `paper/supporting/specialized_theory/` — Hermansson (2026b–f), the five specialized Appendix E supporting papers.

The checked-in TeX filename is shorter than the release-package artifact name recorded in `docs/releases/v0.1.8.json`, but `verification/repository_gate.py` hashes the checked-in source against the frozen final-TeX SHA-256 above. The supporting-paper PDFs were added after the release package was frozen and are repository-hosted citation aids; they do not alter any frozen release hash, test archive, or the immutable Lean snapshot.

## Formalization snapshot

- Immutable mathematical snapshot: `c018f79ea4ce46f4f679ad5bca254509778fc53c`
- Lean: `4.34.0`
- mathlib: `v4.34.0`
- Green CI run: `35808810682`
- CI job: `107015473604`
- CI checks: axiom audit, `lake build`, and rejection of `sorry`, `admit`, and source-level custom `axiom` declarations.

The cited commit is the mathematical source snapshot used by the paper. Later documentation, executable-test, packaging, and provenance commits do not alter that immutable theorem snapshot.

## Verification layers

The verification record has three deliberately distinct layers.

### 1. Executable destructive/regression layer

The frozen v0.1.7 post-proofread lineage records:

- 85/85 historical Python executions;
- 16/16 baseline compatibility checks;
- 3240/3240 checks across numbered Runs 17–30;
- a fresh portable rerun of Runs 17–30 with **14/14 PASS**.

The inspectable Python source for Runs 17–30 is now kept under `verification/destructive/suite/` in this repository. The exact frozen evidentiary ZIP remains identified by the SHA-256 above.

Repository CI reruns this layer on **CPython 3.13** with **NumPy 2.5.3** pinned in `verification/destructive/suite/requirements.txt`.

### 2. Deductive Lean layer

The companion Lean development machine-checks the discrete GR/PR mathematical core through Proposition 8.1. The paper-to-Lean declaration crosswalk and exact CI evidence are under `verification/lean/`.

### 3. Release/artifact layer

Historical release gates are preserved as source:

- Run 31: **42/42 PASS**
- Run 32: **45/45 PASS**
- Run 33: **50/50 PASS**

The editorial-final package gate is:

- Run 34: **58/58 PASS**

Run 34 checks final artifact hashes, editorial-clean scope separation, mathematical-surface continuity, Lean provenance, figure semantics, cold TeX compilation, PDF text identity, ZIP integrity, and preservation of the earlier release gates.

The full package-level Run 34 requires the release PDF and frozen ZIP artifacts. Repository CI therefore runs the unpacked destructive suite and a repository synchronization gate; the exact Run 34 source and final PASS record remain preserved under `verification/v0.1.8_release_gate/`.

## Editorial-final change boundary

The editorial-clean pass did **not** change the mathematical theorem surface. It removed development-history/release scaffolding from the theory body, consolidated formal-verification and artifact lineage in Appendix D, and moved the specialized finite-certificate/rigidity material to Appendix E.

The final TeX preserves the 34-equation tag sequence against the v0.1.7 control.

## Distribution packaging

Final package:

`Permansson_v0.1.8_SUBMISSION_FINAL_RELEASE_PACKAGE_2026-09-23_EDITORIAL_CLEAN_WINDOWS_SAFE.zip`

SHA-256:

`66a13d3d4ea6854d38a6a32fe8b7946cbc290c62484b654dc02e0317039faf25`

The Windows-safe layout retains short archive paths and leaves the byte-identical frozen evidentiary archive unchanged.

## Claim boundary

The machine-checked completion claim is the **discrete GR/PR mathematical core through Proposition 8.1**.

It does not extend to empirical validity, causal identification, provenance quality, statistical adequacy, literature priority, continuous-time/set-valued/nonautonomous extensions, or the specialized finite-certificate/rigidity material collected in Appendix E.
