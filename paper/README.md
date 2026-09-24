# Paper and supporting theory

This directory contains the manuscript associated with the **Permansson Regimes v0.1.8** formalization companion and repository-hosted copies of the author's internal supporting papers cited by the manuscript.

## Canonical v0.1.8 manuscript

- [Editorial-clean submission-final PDF](Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_EDITORIAL_CLEAN_2026-09-23.pdf)
- [TeX source](Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.tex)

The PDF is the final editorial-clean 23 September 2026 artifact identified in the release metadata by SHA-256:

`24f7dd43c8996b6fc8bedf708704969ba2124e159783bbd2ded45db61525df54`

The checked-in TeX source is byte-checked by `verification/repository_gate.py` against the frozen final-TeX SHA-256 even though the repository filename is shorter than the release-package artifact name.

## Internal theoretical lineage

### Foundational

[**Foundational supporting theory**](supporting/foundational/README.md) contains Hermansson (2026a), the Paper-I / EGR predecessor that v0.1.8 embeds and generalizes.

### Specialized Appendix E theory

[**Specialized supporting theory**](supporting/specialized_theory/README.md) contains Hermansson (2026b–f), the five Weil–CCM working papers referenced as specialized theorem-transfer architectures in Appendix E.

These specialized papers are not universal GR/PR theorems. The manuscript requires a natural Permansson subclass, satisfaction of the specialized hypotheses, and a direct transfer theorem before such a result belongs to the general framework.

## Release-lineage boundary

The supporting-paper PDFs were added to the Git repository after the v0.1.8 release package was frozen. They are provided for reader convenience and citation transparency. Their inclusion here does **not** modify the release-package hashes, the frozen destructive-test archives, or the immutable Lean formalization snapshot.
