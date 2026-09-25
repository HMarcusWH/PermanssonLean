# Paper and supporting theory

[Repository home](../README.md) · [Documentation index](../docs/README.md) · [Glossary](../docs/GLOSSARY.md)

This directory contains the manuscript associated with the **Permansson Regimes v0.1.8** formalization companion and repository-hosted copies of the author's internal supporting papers cited by the manuscript.

## Canonical v0.1.8 manuscript

- [Editorial-clean submission-final PDF](Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_EDITORIAL_CLEAN_2026-09-23.pdf)
- [TeX source](Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_2026-09-23.tex)

The PDF is the final editorial-clean 23 September 2026 artifact identified in the release metadata by SHA-256:

`24f7dd43c8996b6fc8bedf708704969ba2124e159783bbd2ded45db61525df54`

The checked-in TeX source is byte-checked by `verification/repository_gate.py` against the frozen final-TeX SHA-256 even though the repository filename is shorter than the release-package artifact name.

## Suggested reading order

For the framework's purpose and limits, start with Sections 1–2. For definitions,
read Sections 3–5 in order: typed process, Generated Regime, then strategic
constitution. Section 6 treats Paper-I recovery; Section 7 treats representation
and interventions. Sections 10.5–10.7 describe application certification, and
Section 12 states failure modes and claim boundaries.

Appendix C gives the applied workflow. Appendix D records formalization and release
provenance. Appendix E is specialized supporting material, **not** part of the
universal discrete-core completion claim. The supporting papers below are not
prerequisites for trying the [application-format example](../docs/GETTING_STARTED.md).

To compare paper statements with proofs, use the
[full theorem/definition ledger](../docs/FORMALIZATION_MAP.md#source-to-lean-theorem-and-definition-ledger).
To prepare a report, use the [Application Standard](../application/README.md), not
the mathematical PDF as a substitute for the JSON/CLI documentation.

## Internal theoretical lineage

### Foundational

[**Foundational supporting theory**](supporting/foundational/README.md) contains Hermansson (2026a), the Paper-I / EGR predecessor that v0.1.8 embeds and generalizes.

### Specialized Appendix E theory

[**Specialized supporting theory**](supporting/specialized_theory/README.md) contains Hermansson (2026b–f), the five Weil–CCM working papers referenced as specialized theorem-transfer architectures in Appendix E.

These specialized papers are not universal GR/PR theorems. The manuscript requires a natural Permansson subclass, satisfaction of the specialized hypotheses, and a direct theorem to establish the transfer before such a result belongs to the general framework.

## Release-lineage boundary

The supporting-paper PDFs were added to the Git repository after the v0.1.8 release package was frozen. They are provided for reader convenience and citation transparency. Their inclusion here does **not** modify the release-package hashes, the frozen destructive-test archives, or the immutable Lean formalization snapshot.

The paper, Lean package, and application standard have distinct version identities.
Use [CITATION.cff](../CITATION.cff) for the scholarly companion and record the exact
commit for repository implementations. The [provenance guide](../provenance/README.md)
explains filename differences between this directory and the external release package.
For the historical PDF/TeX build audit, follow the
[package-level Run 34 instructions](../verification/v0.1.8_release_gate/README.md);
a fresh PDF build need not reproduce the distributed PDF's byte hash.
