# Reviewed manuscript v2.0.1

[Second-edition publication hub](../README.md) · [Publication manifest](PUBLICATION_MANIFEST.json) · [Citation](CITATION.bib)

**Title:** Permansson Regimes: Structure, Intervention, and Computation Beyond Equilibrium  
**Author:** Marcus Hermansson  
**Status:** reviewed manuscript draft, second edition  
**Manuscript date:** 20 November 2026  
**Extent:** 218 physical PDF pages, 31 main sections, 16 appendices.

## Exact assets

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| [Permansson_Regimes_v2_0_1_Reviewed_Manuscript_2026-11-20.pdf](Permansson_Regimes_v2_0_1_Reviewed_Manuscript_2026-11-20.pdf) | 1,591,865 | `56a6ea1538e0a31f8555f4457b706e96d159ed96d3e1add7bba7b6847e4b3d17` |
| [Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip](Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip) | 7,406,118 | `d66d9ac3a8e8dac1a15ecc5e7703569f5cbe3c29121a97d9cfe6d148546e8a18` |
| [Permansson_Regimes_v2_0_1_Review_Report_2026-11-20.pdf](Permansson_Regimes_v2_0_1_Review_Report_2026-11-20.pdf) | 85,525 | `df19f6656e1a5ef3e1f66c9b6c28e9f60620f04a5dd86aa1c64030b55d217f71` |

These are the exact reviewed assets. The three files and seven index copies are listed in [SHA256SUMS](SHA256SUMS). From this directory run:

```bash
sha256sum -c SHA256SUMS
```

This checks byte identity against the published list. It does not establish a theorem, authenticate an external origin or replace independent review.

## Source identities

| Role | Commit |
| --- | --- |
| Mathematical source | [`c5a36cd6189e2a249d5f4bc11f31698917dc8b10`](https://github.com/HMarcusWH/PermanssonLean/commit/c5a36cd6189e2a249d5f4bc11f31698917dc8b10) |
| Documented pre-upload repository snapshot | [`f0dee1c11a20f96c9a11b380e942b9252e6ebe44`](https://github.com/HMarcusWH/PermanssonLean/commit/f0dee1c11a20f96c9a11b380e942b9252e6ebe44) |
| First commit containing these reviewed assets | [`5160a32eecec9d5f17713416f7f58ec2df67e744`](https://github.com/HMarcusWH/PermanssonLean/commit/5160a32eecec9d5f17713416f7f58ec2df67e744) |

The f0 snapshot is called a publication snapshot in the packaged concordance; it records the repository navigation state before the paper upload. It is not the commit containing this PDF. Later documentation and CI identities belong to their own records and are not inferred from any of these three commits.

## Inspect the reviewed indexes

| Exact index copy | Scope |
| --- | --- |
| [all_lean_written_connections.json](indices/all_lean_written_connections.json) | All 798 Lean files with grouped written connections and qualifications |
| [earlier_paper_written_obligations.json](indices/earlier_paper_written_obligations.json) | 51 earlier-paper obligations and 201 required-content entries |
| [manuscript_label_index.json](indices/manuscript_label_index.json) | All 603 literal manuscript labels |
| [source_citation_index.json](indices/source_citation_index.json) | All 538 printed source-anchor occurrences |
| [statement_index.json](indices/statement_index.json) | All 147 numbered mathematical items |
| [review_findings.json](indices/review_findings.json) | 58 internal draft revision findings |
| [revision_verification.json](indices/revision_verification.json) | Observed checks from the reviewed manuscript revision |

Each copy has the same bytes as its named member inside the source ZIP. The publication manifest gives every archive member name, byte count and hash. The larger repository, declaration, historical-source and Python inventories remain in the ZIP's `coverage/inventory/` directory; they are not a second independently reviewed source tree.

## Reproduce the manuscript

Extract the [source ZIP](Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip) into a fresh directory and read its `README.txt`. Its top-level directory is `Permansson_Regimes_v2_0_1/`. The packaged `build.sh` runs the manuscript index checks, included exact computations and TeX build; `python3 build_index.py` runs the index checks alone. The TeX toolchain and Python requirements are described in the package.

Run reproduction in that extracted directory and retain the result separately from the published PDF. A successful TeX build is not a full Lean build, and a different TeX environment is not guaranteed to produce byte-identical PDFs. The source ZIP's `MANIFEST.json` records the packaged files.

## Review and remaining obligations

The [review report](Permansson_Regimes_v2_0_1_Review_Report_2026-11-20.pdf) and [findings](indices/review_findings.json) cover the internal draft 2.0-to-2.0.1 revision. There were 389 supplementary exact checks (326 foundations, 43 quantitative and 20 specialized), separate 272 X1 checks and a separate 361,201-pair pricing grid check. These are distinct records with different scopes.

Section 31 and Appendix P retain the named X-01, F-02, A-01, A-04, E-05, Later Q1 and M-02 obligations, plus broader continuous-time, partial-observation, empirical and semantic-reconciliation limits. The earlier-paper ledger retains 192 substantive written treatments, five historical-delta-pending entries, one wording clarification and three incomplete historical reconciliations among its 201 entries.

The historical case dispositions remain 15 `PENDING`, 30 `PARTIAL_SCOPE` and 11 `SOURCE_PRESENT_REVIEW_PENDING`. This manuscript publication does not promote independent case acceptance, application report evidence fields or empirical identification. The [publication manifest](PUBLICATION_MANIFEST.json) records the edition and these boundaries in machine-readable form.
