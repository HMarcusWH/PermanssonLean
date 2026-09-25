# README-inward documentation review

[Documentation index](README.md) · [Contribution guide](../CONTRIBUTING.md)

Review date: **25 September 2026**. Repository baseline:
`7cbf849eeb8d818fba6b20aa419e364b9399c944`, after merge of the application-standard PR.
This is a usability/navigation review, not a new mathematical or empirical audit.

## Scope and disposition

| Area reviewed | Treatment |
|---|---|
| Root README | Put reader goals and the first application command before detailed proof/release references; retain links to the full coverage and provenance authorities. |
| Application README, standard, CLI reference, schemas and tests | Add setup, output interpretation, schema navigation, and a proposal-then-validation walkthrough. Preserve the standard, CLI semantics, schemas and code. |
| Seven synthetic bundles | Review the fourteen specification/argument files through their four shared text bodies and the generator; keep all evidence bytes, manifests, hashes and expected outcomes unchanged. |
| Paper guide and two supporting-paper guides | Add reading order and links without revising paper content or specialized-scope claims. Leave the supporting-paper guides and PDFs unchanged. |
| Formalization map and future-theory roadmap | Retain the expert ledger and research boundaries; the new index distinguishes current coverage from historical milestone narration. |
| Verification README, suite guide and Windows instructions | Separate clone commands from external-package reproduction; specify environments, working directories and expected outputs. |
| Historical sketch, input-fixture guide, test reports and Runs 31–34 records | Preserve the records; add surrounding navigation and explain which are historical rather than current instructions. |
| Lean crosswalk/provenance and release hash/build records | Add entry-point guides; keep the selected 17-entry crosswalk distinct from the full ledger and historical CI distinct from a new run. |
| Citation, version metadata and requirements | Check documentation against their separate roles; do not synchronize unrelated version numbers or change the records. |

## Concrete issues addressed

The prior root page led with internal proof milestones and hashes but did not give
a new user a clone/environment/expected-result path. Application instructions
assumed Python setup and did not guide users from a synthetic example to a separate
practice copy. Some deeper directories opened onto bare schema or evidence files
without a reading guide.

The example README described `build_examples.py` as comparing byte-for-byte. Its
read-only comparison actually uses decoded text; exact byte checks live in the
unit tests. The revised guide states both accurately. It also describes the current
`-text` protection for raw bundle evidence instead of implying blanket LF conversion.

Suite commands needed an explicit working directory and the CI-pinned environment.
Release-gate instructions needed to identify the missing external assets and the
repository/package PDF filename difference. The reader guides now distinguish a
GitHub source archive from the named historical distribution rather than promising
an unverified download location.

## Preservation boundary

Only Markdown is changed or added. The mathematical PDF/TeX, Lean source/imports,
package pins, application schemas and implementation, fixture files, numerical
suite, CI workflows, citation/version metadata, historical reports and release
hashes are unchanged. Navigation wrappers are not new evidence.

The paper and existing contract remain the authority. The glossary and onboarding
guide simplify navigation, not definitions or admissibility. No historical case is
reclassified and no future-theory lane is promoted to a theorem or certificate.

## Verification record

Check introduced relative links and anchors against the proposed tree, review the
Markdown rendering, and run the unchanged application tests, example regeneration,
application gate, repository gate and normal CI on the documentation head. Keep
actual current-head results in the documentation PR discussion, not in the frozen
historical reports.

Local environment limitations must remain explicit: a source/command review is not
execution of a fresh Lean build, dependency installation, or external-package Run
34. Report only the commands actually run and the CI results actually observed.
