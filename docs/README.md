# Documentation index

[Repository home](../README.md) · [Getting started](GETTING_STARTED.md) · [Glossary](GLOSSARY.md)

## Choose a reading path

**Reader:** start with the [paper guide](../paper/README.md), then use the
[glossary](GLOSSARY.md) and [claim boundary](APPLICATION_BOUNDARY.md). No software
installation is required to read the paper.

**Application user:** follow [setup and the first example](GETTING_STARTED.md),
compare the [seven fixtures](../application/examples/README.md), and consult the
[canonical standard](../application/APPLICATION_STANDARD.md) for the reporting rules.

**Proof reviewer:** use the [current ledger](FORMALIZATION_MAP.md#source-to-lean-theorem-and-definition-ledger),
[dependency map](FORMALIZATION_MAP.md#dependency-dag), and
[Lean provenance/crosswalk guide](../verification/lean/README.md).
The formalization map's later numbered milestones describe historical construction;
read its completion boundary for current coverage.

**Reproducer or contributor:** use the [verification guide](../verification/README.md)
and [contribution guide](../CONTRIBUTING.md). Select the check corresponding to your
change; neither Python tests nor schema validation substitutes for a Lean proof.

## Reference map

| Reference | What it answers |
|---|---|
| [Application Standard](../application/APPLICATION_STANDARD.md) | What must an application declare? |
| [Schema guide](../application/schemas/README.md) | How do the seven JSON schemas fit together? |
| [Validator reference](../application/validator/README.md) | What do options, output, hashes, and exit codes mean? |
| [Application boundary](APPLICATION_BOUNDARY.md) | What does each verification layer establish? |
| [Formalization map](FORMALIZATION_MAP.md) | Which definitions and theorems are represented in Lean? |
| [Paper verification manifest](PAPER_VERIFICATION_MANIFEST.md) | Which snapshot, artifacts, and runs belong to v0.1.8? |
| [Release metadata](releases/v0.1.8.json) | What are the machine-readable release identifiers? |
| [Future theory roadmap](FUTURE_THEORY_ROADMAP.md) | Which directions are research, not v0.1.8 results? |

## Archives are not onboarding instructions

The [provenance guide](../provenance/README.md) identifies preserved release records.
The [release-gate guide](../verification/v0.1.8_release_gate/README.md) distinguishes
Run 34 from historical Runs 31–33 and explains their external package requirements.
The [destructive-suite guide](../verification/destructive/suite/README_RERUN.md)
explains the compact Run 30 source fixture and unavailable legacy workpacks.

The v0.1.7 sketch and historical PASS reports remain unchanged as records of their
own stages. They do not redefine the final paper, the current application format,
or the current [research roadmap](FUTURE_THEORY_ROADMAP.md).

[Documentation review scope and findings](DOCUMENTATION_REVIEW.md) records the
README-inward usability review without changing scientific or historical evidence.
