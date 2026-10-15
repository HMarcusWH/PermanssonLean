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

**Future-theory researcher:** begin with the [current future-theory roadmap](FUTURE_THEORY_ROADMAP.md),
then use the [complete v0.2.0 mathematical integration contract](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md)
for precise theorem hypotheses, equations, proof sketches, failure cases, proposed Lean interfaces and release gates.
The [next-generation architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md) preserves the detailed
historical A/B/C/D design, while the [research build guide](RESEARCH_BUILD.md) records actual
merged research, CI and active PR boundaries. None of the proposed v0.2.0 obligations is automatically
part of the proved v0.1.8 core.

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
| [v0.2.0 mathematical integration contract](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md) | Full new equations, hypotheses, proofs-to-build, Lean targets, counterexamples and release conditions |
| [Next-generation research architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md) | How are lanes A/B/C/D specified, wired, proved and independently tested? |
| [Research library build guide](RESEARCH_BUILD.md) | How do I build and audit the separate research Lean target? |
| [v0.2.0 research proof ledger](V020_RESEARCH_PROOF_LEDGER.md) | What is implemented in proposed v0.2.0, what passed at a specific commit, and which proof/empirical gates remain open? |
| [A2 primitive-kernel perturbation](LANE_A2_PRIMITIVE_TV.md) | Which bounded typed alpha/world/update errors imply a finite constitutive margin under matched interventions? Merged PR #64 on main; consult exact-commit proof evidence. |
| [B2 four-corner sequential effects](LANE_B2_SEQUENTIAL_EFFECTS.md) | What is proven and tested about joint strategic effects, conditional constitutive margins, and separately admitted block projections? Draft PR #65. |\n| [C10 exact rational execution ledger](LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md) | How do exact absorption, original constitutive margins, checked receipts and release gates fit together? |
| [C10 source-bound release evidence](C10_RELEASE_EVIDENCE.md) | How is the six-state literal proof bound to the exact PR source, synthetic merge, specification and receipt? |
| [C11-A rational stationary-class certification](LANE_C11_CLASS_STATIONARY_CERTIFICATION.md) | How are complete exact stationary class receipts related to genuine typed C2 occupation laws? |
| [CQ-1 finite-path bridge](CQ1_FINITE_PATH_BRIDGE.md) | Which new bounded finite-horizon property and TV results are proposed and what are their boundaries? |

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

- [CQ-1 Part 2 finite constitutive certificate (research candidate)](CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md)

- [CQ-1 Part 3 certificate transport (research candidate)](CQ1_CERTIFICATE_TRANSPORT.md)

- [D0 frozen-menu reverse solver (research)](D0_FROZEN_MENU.md)

- [D0-B finite rational evaluator and conditional menu certification](D0_FROZEN_MENU.md#d0-b-theorem-inventory-pr-40)
