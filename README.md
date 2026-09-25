# PermanssonLean

Formal verification and executable-validation companion for **Permansson Regimes: A General Framework for Strategic Dynamics Beyond Equilibrium v0.1.8**.

Permansson separates two questions: what persistent regime a strategic process
generates, and whether a declared strategic component is constitutive of a regime
property under a specified intervention. This repository collects the paper, Lean
proofs, executable tests, and an application-reporting standard. It is not an
automatic regime-discovery, prediction, or causal-estimation service.

## Start here

| Your goal | First stop | Software needed |
|---|---|---|
| Understand the theory | [Paper and reading order](paper/README.md) | None to read the PDF |
| Try the application format | [Setup and first example](docs/GETTING_STARTED.md) | Git and Python 3.13 |
| Check the mathematical claims | [Formalization map](docs/FORMALIZATION_MAP.md#source-to-lean-theorem-and-definition-ledger) and [Lean setup](docs/GETTING_STARTED.md#build-the-lean-proofs) | Lean/elan and Git |
| Reproduce verification | [Verification guide](verification/README.md) | Depends on the selected check |
| Make a change | [Contribution guide](CONTRIBUTING.md) | Depends on the change |

New to the terminology? See the [glossary](docs/GLOSSARY.md).
The [documentation index](docs/README.md) links the detailed references and archives.

## Using Permansson in applications

The [Application Standard](application/README.md) is **draft 0.1.0**, compatible
with theory v0.1.8. It serializes the nine independent certificate dimensions,
frozen semantic choices, typed interventions, provenance, and identified sets.
You do not need Lean or LaTeX to use its Python validator.

After [setting up Python and entering the repository root](docs/GETTING_STARTED.md#setup):

```bash
python -m pip install -r application/requirements.txt
python application/validator/validate_application.py application/examples/grounded_pr_minimal/application.json --json
```

Expect exit 0, `contract_valid=true`, and `scientific_claims_verified=false`.
This synthetic example demonstrates a well-formed record, not empirical evidence.
`CONTRACT PASS` checks structural consistency, not proof, causal identification,
statistical coverage, or authentic preregistration. In particular, a well-formed
record can truthfully describe an invalid or unresolved application.

Continue with the [worked examples](application/examples/README.md),
[CLI reference](application/validator/README.md), or
[application/formalization boundary](docs/APPLICATION_BOUNDARY.md).
**Digest generation is not validation:** `--digest` can exit 0 for matching stale
IDs. Use ordinary validation, without `--digest`, as the contract gate.

## Paper and supporting theory

Read the [editorial-clean v0.1.8 PDF](paper/Permansson_Regimes_Strategic_Dynamics_Beyond_Equilibrium_v0.1.8_SUBMISSION_FINAL_EDITORIAL_CLEAN_2026-09-23.pdf).
The [paper guide](paper/README.md) links its TeX source, the foundational EGR paper,
and the specialized Appendix E papers. Those supporting copies do not change the
frozen release hashes or the formalization snapshot.

## Build

Install Lean through elan using the [Lean setup guide](docs/GETTING_STARTED.md#build-the-lean-proofs),
then run from the repository root:

```bash
lake exe cache get
lake build
```

Use the checked-in dependency manifest; a routine build does not require
`lake update`. The [Lean workflow](.github/workflows/lean.yml) additionally runs
an axiom audit and rejects placeholders and source-level custom axioms.

## Current coverage

The completion claim covers the **v0.1.8 discrete formal core through Proposition
8.1**, not every statement in the paper. The full
[theorem/definition ledger](docs/FORMALIZATION_MAP.md#source-to-lean-theorem-and-definition-ledger)
records the checked declarations and their boundaries.

### Formalization strategy

The [dependency map](docs/FORMALIZATION_MAP.md#dependency-dag) follows typed kernels,
path laws, regime/persistence semantics, constitution, representation and quotient
preservation, Paper-I recovery, and the periodic example. Its later milestone
sections retain the historical build sequence, not a list of remaining tasks.

### Status discipline

[Status definitions](docs/FORMALIZATION_MAP.md#claim-firewall) distinguish PROVED,
DEFINED, SCAFFOLDED, OPEN, NON-CORE, and EMPIRICAL material. A green Lean build checks
the encoded declarations; it does not certify empirical premises or literature priority.
Appendix E and the [future theory roadmap](docs/FUTURE_THEORY_ROADMAP.md) remain
outside the completed discrete core.

## Executable verification

The [verification guide](verification/README.md) separates Lean proof checking,
Runs 17–30, repository/release integrity, and application-contract validation.
It gives commands, expected outcomes, and the distinction between a normal clone
and the historical release packages. Their PASS results are not interchangeable.

## Toolchain

| Component | Version authority |
|---|---|
| Theory and scholarly companion | v0.1.8 — [CITATION.cff](CITATION.cff) |
| Lean / mathlib | 4.34.0 / v4.34.0 — [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml) |
| Application format | Draft 0.1.0 — [application/VERSION.json](application/VERSION.json) |
| Python verification | CPython 3.13; separate [application](application/requirements.txt) and [destructive-suite](verification/destructive/suite/requirements.txt) dependencies |

The Lean package version remains `0.1.0` because its package metadata belongs to
the immutable formalization snapshot. It is not the paper's release version or
the independently versioned application standard.

## Paper release provenance

The manuscript identifies mathematical snapshot
`c018f79ea4ce46f4f679ad5bca254509778fc53c` and
[its recorded green CI run](https://github.com/HMarcusWH/PermanssonLean/actions/runs/35808810682).
For exact artifact hashes and filename mappings, use the
[paper verification manifest](docs/PAPER_VERIFICATION_MANIFEST.md),
[machine-readable release metadata](docs/releases/v0.1.8.json), and
[provenance guide](provenance/README.md).

Use [CITATION.cff](CITATION.cff) for the scholarly companion and record the exact
commit when referring to a later repository or application implementation.
