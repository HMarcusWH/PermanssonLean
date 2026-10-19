# Documentation index

[Repository home](../README.md) · [Getting started](GETTING_STARTED.md) · [Glossary](GLOSSARY.md)

## Choose a reading path

**Reader:** start with the [paper guide](../paper/README.md), then use the
[glossary](GLOSSARY.md) and [claim boundary](APPLICATION_BOUNDARY.md). No software
installation is required to read the paper.

**Application-report author:** follow [setup and the first example](GETTING_STARTED.md),
compare the [seven fixtures](../application/examples/README.md), and consult the
[canonical standard](../application/APPLICATION_STANDARD.md) for draft reporting rules.
This checks structural consistency, not mathematical or empirical truth.

**Proof-replay user:** consult the [C10 six-state successor](../apps/permansson/closure-successor/README.md)
or the [C11 finite stationary-family successor](../apps/permansson/closure-successor-c11/README.md).
The C10 metadata still carries a draft/CI-pending status marker; neither CLI
certifies an external strategic model or real-world regime.

**Proof reviewer:** use the [original v0.1.8 ledger](FORMALIZATION_MAP.md#source-to-lean-theorem-and-definition-ledger)
and [Lean provenance](../verification/lean/README.md) for the frozen core;
use the [research build guide](RESEARCH_BUILD.md),
[implementation index](V020_IMPLEMENTATION_INDEX.md), and
[post-PR79 source/CI index](../research/paper_closures/post_merge_79/source_ci_index.json)
for later scoped research proofs. A dated result belongs only to its source and CI event.

**Research mathematician:** begin with the [research build guide](RESEARCH_BUILD.md)
and [implementation index](V020_IMPLEMENTATION_INDEX.md), then consult the
[v0.2.0 mathematical integration contract](PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md)
for hypotheses and open targets. The [future-theory roadmap](FUTURE_THEORY_ROADMAP.md)
and [architecture](PERMANSSON_RESEARCH_ARCHITECTURE.md) preserve earlier dated plans;
they are not live acceptance certificates. The [accepted v0.2.0 research companion](../release/v0.2.0/README.md)
predates the PR #79–102 additions and must not be represented as their release.

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
| [Research library build guide](RESEARCH_BUILD.md) | Current 19 October 2026 checkpoint, non-default research build, CI and historical research status snapshots |
| [C10 v0.1.0 proof-replay application](../apps/permansson/closure-successor/README.md) | Frozen six-state model only; exact arithmetic and real Lean replay, with unreconciled draft status metadata |
| [C11 v0.2.0 proof-replay application](../apps/permansson/closure-successor-c11/README.md) | Reified 1–6-state rational stationary families; not a strategic or empirical certificate |
| [Post-PR79 source/CI evidence index](../research/paper_closures/post_merge_79/source_ci_index.json) | Merged proof source, CI and reviewer-receipt provenance for the October 18 closure build |
| [Post-PR79 acceptance decisions](../research/paper_closures/post_merge_79/acceptance_decisions.json) | Historical 45-case acceptance status; later PRs need separately reconciled proof and acceptance evidence |
| [Accepted v0.2.0 research companion](../release/v0.2.0/README.md) | Accepted earlier source `5822cdff0fc3…`: TeX/PDF, exact theorem crosswalk, source-bound receipts; not the later PR #79–102 closure build |
| [v0.2.0 master implementation index](V020_IMPLEMENTATION_INDEX.md) | Dated October 16–17 anchor map and theorem scopes; not a live acceptance index for PRs #79–102 |
| [X1 same-world commons](LANE_X1_COMMONS.md) | Both-player exact incentive certificates, typed equilibrium/learner models with identical P, leaking replete region, proved distinct descriptor occupation laws, killed persistence and explicit comparison-design limits |
| [F1 multi-agent protocols](LANE_F1_MULTIAGENT_PROTOCOLS.md) | Crosswalk for F1: two-player conditional-product subclass, strict opponent-locking, V20.29 metric bounds, MA1 and MA3 witnesses, and the open strict MA2 boundary |
| [E1 approximate quotients](LANE_E1_APPROX_QUOTIENT.md) | Crosswalk for E1: general event-TV calculus, linear finite-prefix bound for approximate type-respecting quotients, margin comparison, leakage counterexample |
| [A3 conditional dual-form robustness](LANE_A3_CONTRACTIVE.md) | Crosswalk for A3: conditional dual-form distance calculus, assumed invariant laws and four-law margin factorization, bundled survival counterexample, TV conversion firewall |
| [C-Exit E random-entry occupation](LANE_C_EXIT_RANDOM_ENTRY.md) | Crosswalk for C70: finite-prefix deletion estimate, a.s. and in-probability occupation after random entry, scoped Proposition 4.2f |
| [D2 finite residence objectives](D2_RESIDENCE_OBJECTIVE.md) | Literal reach-and-stay events, genuine typed finite-path evaluation, finite-history optimization, robust-order and hard-risk boundaries |
| [v0.2.0 research proof ledger](V020_RESEARCH_PROOF_LEDGER.md) | What is implemented in proposed v0.2.0, what passed at a specific commit, and which proof/empirical gates remain open? |
| [A2 primitive-kernel perturbation](LANE_A2_PRIMITIVE_TV.md) | Which bounded typed alpha/world/update errors imply a finite constitutive margin under matched interventions? Merged PR #64 on main; consult exact-commit proof evidence. |
| [B2 four-corner sequential effects](LANE_B2_SEQUENTIAL_EFFECTS.md) | Source and tests for scoped joint effects and conditional margins; PR #65 merged, with exact theorem hypotheses governing scope |
| [C-Exit destination routing research](LANE_C_EXIT_ROUTING.md) | First-exit destination submeasure and QSD routing; PR #66 merged, with later C-Exit work in separate PRs |
| [C10 exact rational execution ledger](LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md) | How do exact absorption, original constitutive margins, checked receipts and release gates fit together? |
| [C10 source-bound release evidence](C10_RELEASE_EVIDENCE.md) | How is the six-state literal proof bound to the exact PR source, synthetic merge, specification and receipt? |
| [C11-A rational stationary-class certification](LANE_C11_CLASS_STATIONARY_CERTIFICATION.md) | How are complete exact stationary class receipts related to genuine typed C2 occupation laws? |
| [CQ-1 finite-path bridge](CQ1_FINITE_PATH_BRIDGE.md) | Bounded finite-horizon property/TV foundations and their limits |
| [CQ-1 finite constitutive certificate](CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md) | Second CQ-1 stage, with its own assumptions and proof limits |
| [CQ-1 certificate transport](CQ1_CERTIFICATE_TRANSPORT.md) | Third CQ-1 stage: scoped model-error certificate transfer |
| [D0 frozen-menu reverse solver](D0_FROZEN_MENU.md) | Finite-menu rational optimization and conditional typed bridge |
| [D0-B rational evaluator and certification](D0_FROZEN_MENU.md#d0-b-theorem-inventory-pr-40) | The exact historical D0-B theorem inventory and conditional limit |

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
