---
title: "Permansson — Mathematical and Executable Reference Guide"
subtitle: "Volumes A–F | 46 chapters | Technical reference v1.1.1 | Proofread and clarified edition"
author: "Based on the Permansson research and formalization by Marcus Hermansson"
date: "20 November 2026 (Europe/Stockholm)"
lang: en
---

**Edition status — v1.1.1: proofread technical reference; independent case review remains pending.** This edition retains the 46 chapters, 24 formal-core interpretations and complete 56-case source crosswalk of v1.1, with explicitly recorded editorial and scope clarifications. Original v1.0 and v1.1 artifacts retain their original bytes. The independent 45-case and 11-claim acceptance processes are not represented as completed. Numerical release reproduction, research-source compilation, editorial review and external identification retain their separate statuses. Appendix K.1 and the accompanying proofreading addendum identify the changes and fresh checks.

**Latest added-source commit:** `23e6a57b381363cf20751a18337ca927cd393a6c`; tree `e3211713f1ef508ea891f534509116accaad56a4`.

**CI/integration state supplied for this edition:** PR126 passed all six workflows and all nine check runs. Research run 44639175231 passed 2,260 tests in 2,998.737 seconds. GitHub checked synthetic merge e1adca3ae51ea5e220573171ef5ef53a7c6c3654 against base 4d2f0367a37e47c3c4f10fb17baad575521c6f11. PR126 merged as c5a36cd6189e2a249d5f4bc11f31698917dc8b10 on 20 November 2026 at 01:50 Europe/Stockholm. Candidate, synthetic test merge and actual merge share tree e3211713f1ef508ea891f534509116accaad56a4. The separate clean committed local replay passed eight tests in 94.745 seconds with unchanged inputs and clean worktrees. The newly triggered postmerge workflows are recorded separately; they were queued at the initial merge observation.

The five focused packets each passed clean local replay and authenticated PR126 CI, retaining 257 named declaration occurrences (256 distinct names) and 17 semantic controls. The separate all-56 packet retains 136 distinct names, 139 case-owned occurrences, 77 provider artifacts and 167 source/meta pins, and executes zero semantic controls itself. All 23 new CI compiler-stage hashes and their allowed-axiom output were verified. The internal clause review, supplementary E-04 local Lean controls and C11-02 local Python checker control have separately identified records. None is an independent case-acceptance decision.

**All-56 named-source receipt:** CI_AND_CLEAN_COMMITTED_NAMED_SOURCE_REPLAY_PASS. All 56 frozen entries have selected named-source coverage in both clean committed replay and authenticated PR126 CI: 136 distinct declarations, 139 case-owned route occurrences, 77 provider artifacts and 167 source/meta pins. This direct packet executed zero semantic controls. Internal clause inspection, criterion-specific controls and independent acceptance are separately recorded. Receipt: `PR126_Tranche10_All56_Receipt.json` (SHA-256 prefix `cf69c15c398d`). Receipt: `PR126_Completed_CI_Verification.json` (SHA-256 prefix `ee1d3e0d92b9`). Receipt: `Tranche10_All56_Clean_Receipt.json` (SHA-256 prefix `b49c6683a7ee`).

**Installed-release verification completed (19 November 2026).** The exact published v0.2.0 wheel and sdist SHA-256 digests were reproduced from GitHub Actions release-build and release-gated artifacts. The wheel was installed outside the repository into a separate Linux CPython 3.13 environment. The packaged 25 primary profile examples and three native C10/C11 requests passed the released independent-checker walkthrough (28/28). In 21 cases Lean-candidate source generation, byte recheck and tamper rejection passed; four cases were numerical-only because of reflection bounds. That historical installed-wheel walkthrough did not compile its 21 emitted application candidates or perform independent research certification. The new research-source compiler receipts are separate and appear in E02.6. See Appendix I for the unchanged dependency and evidence qualifications.

**Immutable source baseline:** [Pinned repository source](https://github.com/HMarcusWH/PermanssonLean/tree/89ac97cb8bcaad0c47c421209dd2e103db6d60ee), commit `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`. **Numerical release:** `permansson-app-v0.2.0`, from `63a66c82a9ece4361f646ee13b6711192f831406`. The historical research imports are separate evidence artifacts, not identified causal kernels.

# How this guide is organized

- **Volumes A–B:** Orientation and mathematical foundations (12 chapters)
- **Volume C:** Advanced mathematics and reverse solver (15 chapters)
- **Volume D:** Executable exact numerical application (7 chapters)
- **Volume E:** Verification, evidence and certification (8 chapters)
- **Volume F:** Case studies, reproducibility and research boundaries (4 chapters)

---


\newpage

# Volumes A–B — Orientation and Mathematical Foundations

**Scope of Volumes A–B.** These chapters teach declared stochastic models and bounded software verification through fictional public-service systems. No operational targeting, attack selection, offensive sequencing, or real-conflict prediction is supplied.

> **Frozen source:** `HMarcusWH/PermanssonLean`, commit `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`, tree `cf3d19b5eaa3756fe5c2e392367b9066330e1a4b`. Published successor numerical release: `permansson-app-v0.2.0` from commit `63a66c82a9ece4361f646ee13b6711192f831406`. Source and release have different commits. Lean source compilation is supported by the separately recorded GitHub Actions checks; this manuscript is not a new independent mathematical certification.

# How to use this volume

This is the orientation section of the complete 46-chapter reference guide. **Volume A** is the reader's orientation and source/installation reference. **Volume B** introduces the typed strategic-world process, generated law, exact and approximate regime objects, constitutive tests, representation, and long-run behavior. The associated source index names actual files, not hypothetical new modules. Volumes C–F cover advanced reverse-solver mathematics, the 26-profile application, the C10/C11 providers, proof evidence, and neutral end-to-end exercises.

Every chapter has five fields: **objective**, **definition**, **source correspondence**, **worked reading or calculation**, and **claim boundary**. A reader should never need to guess whether a statement is (i) a definition, (ii) proved in a stated Lean scope, (iii) numerically evaluated for a finite input, or (iv) an empirical inference. These labels are not interchangeable.

## Verification vocabulary

| Status | Meaning in this guide |
|:--|:--|
| *Defined* | A data type or mathematical predicate exists. Merely defining it does not prove that any nontrivial example satisfies it. |
| *Lean-checked* | A concrete declaration compiles in the pinned Lean/mathlib environment under its written hypotheses and approved axioms. |
| *Numerically checked* | An independent exact arithmetic checker confirms the reported result for a supplied, bounded input. |
| *Source-bound candidate* | An emitted Lean file is tied to source bytes, but not thereby compiled or independently certified. |
| *Outside scope* | The stronger theorem, empirical claim, or unrestricted generalization has not been established by that artifact. |

The primary internal references are [the source README](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/README.md), [the Formalization Map](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/FORMALIZATION_MAP.md), [the research build guide](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/RESEARCH_BUILD.md), and [the successor application manual](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/README.md).

# Volume A - Orientation, versions and first execution

## A01. What Permansson is, and is not

**Learning objective.** Distinguish *theory of an induced process* from a method for solving an equilibrium or inferring a model from observations.

Permansson starts with a strategic generator $G=(\alpha,U)$ and a separate world-transition kernel $P$. Together they induce a process on joint strategic-world states. The general theory studies the properties of that process, especially long-run configurations and how declared properties respond to particular admissible interventions. An equilibrium can supply a generator in a particular model, but the generalized regime concept does not require equilibrium to be a primitive of regime classification.

A **Generated Regime (GR)** concerns the generated process and a declared, invariant region with a limiting descriptor occupation behavior. A **Permansson Regime (PR)** adds the requirement that at least one eligible strategic-generator component is *constitutive* of a defining property under a typed intervention. These are conjunctive requirements. An analyst cannot declare a PR because an interesting trajectory occurred, a score crossed a threshold, or an intervention changed some number.

The framework is **not** a universal optimizer, a factual event classifier, a theory of justified political ends, or an estimator that extracts the causal factors $\alpha$, $P$, and $U$ from one observed trajectory. The original paper's equilibrium-related EGR terminology and the generalized GR/PR layer require deliberate version mapping, not silent substitution.

**Source correspondence.** `README.md`, `paper/README.md`, `docs/GLOSSARY.md`, `docs/APPLICATION_BOUNDARY.md`, `PermanssonLean/Regime/GeneratedRegime.lean`, `PermanssonLean/Regime/Permansson.lean` and the formalization map. These are authoritative for scope; historical explanatory documents must be read against the frozen commit.

**Reader test.** Consider the statement, "This case remained in an interesting high-coupling state for 20 observations, therefore it is an Exact GR." The conclusion does not follow: observed recurrence cannot establish exact invariance of a region or convergence of the declared occupation law for the entire admissible initial-law class. A finite path can motivate a candidate specification, not complete the formal gate.

**Claim boundary.** The existence of a mathematical classifier does not identify its inputs from reality and does not validate a real-world conclusion. Exact arithmetic is conditional on the model.

## A02. Declare a property before computing

**Learning objective.** Write a mathematically evaluable objective and a falsifier without letting the calculation choose its own goal.

Start by specifying a *system boundary*: which variables enter $S$ (strategic state), which enter $X$ (world state), and which states are deliberately out of scope. Next specify an observable descriptor $h:Y\rightarrow H$ on the full joint state space $Y=S\times X$. Separately declare a region $B$, a nonempty basin or admissible starting class $B_0$, a mathematical property $\psi$ of a path law, a time horizon where appropriate, and the comparison object. If an outcome matters only under legal, resource, reliability, or equity constraints, those constraints belong in the declared model, not in a post-hoc paragraph.

For a **fictional municipal service**, an example property is the probability of maintaining service for two consecutive transitions, starting in an operating state. That property is distinct from the probability that the service is operating at time two. An alternative could improve the latter while not improving the former. A declaration must choose which is being measured.

The guide will use an *objective card* with these fields:

1. **Purpose and authority:** who specifies the property, and who may revise it.
2. **State ontology:** $S$, $X$, $A$, admissibility, known exclusions.
3. **Property:** explicit function of an initial state or distribution and a path law.
4. **Observation and uncertainty:** what is specified, assumed, or measured.
5. **Stop/failure rule:** which result would refute a proposed interpretation.
6. **Version pin:** exact source, model, schema, fixture, and calculation mode.

**Source correspondence.** `PermanssonLean/Regime/Specification.lean` defines $B$, $B_0$, $h$, $\nu$ and convergence mode. `PermanssonLean/Regime/Property.lean` defines properties of full path laws, not merely instantaneous labels. The strategic doctrine's end-state framework is an external *design analogy*, not a theorem in the Lean repository.

**Reader test.** Rewrite "make the system better" as a specific statement, for example $\Pr(X_2=\text{operating}) \ge 0.8$ under a fixed initial distribution and a fixed kernel. Then separately record that a lower chance of interruption *at exactly time two* does not automatically imply a smaller probability of *ever* being interrupted by time two.

**Claim boundary.** Mathematical optimization cannot supply the underlying public purpose or authorization. The guide's examples do not assign military objectives or operational means.

## A03. Source, release and authority map

**Learning objective.** Reproduce a result without accidentally combining different releases or treating release acceptance as mathematical certification.

The canonical version boundary contains several deliberately separate objects:

| Artifact | Identity | What it establishes |
|:--|:--|:--|
| Source paper | Permansson v0.1.8 | Versioned mathematical definitions and stated research claims |
| Frozen core | `PermanssonLean/` and root `PermanssonLean.lean` | Discrete Lean formalization; default Lake target |
| Research library | `PermanssonResearch/` and root `PermanssonResearch.lean` | Further finite, measurable, nonfinite and application-related theorems, each under local hypotheses |
| Research companion | `release/v0.2.0/` | Separate accepted research artifact with its own acceptance boundary |
| Legacy Application Standard | `application/` (draft v0.1.0) | Semantic reporting/contract validation, not numeric proof |
| Native providers | `apps/permansson/closure-successor/` and `closure-successor-c11/` | Separate bounded C10/C11 rational proof-replay interfaces |
| Successor numeric app | `apps/permansson/application-successor/` v0.2.0 | 26 finite numerical profile commands, independent checkers and bounded Lean-source bridges |
| Verification infrastructure | `verification/` and workflows | Compilation, static/regression, source identity and release acceptance, with distinct semantics |

The frozen root package can still display `0.1.0` in metadata while its associated paper is v0.1.8. Likewise, the *research* companion v0.2.0 and *numeric application* v0.2.0 are not the same product. The current `main` commit and published wheel have different commit identities; this is expected and must be displayed rather than reconciled away.

**Reproduce source selection.** Clone or extract the verified source, check the exact commit, and record both `git rev-parse HEAD` and the pinned `lean-toolchain`/`lake-manifest.json`. A local ZIP with a matching full Git tree can act as an immutable source reference, but must not be mistaken for fresh output from a deployed installed wheel.

**Source correspondence.** `README.md`, `docs/RESEARCH_BUILD.md`, `docs/V020_IMPLEMENTATION_INDEX.md`, `release/v0.2.0/README.md`, `apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md`, `.github/workflows/lean.yml`, `.github/workflows/research-lean.yml`.

**Claim boundary.** Historical source identities are evidence, not an invitation to upgrade proof status; compiler, producer, checker, and independent acceptance remain separately documented.

### A03.1. Edition v1.1 source layers and precedence

| Object | Immutable identity | Role in this edition |
|:--|:--|:--|
| Canonical guide v1.0 | Markdown SHA-256 `b5333d3719995a1a1e99a0de5ab340af5de9485921f9c5d7730dd270c205e98b` | Preserved manuscript; original 46 chapters and core interpretation ledger |
| Historical guide source | `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`; tree `cf3d19b5eaa3756fe5c2e392367b9066330e1a4b` | Original references and six recorded CI runs |
| Published numeric application | `63a66c82a9ece4361f646ee13b6711192f831406`; `permansson-app-v0.2.0` | Installed-wheel evidence preserved in Appendix I |
| Merged Q-05 additions | `b6ac6a0ca0de933b555454e5f7a7739d67004aa1` | Original whole-path outputs and margins |
| Merged Tranche 8 | `54e00dfdc09713b164060caff9be71d5412b1614` | F-01 and D-09 source/evidence packet |
| Merged Tranche 9 | `4d2f0367a37e47c3c4f10fb17baad575521c6f11` | D-08 and D-06 source/evidence packet |
| Latest additive source | `23e6a57b381363cf20751a18337ca927cd393a6c` | Tranche 10 repairs and direct case receipts; status in E02.6/E06.6 |

Later dated source additions supersede earlier descriptions of missing proofs only where they establish the literal narrower result. They do not rewrite historical artifacts or change an independent acceptance status. All source links inherited from v1.0 retain their original commit; the new examples identify their own sources. The Appendix H label v0.9.2 is part of a retained historical review recommendation, not the current edition number.

## A04. Installation and the first independently checked calculation

**Learning objective.** Install the supported numeric interface and run an existing self-contained, noncombat example.

The published numeric release targets **Linux CPython 3.12 or 3.13**. Other platforms are not covered by that release's whole-run resource-budget assurance. A source checkout is suitable for learning, but the official wheel should be installed with its released checksum file when comparing against the publication.

For a source checkout, install the application with its required JSON Schema dependencies (`[full-schema]` is a compatibility alias):

```bash
python -m pip install './apps/permansson/application-successor[full-schema]'
permansson-app about
permansson-app capabilities
permansson-app resources --full --output /tmp/permansson-guide-resources
permansson-app finite-kernel \
  /tmp/permansson-guide-resources/examples/finite_world.v1.model.json \
  --output /tmp/permansson-guide-kernel
cat /tmp/permansson-guide-kernel/independent_check.json
cat /tmp/permansson-guide-kernel/scientific_report.json
```

Use a *new* output directory for each command. The application creates an exact receipt and an independent check. A reported `PASS` concerns the finite declared input. It does **not** imply that Lean compiled an emitted candidate, that a manuscript claim passed independent scholarly acceptance, or that the parameters were inferred from any real system.

The original Lean core and research root are built separately from the repository root, using the checked-in pinned toolchain:

```bash
lake exe cache get
lake build
lake build PermanssonResearch
```

The historical source-snapshot audit records successful original and research Lean GitHub CI evidence. The v1.0 installed-application walkthrough did not compile its emitted candidate instances; new research-source compiler receipts for v1.1 are recorded separately in E02.6. For a source-bound Lean example, the application distinguishes `lean-emit`, `lean-recheck`, and an actual `lake env lean` invocation. Byte equality and compilation are different checks.

**Source correspondence.** `apps/permansson/application-successor/README.md`, `docs/CAPABILITY_SCOPES.md`, `src/permansson_app/__main__.py`, the packaged example `finite_world.v1.model.json` under `src/permansson_app/data/examples/`, plus `src/permansson_app/receipts/`, `docs/RESEARCH_BUILD.md`.

**Exercise A04.** Export the packaged resources, run `finite-kernel`, preserve the original input JSON and the two output JSON reports, and write down five fields: package version, source identity, independent-check status, Lean status, and empirical-identification status. An acceptable answer does not replace the latter three with one undifferentiated word *verified*.

# Volume B - The mathematical foundations

## B01. The typed strategic-world model

**Learning objective.** Describe a model in the paper's exact composition order and verify the probability-law contracts.

Let $S$ be a measurable strategic-state space, $X$ a measurable world-state space, and $A$ a measurable action space. The **joint state** is $Y=S\times X$. The strategic generator consists of two Markov kernels:

$$
\alpha(da\mid s,x), \qquad U(ds'\mid s,x,a,x'),
$$

while the world-transition kernel is

$$
P(dx'\mid s,x,a).
$$

The order is essential: observe $(s,x)$, draw an action from $\alpha$, draw the next world state using $P$, then update the strategic state with $U$ using the newly realized world state. Merely placing $P$ and $U$ in the opposite order changes the declared model. In Lean, `StrategicGenerator` carries `action`, `update` and their Markov-kernel obligations; `StrategicWorldModel` carries `generator` and `world`.

For a *finite* model, each feasible action-selection row, world-transition row and strategic-update row must be nonnegative and sum to one. Inadmissible-action completions, if required by a source representation, need an explicit mathematical convention. The model's feasibility relation must not be silently inferred from the numeric optimizer's result.

**Worked model (fictional public service).** Use $S=\{N,B\}$ (normal/burdened strategic status), $X=\{O,I\}$ (operating/interrupted), and $A=\{m,r\}$ (monitor/recover). At every joint state, suppose

$$
\alpha(r\mid s,x)=\frac34,\quad \alpha(m\mid s,x)=\frac14;
\qquad P(O\mid s,x,r)=\frac45,\quad P(O\mid s,x,m)=\frac15.
$$

Let the update be deterministic: $s'=N$ when $x'=O$, and $s'=B$ when $x'=I$. Each specified binary complementary probability completes to one. These are **illustrative assumed values**, not claims about the performance of any actual service or intervention.

**Source correspondence.** `PermanssonLean/StrategicWorld/Model.lean` (`JointState`, `StrategicGenerator`, `StrategicWorldModel`); `PermanssonLean/StrategicWorld/InducedKernel.lean` (typed composition); and the finite `finite_world.py` interpreter.

**Claim boundary.** The separate factors are model primitives. A realized joint-state time series generally does not identify $\alpha$, $P$ and $U$ individually.

## B02. Induced kernel, initial law, and path law

**Learning objective.** Calculate the induced joint-state transition matrix and distinguish its one-step law from a full path law.

For finite spaces, the joint transition kernel is

$$
K_{G,P}((s,x),(s',x'))
=\sum_{a\in A}\alpha(a\mid s,x)P(x'\mid s,x,a)U(s'\mid s,x,a,x').
$$

The measurable-space definition uses iterated integrals rather than a sum. The Lean theorem `StrategicWorldModel.inducedKernel_isMarkov` proves that the ordered construction is a Markov kernel; `inducedKernel_apply` connects the construction to the measure-theoretic expression. This does not assert that observed data identify the factors.

**Calculate the B01 example.** For any present state, the probability of $x'=O$ is

$$
\Pr(O')=\frac34\cdot\frac45+\frac14\cdot\frac15=\frac{13}{20},
$$

and of $x'=I$ is $7/20$. Because $U$ maps operating to $N$ and interrupted to $B$, the next joint state is either $(N,O)$ with probability $13/20$ or $(B,I)$ with probability $7/20$. The other two joint outcomes have probability zero. Each row of the four-state joint matrix therefore has exact sum $1$.

Let $\mu_0$ denote a probability law on $Y$. For a finite Markov kernel, the time-$t$ marginal is $\mu_t=\mu_0K^t$. The law of a prefix $(Y_0,\ldots,Y_T)$ is a different object: it retains transition order and temporal dependence. For a fixed initial state $y_0$,

$$
\Pr(Y_0=y_0,\ldots,Y_T=y_T)=\prod_{t=0}^{T-1}K(y_t,y_{t+1}).
$$

This has $T$ transitions and $T+1$ recorded states. The zero-transition prefix is a point mass at the initial state, not a fictitious first move. The repository's canonical path-law construction uses Ionescu--Tulcea and includes a well-posedness theorem (`joint_process_well_posed`) with its stated measurable-space assumptions. The finite `CanonicalFiniteKernel` and `FinitePrefixBridge` files separately establish specific rational-prefix correspondences; they must not be described as having identical generality without reading each theorem's quantifiers.

**Source correspondence.** `PermanssonLean/StrategicWorld/InducedKernel.lean`, `PermanssonLean/StrategicWorld/PathLaw.lean`, `PermanssonResearch/ReverseSolver/` (modules `CanonicalFiniteKernel.lean` and `FinitePrefixBridge.lean`).

**Exercise B02.** Verify $\Pr(X_2=O)=13/20$ in the example (all rows happen to be identical), while $\Pr(X_1=O,X_2=O)=(13/20)^2=169/400$. These are different events and must not be merged in a report.

## B03. Frozen regime specification and descriptor occupation

**Learning objective.** State the ex-ante object that an Exact Generated Regime claim must evaluate.

The frozen specification in `RegimeSpecification` is

$$
\Sigma=(B,B_0,h,\nu,\mathfrak c),
$$

where $B\subseteq Y$ is the measurable candidate region, $B_0\subseteq B$ is the measurable initial basin, $h:Y\to H$ is a measurable descriptor on the **entire** joint state space, $\nu$ is a target probability law on the descriptor space, and $\mathfrak c$ is the declared convergence mode. The data structure enforces measurability and basin inclusion. The chronological meaning of *ex ante* comes from fixing the specification before classifying a trajectory, not from a theorem that can determine when a human actually chose the definition.

Given a realized path $w=(Y_0,Y_1,\ldots)$, its finite descriptor occupation law at positive horizon $T$ is

$$
\widehat\nu_T^h(w)=\frac1T\sum_{t=0}^{T-1}\delta_{h(Y_t)}.
$$

This is not the same thing as the expected occupation law, nor the distribution of which absorbing or recurrent class will eventually be entered. The source represents the empirical occupation as a pushforward of the uniform law on `Fin T`, which ensures that the result is itself a probability measure. A limiting law requires an explicitly chosen convergence mode and quantifiers over **all admissible initial laws**, not just one simulation.

**Example.** For the two-output model, take $h(s,x)=\mathbf 1\{x=O\}$. The long-run mean occupancy of $O$ is $13/20$ under that specific memoryless matrix. But the region $B=\{(s,O):s\in S\}$ is **not exactly invariant**, because each transition has positive probability $7/20$ of leaving it. Therefore this positive occupation fraction does **not** certify an Exact GR for that $B$.

**Source correspondence.** `PermanssonLean/Regime/Specification.lean`, `Regime/Occupation.lean`, `Regime/ConvergenceMode.lean`, `Regime/Admissible.lean`, `Regime/GeneratedRegime.lean` and `docs/FORMALIZATION_MAP.md`.

**Reader check.** Before accepting any alleged regime, record $B$, $B_0$, $h$, $\nu$, convergence mode, initial-law class, and the full exact-invariance proof obligation. An undefined basin or arbitrary final-state score is not a complete specification.

## B04. Survival, killing, quasi-regimes and exact invariance

**Learning objective.** Separate finite-horizon residence from perpetual invariance, and optional quasi-stationary certificates from Exact GR claims.

Given a measurable region $B$, a *killed kernel* keeps the transition mass that stays inside $B$ and discards escaping mass. Its $T$-step surviving mass corresponds to the path event that the process stays in $B$ at the required intermediate times. The source proves a path-law/killed-kernel identity and a finite-persistence equivalence (`finitePersistence_iff_killed`). These are mathematical statements about a specified kernel and region, not forecasts.

The region-wide finite-horizon persistence gate is

$$
\Pr_y( Y_t\in B\ \text{for every}\ 0\le t\le T)\ge 1-\eta
\quad \text{for every initial }y\in B.
$$

The actual Lean predicate `IsFinitePersistent` requires `η ≤ 1` and the bound for **every** state of `spec.region` (the full candidate region $B$), not only for the smaller basin $B_0$. The comparison set used in strategic constitution is a different object. The exact-invariance condition is materially stronger: the next state stays in $B$ with probability one from **every** $y\in B$, and the source proves its equivalence to almost-sure survival forever (`exactInvariant_iff_survivalForever`) under the expressed assumptions.

In the constructed B01 model with $B=\{x=O\}$ and initial $X_0=O$, survival for two transitions is $(13/20)^2=169/400$, while survival for every future transition has probability zero. The latter follows because the factor $13/20$ is strictly less than one. This is why observed long runs cannot be promoted to a theorem of exact invariance.

A **quasi-stationary distribution (QSD)** is a probability law supported in $B$ that is stationary conditional on survival, paired with an eigenvalue $\theta$. In the source's `proposition_4_4b`, survival from the QSD takes the form $\theta^n$ and the normalized surviving endpoint law stays equal to that QSD. A QSD is not a substitute for the full Exact GR gate, nor does its existence alone establish uniform finite persistence over an arbitrary basin. The repository contains an explicit counterexample to that inference.

**Source correspondence.** `Regime/KilledKernel.lean`, `Regime/Persistence.lean`, `Regime/SurvivalBridge.lean`, `Regime/Invariance.lean`, `Regime/QuasiStationary.lean` and `Regime/ExitTime.lean`.

**Reader check.** When a result mentions *survival*, always record whether it means survival through $T$ transitions, never leaving, expected exit time, conditional survivor distribution, or survival under a QSD. They are five different objects.

## B05. Typed strategic interventions and constitutive dependence

**Learning objective.** Explain what a lawful *mathematical* intervention changes and why a numerical difference is not, by itself, a Permansson certificate.

The framework distinguishes a world-transition primitive $P$ from the strategic generator $G=(\alpha,U)$. An admissible **strategic-generator intervention** is taken from a declared family, changes a permitted component of $\alpha$ or $U$, and holds the world kernel $P$ fixed. The corresponding Lean types include `InterventionReplacement`, `InterventionFamily`, `TypedIntervention`, and `AdmissibleStrategicIntervention`. A direct physical/world-kernel change is a different estimand and cannot be relabeled a strategic-generator-only intervention.

A regime property map $\psi$ is applied to the *whole path law*. With baseline $M$, a predeclared nontrivial comparison set $B_1\subseteq B_0\subseteq B$, and an admissible strategic intervention $J$, the constitutive test has the form

$$
\forall y\in B_1:\quad
\psi(\mathcal L^M_y)\ne\psi(\mathcal L^{J(M)}_y).
$$

The source's `ConstitutiveComparisonSet` requires a formal point-initialized path-law nontriviality witness: two starting states in $B_1$ must have different full baseline path laws. Because those laws record time zero, distinct initial states already differ; this condition alone is not a substantive future-dynamics diversity test. The intervened diagnostic model need not itself remain a GR.

**Worked diagnostic only.** Change the B01 action-selection probability of `recover` from $3/4$ to $1/4$, holding $P$ and $U$ exactly fixed. Then

$$
\Pr^J(O')=\frac14\cdot\frac45+\frac34\cdot\frac15=\frac7{20}.
$$

For the one-step service-availability path property, the baseline-to-intervention difference is $13/20-7/20=3/10$. This establishes **a calculation in two declared models**, not an Exact GR: the baseline region $\{x=O\}$ already fails exact invariance. Thus even a large, uniform arithmetic difference does not magically turn this example into a certified PR.

**Source correspondence.** `PermanssonLean/Regime/Property.lean`, `Regime/Constitution.lean`, `Regime/Permansson.lean`, `Regime/ConstitutiveMargin.lean`, and the files in `PermanssonLean/Intervention/`.

**Reader check.** Demand a typed admissibility witness, held-fixed primitive list, $B_1$ proof obligations, full path-property definition, and baseline Exact GR evidence before using the label *Permansson Regime*.

## B06. Perturbation margins and representation discipline

**Learning objective.** Distinguish sensitivity of a computed effect from its robustness, and know when compression changes the question.

Suppose a constitutive comparison yields property values $p_0(y)$ and $p_J(y)$ on $B_1$. For a metric-valued property define its pointwise effect

$$
\Delta(y)=d\big(p_0(y),p_J(y)\big),
\qquad \delta=\inf_{y\in B_1}\Delta(y).
$$

An approximate model or computation may perturb each of the two outputs. Under a uniform output-error envelope $e_0(y)+e_J(y)$, the triangle inequality gives the schematic bound

$$
\big|\widetilde\Delta(y)-\Delta(y)\big|\le e_0(y)+e_J(y).
$$

A uniform bound controls the corresponding margin. The formal Proposition 5.2 implementation carries explicit assumptions and error objects; Corollary 5.3 supplies a conditional robustness criterion when the original margin exceeds the total error budget. The theorem does not say a large observed difference is causal.

For the B05 arithmetic diagnostic, $\Delta=3/10$. If a hypothetical property-output error bound is $1/25$ on each side, the total error envelope is $2/25$ and the difference is bounded below by $3/10-2/25=11/50>0$. This protects the *calculated output difference under the stated envelope*. It still does not establish Exact GR, empirical identification, or an unrestricted intervention claim.

The representation layer is equally important. Two factorizations may produce the same baseline induced kernel $K$ and thus identical baseline path laws, but respond differently under the declared intervention family. Therefore **baseline equivalence alone is insufficient for constitutive equivalence**. The Formalization Map specifically records a factorization non-identification theorem and a theorem concerning non-invariance of constitution under baseline-only equivalence. A quotient or compressed state representation preserves relevant claims only when its type, kernel intertwining and intervention-compatibility hypotheses are actually satisfied.

**Theorem 7.3 source nuance.** The Lean proof uses an alternative deterministic counterexample with a one-step survival property and a custom convergence mode; the paper illustrates the existential claim with a Bernoulli/long-run occupation witness. The proved existential non-invariance holds, but the paper’s exact illustrated dynamics are not what the named Lean proof compiles. See Appendix H.

**Source correspondence.** `Regime/Perturbation.lean`, `Regime/ConstitutiveMargin.lean`, `Regime/RepresentationEquivalence.lean`, `Regime/InterventionEquivalence.lean`, `PermanssonLean/Quotient/`, and `docs/FORMALIZATION_MAP.md`.

**Reader test.** If someone changes $P$ while claiming a pure $\alpha$ intervention, or changes the represented intervention family while claiming representation invariance, stop: the comparand has changed.

### B06.1. The actual discounted whole-path margin: Q-05

The source now supplies the original infinite-path quantities behind the approximate-quotient bound. This example uses fine state $(s,x)\in\mathrm{Bool}\times\mathrm{Bool}$ and coarse state $((),x)$; compression forgets the strategic coordinate and retains the physical coordinate. Let $t=0$ denote the baseline and $t=1$ the admitted joint strategic intervention. The intervention changes action selection and strategic update while retaining the physical transition primitive.

| Treatment | Fine rate at $s=0$ | Fine rate at $s=1$ | Coarse rate |
|:--|--:|--:|--:|
| Baseline | $1/10$ | $1/5$ | $3/20$ |
| Treated | $7/10$ | $4/5$ | $3/4$ |

The next physical bit equals the sampled action, and the fine strategic update sets the next strategic bit to $t$. Write $p(t,s)$ for the fine action rate and $\bar p(t)$ for the coarse rate. For $I(x)=\mathbf1_{\{x=1\}}$, the property is the normalized discounted whole-path score

$$
S(\omega)=(1-\gamma)\sum_{n=0}^{\infty}\gamma^n I(x_n(\omega)),
\qquad \gamma=\frac13.
$$

The original canonical path laws have outputs

$$
V_F(t,s,x)=\frac23 I(x)+\frac29p(t,s)+\frac19p(t,t),
\qquad
V_C(t,x)=\frac23 I(x)+\frac13\bar p(t).
$$

These coefficients distinguish time zero, the first transition and the entire later geometric tail. In particular, $(2/3)\sum_{n=2}^{\infty}(1/3)^n=1/9$. The source proves canonical marginal identities at every time and the integral/sum interchange. The accompanying finite-horizon arithmetic checks are crosschecks, not the justification for the infinite series.

The fine comparison set remains the two original starts $(0,0)$ and $(0,1)$; the coarse comparison set contains both physical starts. The resulting values are:

| Initial physical bit | Fine baseline | Fine treated | Coarse baseline | Coarse treated |
|:--|--:|--:|--:|--:|
| $0$ | $1/30$ | $11/45$ | $1/20$ | $1/4$ |
| $1$ | $7/10$ | $41/45$ | $43/60$ | $11/12$ |

Both fine differences equal $19/90$ and both coarse differences equal $1/5$. Thus the infima over the full original comparison sets satisfy

$$
\delta_F=\frac{19}{90},\qquad
\delta_C=\frac15,\qquad
|\delta_F-\delta_C|=\frac1{90}.
$$

The earlier error envelope $2/41$ remains a valid upper bound. The exact equality supplies its original source-law quantities; it does not establish an Exact GR or identify an external model. The shared time-zero term $2I(x)/3$ cancels in each intervention difference.

**Source trail.** [Original model and comparison sets](https://github.com/HMarcusWH/PermanssonLean/blob/b6ac6a0ca0de933b555454e5f7a7739d67004aa1/PermanssonResearch/Quotient/Q05ActualOriginalMarginWitnessFixture.lean); [canonical whole-path identification](https://github.com/HMarcusWH/PermanssonLean/blob/b6ac6a0ca0de933b555454e5f7a7739d67004aa1/verification/research/tranche6_q05_whole_path_identification.lean); [original-margin closure](https://github.com/HMarcusWH/PermanssonLean/blob/b6ac6a0ca0de933b555454e5f7a7739d67004aa1/verification/research/tranche7_q05_original_margin_addendum.lean). These are the merged Q-05 additions, preserved separately from the original v1.0 source baseline.

### B06.2. Local errors require both protocol visit laws: Q-04

The general localized certificate uses separate bad-history probabilities under the **true baseline** and the **true treated** finite-prefix laws. A row that baseline trajectories never visit can still matter after an admitted intervention. The reporting errors for both outputs and any initial mismatch are additional terms; they cannot be inferred from baseline visits.

`LocalizedProtocolErrors.toConstitutiveOutputErrors` connects these actual source-law bounds to the original constitutive-margin perturbation theorem on the original comparison set. The existing `LocalizedPrefixExamples.lean` fixture uses identical true/approximate models and reporting errors $1/10$ on each side. Its reported margin is $4/5$, total reporting budget $1/5$, and resulting lower bound $3/5$. This is a valid reporting-error example. It is not the defective-row example.

**The actual defective-row construction.** Retain the original `modelB`, its action-selection intervention `interventionB`, and `comparisonStay`, whose two starts are $(s,\mathrm{false})$ for $s\in\mathrm{Bool}$. The strategic update preserves $s$. Baseline action is true, and the intervention selects false. Write $x$ for the current physical bit. The true and approximate world rules are:

| Selected action | True next physical bit | Approximate next physical bit |
|:--|:--|:--|
| `true` (baseline) | $x$ | $x$ |
| `false` (treated) | `true` | $\neg x$ |

Each strategic intervention preserves its own model's physical primitive. Comparing the true world with the approximate world is a separate model approximation; that comparison is not itself labeled a strategic intervention.

All baseline induced rows agree, including rows with $x=\mathrm{true}$. The treated rows agree when $x=\mathrm{false}$ and differ maximally when $x=\mathrm{true}$: they are point masses at distinct physical outcomes, so their event total variation is exactly $1$.

Define a good history at time $n$ by its terminal physical bit being false. The actual canonical finite-prefix laws give, from either original comparison start,

$$
\Pr_{\rm baseline}(\text{bad history at }n)=0,
\qquad
\Pr_{\rm treated}(\text{bad history at }n)=
\begin{cases}0,&n=0,\\1,&n>0.\end{cases}
$$

The true and approximate baseline paths both keep the physical bit false. The true treated path begins false, true, true, while the approximate treated path begins false, true, false. For the indicator that the physical bit is true after **two transitions**, the four actual outputs are therefore:

| Output | Baseline | Treated |
|:--|--:|--:|
| True model | $0$ | $1$ |
| Approximate model, reported exactly | $0$ | $0$ |

The source connects these deterministic paths to `finitePrefixLaw` through the original canonical path-law and deterministic-orbit identities. It does not introduce an independent surrogate finite process.

The full `LocalizedProtocolErrors` object uses zero defects on good rows, zero baseline bad-visit probabilities, and the actual treated bad-visit schedule. The initial laws match and both numerical/reporting errors are zero. At horizon two its baseline budget is $0$ and treated budget is $1$. The actual treated output error is $1$, so the baseline budget cannot pay for it.

The same fixture retains the full original comparison set and converts the finite terminal score into the original regime-property interface. Its original constitutive margin is $1$ and its reported approximate margin is $0$. Hence

$$
|\widetilde\delta-\delta|=|0-1|=1
=e_{\rm baseline}+e_{\rm treated}=0+1.
$$

This is a sharp finite example of the two-sided error theorem. It does not satisfy the strict margin-greater-than-budget premise needed to retain positivity: here the original margin equals the total budget, and the approximate margin is zero.

**Added source.** [tranche10_q04_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_q04_scope_receipt_addendum.lean), namespace `PermanssonResearch.ConstitutiveQuasi.Q04ScopeReceiptAddendum`. Key declarations are `baseline_bad_visit_zero`, `treated_bad_visit_schedule`, `treated_bad_row_defect_one`, `actual_treated_output_gap_one`, `baseline_budget_cannot_pay_intervention_error`, `original_margin_one`, `reported_margin_zero` and `original_margin_error_equals_charged_budget`. The edition's compiler/negative-control status remains the explicitly injected Q-04 receipt state below.


**Reading exercise.** Why is a baseline visit bound alone insufficient? **Answer:** the intervention changes the generated law. A set of histories with zero baseline probability can have positive treated probability, so a defect there contributes to the treated output error and hence to the two-sided margin budget.

**Source trail.** [LocalizedPrefixError.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixError.lean) and [LocalizedPrefixExamples.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean). Q-04 receipt status for this edition: `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 65 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_Q-04_Receipt.json` (SHA-256 prefix `fd2cc0cf72c7`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`).

## B07. Canonical finite probability laws and exact-rational bridges

**Learning objective.** Relate finite rational tables to genuine stochastic kernels without confusing entry arithmetic with a universal path-law theorem.

A finite rational transition model supplies a matrix $K\in\mathbb Q^{n\times n}$ with $K_{ij}\ge0$ and $\sum_jK_{ij}=1$. The research library constructs a canonical finite kernel from those rational entries, and shows that the kernel's singleton transition probabilities agree with the matrix values (`rationalFiniteKernel_singleton`). Its row-sum proof gives a Markov kernel (`rationalFiniteKernel_isMarkov`).

The **zero-transition** prefix is an initial-state point mass. At **one transition**, the final-state marginal equals the specified rational kernel row. `FinitePrefixBridge.lean` explicitly documents that its particular results cover horizon zero and one; readers must look elsewhere for a separately proved arbitrary-horizon dependent-path bridge, rather than silently strengthening that file's claim. More general canonical path-law proofs exist elsewhere in the research library, each with their own assumptions.

For a fixed matrix and path $(y_0,\ldots,y_T)$, its rational word weight is the product of $T$ entries. A basic check is that the sum of the weights of every possible length-$T$ continuation from a fixed initial state equals one. This follows from row stochasticity; an implementation that forgets the initial-state convention may instead introduce a spurious transition.

**Worked check.** In the binary example, the four two-transition outcome weights for $(O,O)$, $(O,I)$, $(I,O)$ and $(I,I)$ conditional on $X_0=O$ are respectively $169/400$, $91/400$, $91/400$ and $49/400$. Their sum is $400/400$. Because the example's rows are identical, these particular values also factor as independent successive draws; that independence is **special to this example**, not a general Markov-chain assumption.

**Source correspondence.** `PermanssonResearch/ReverseSolver/CanonicalFiniteKernel.lean`, `FinitePrefixBridge.lean`, `PermanssonLean/Probability/`, `PermanssonResearch/Probability/` and `ReverseSolver/RationalKernel.lean`.

**Reader check.** Track time origin, horizon, initial-state mass, event definition, exact rational normalization and whether a result is proved for $T=0,1$ or arbitrary $T$.

### B07.1. A dependent finite history embedded into actual event total variation: Q-03

Product-shaped error bounds do not require independent failure events. The common-subkernel argument works chronologically: at each history, retain a subprobability row dominated by both conditional rows, then multiply the conditional retained-mass floors. The primitive theorem follows the actual $\alpha\rightarrow P\rightarrow U$ order; the dependent-history theorem permits the next history type and conditional row to depend on the preceding prefix.

The concrete three-stage law records $w=(b_1,(b_2,b_3))\in\mathrm{Bool}^3$. Its first stage succeeds with probability $9/10$. Conditional on prior success, the next success rates are $4/5$ and $3/4$; after failure, success is impossible. Thus the all-success atom is

$$
\nu\{(1,1,1)\}=\frac9{10}\frac45\frac34=\frac{27}{50}.
$$

All eight original atoms form a normalized finite probability law. The comparison law $\mu$ is concentrated on $(1,1,1)$. Earlier source already proved the finite half-$L^1$ value $23/50$. The new adapter constructs `ActionTrace.Row` from those same atoms and uses its actual weighted-Dirac `measure`; every singleton keeps exactly its original mass. It therefore addresses the repository's measure-based, event-supremum total variation rather than merely repeating the finite table calculation.

Take the common submeasure

$$
\xi=\frac{27}{50}\,\delta_{(1,1,1)}.
$$

The source proves $\xi\le\nu$ and $\xi\le\mu$. The common-mass theorem gives

$$
d_{\rm TV}(\nu,\mu)\le 1-\xi(\Omega)=\frac{23}{50}.
$$

The singleton event $\{(1,1,1)\}$ attains the difference $1-27/50=23/50$, proving the reverse inequality and hence

$$
d_{\rm TV}(\nu,\mu)=\frac{23}{50}
=\frac12\sum_w|\nu\{w\}-\mu\{w\}|.
$$

Dependence is visible in the actual measure. For $A=\{b_1=0\}$ and $B=\{b_2=1\}$,

$$
\nu(A)=\frac1{10},\quad \nu(B)=\frac{18}{25},\quad
\nu(A\cap B)=0\ne\frac9{125}=\nu(A)\nu(B).
$$

The retained-mass product is consequently a conditional-kernel argument; it is not evidence of unconditional independence. The finite example also does not turn a finite-prefix envelope into a uniform infinite-path bound.

**Source trail.** [DependentThreeStageSaturation.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/PermanssonResearch/Probability/DependentThreeStageSaturation.lean), [DependentHistoryCommonMass.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/PermanssonResearch/Probability/DependentHistoryCommonMass.lean), [PrimitiveProductTV.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/PermanssonResearch/Perturbation/PrimitiveProductTV.lean), and [tranche10_q03_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_q03_scope_receipt_addendum.lean). The last source's namespace is `PermanssonResearch.Certification.Tranche10Q03`; the central declarations are `dependent_measure_atom`, `common_mass_exact`, `actual_event_tv_exact`, `halfL1_eq_actual_event_tv` and `unconditional_event_product_fails`.

**Edition evidence.** `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 51 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_Q-03_Receipt.json` (SHA-256 prefix `0f60c35c1e85`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`). A finite arithmetic receipt, a named compiler/axiom receipt and an independent case-acceptance decision retain their separate meanings.

## B08. Recurrent classes, multiple limits and stationary families

**Learning objective.** Explain why a stationary distribution, a random limiting class, and an expected limiting law are distinct.

A finite stochastic transition graph decomposes into transient states and bottom recurrent classes. A finite irreducible closed class has an invariant probability law. If the chain has multiple closed classes, the class eventually entered can depend on the sample path. Its limiting empirical occupation law may therefore be **random** even though its expectation is a single deterministic probability measure. Periodic behavior requires further care: a chain can possess a stationary law even when its time-$t$ state distributions oscillate instead of converging pointwise.

**Worked counterexample.** Let

$$
K=\begin{pmatrix}1&0\\0&1\end{pmatrix}, \qquad
\mu_0=(3/5,\,2/5).
$$

Both states are absorbing. Every realized path remains forever in whichever state was selected at the start. Therefore its limiting empirical occupation law is either $\delta_0$ (probability $3/5$) or $\delta_1$ (probability $2/5$). The **expected** limiting occupation measure is $\frac35\delta_0+\frac25\delta_1$, but no realized path has that mixed empirical limit. A report that describes the expected mixture as the individual path's realized limiting law is incorrect.

C11 explicitly checks complete families of bottom-class stationary certificates for finite rational Markov matrices. `C11StationaryFamily.lean` demands exactly the computed bottom classes, with no omissions, duplications or invented entries. This is a mathematical property of the supplied matrix; it is not automatically a strategic-generator or generalized PR certificate. The native C11 provider supports 1--6 states under its own bounded schema.

**Source correspondence.** `PermanssonResearch/MultipleLimit/`, `ReverseSolver/C11StationaryFamily.lean`, `ReverseSolver/C11ClassStationaryCertificate.lean`, `ReverseSolver/RationalAbsorptionSolve.lean`, and `apps/permansson/closure-successor-c11/README.md`.

**Reader check.** A complete long-run report should state whether it means a stationary law of a class, the eventual class probabilities, an expected limit, a sample-path empirical limit, or pointwise convergence of marginals. Do not substitute one for another.

### B08.1. Physical class identity survives descriptor coincidence

C09.1 gives the original two-absorbing-law example. Physical classes remain distinct even when a constant descriptor assigns the same target. Its separate Boolean observable gives expected pathwise nonlinear score 1/2 under the equal mixture, while scoring the stationary barycenter gives 5/6. Record the observable as well as the class decomposition.

# Volume A-B consolidated exercises and answers

## Exercise 1 - Three different probabilities

Under the fictional B01 model, starting in an operating state:

1. Calculate the probability that the next state is operating.
2. Calculate the probability of being operating at both time 1 and time 2.
3. Calculate the probability of being operating at time 2.

**Answer:** (1) $13/20$; (2) $(13/20)^2=169/400$; (3) $13/20$. The second and third differ because a service can be interrupted at time 1 and restored at time 2. These answers are derived directly from the declared illustrative matrix.

## Exercise 2 - Intervention versus certification

Replace the recover-selection probability $3/4$ with $1/4$, keeping the other components fixed. What happens to one-step availability? May the resulting difference be called a certified PR?

**Answer:** Availability changes from $13/20$ to $7/20$; the one-step difference is $3/10$. **No** PR certificate follows: in the chosen region $B=\{x=O\}$ the baseline process fails exact invariance. The example is an illustrative typed-model comparison, not a certification of the full regime predicate.

## Exercise 3 - Initial mixture versus realized limit

For a two-state identity transition matrix with initial law $(3/5,2/5)$, give the realized occupation limit and the expected occupation limit.

**Answer:** The realized limit is randomly $\delta_0$ or $\delta_1$ depending on $Y_0$; the expected limit is $(3/5)\delta_0+(2/5)\delta_1$. The reported mixture must be identified as an expectation, not a per-path fact.

## Exercise 4 - Proof status classification

Classify these statements:

- "The induced kernel is Markov under the typed source assumptions."
- "A particular finite instance's independent checker returned `PASS`."
- "A source-bound Lean candidate was emitted and its bytes rechecked."
- "An observed conflict is therefore a certified Permansson regime."

**Answer:** (a) Lean-checked general theorem in the applicable scope; (b) numerically checked finite input; (c) source-bound candidate only, unless separately compiled; (d) unsupported conclusion, requiring additional exact model and regime/constitution certification as well as distinct empirical relevance evidence.

# Technical source appendix

The 12 foundation chapters establish boundaries that apply equally to the subsequent 34 chapters of this complete edition:

- **C01--C15:** frozen D0 menus, controlled D1 laws (fully observed, history-dependent, nonstationary), D2 residence, exact rational LP/Farkas, partial observation, robust nature, constitutive grammar, C10/C11 rational proofs, rational graph absorption, infinite safety, occupancy polytopes, multiagent protocols and specialized economic/nonfinite theorems.
- **D01--D07:** the 26 exact numeric profile commands and the two **separate** native C10/C11 providers; input schemas and independent checkers; the two-command `lp-propose` then `lp-check` certificate handoff.
- **E01--E08:** independent checking, 24 source-bound Lean bridges, typed reports, artifact ingestion, read-only federation, CI, historical release identity, and the legacy Application Standard. Numeric report output, external compiler evidence, and scientific certification remain different.
- **F01--F04:** historical source boundaries, entirely reproducible neutral fixtures and answer keys, claim-status matrix and deferred research/engineering work. The dated PRT Russia--Ukraine and MIDR papers may illustrate evidence provenance and *why* a descriptive history is not a causal intervention, but are not solver-identified models.

The coverage artifact `Permansson_46_Chapter_Reference_Map_2026-11-19.json` remains the source-attachment ledger for all 46 authored chapters. It is a planning and audit crosswalk, not an additional source of mathematical theorems.

# Edition and audit note

This manuscript was constructed against the **locally mounted source**, not general recollection. Key claims were checked against `StrategicWorld/Model.lean`, `StrategicWorld/InducedKernel.lean`, `Regime/Specification.lean`, `Regime/Occupation.lean`, `Regime/Persistence.lean`, `Regime/QuasiStationary.lean`, `Regime/Constitution.lean`, `Regime/Perturbation.lean`, `ReverseSolver/CanonicalFiniteKernel.lean`, `ReverseSolver/FinitePrefixBridge.lean`, `ReverseSolver/C11StationaryFamily.lean`, the Formalization Map, and the successor application's released documentation. Specialized theorem statements remain bound to their declared hypotheses; source-level correspondence checks do not substitute for independent claim acceptance.

The working examples in this volume were constructed for the guide and analytically checked; they are **not** additional profiles shipped by `permansson-app`, and their calculations do not constitute independent Lean proof objects. The current edition includes source-path and cross-reference checks. Independent logical acceptance of every natural-language theorem paraphrase is not claimed.


\newpage

# Volume C — Advanced Mathematics and the Reverse Solver

> **Mathematical scope.** Volume C explains formal reverse-solver and adjacent mathematics with illustrative, fictional public-service examples. It is not a tactical military planning manual, does not recommend targets or military actions, and does not imply the model identifies actual conflict dynamics.
>
> **Frozen source reference.** [`HMarcusWH/PermanssonLean`](https://github.com/HMarcusWH/PermanssonLean/tree/89ac97cb8bcaad0c47c421209dd2e103db6d60ee), commit `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`.

> **Source tree:** `cf3d19b5eaa3756fe5c2e392367b9066330e1a4b`. The published numerical application v0.2.0 was cut from an earlier commit, `63a66c82a9ece4361f646ee13b6711192f831406`. This edition cites source-level declarations; its prose and examples do not constitute fresh mathematical certification or an independent Lean run.

# How to use Volume C

Volume A defined model authority and version identity. Volume B introduced the strategic-world process $(\alpha,P,U)$, the induced kernel $K$, path laws, generated regimes, invariance, occupation, typed interventions, and model-sensitive comparisons. Volume C starts from **a declared mathematical world** and asks what kinds of comparisons and certificates are actually available. It deliberately separates the research proofs in `PermanssonResearch/` from the narrower executable profiles in `apps/permansson/application-successor/`.

A useful reader's checklist applies to every purported optimizer:

1. What is the **mathematical object** being evaluated (a finite matrix, a genuine typed path law, a stationary selector, a history-dependent strategy, or a limiting occupation property)?
2. What is the **admissible policy class** and the **information chronology** available to it?
3. Is the outcome a **finite-horizon event**, a long-run limit, or a nonlinear function of a stationary class distribution?
4. Which quantifiers are proved: *one example*, *every member of a finite list*, *all history-dependent policies in a constructed class*, or *all initial laws*?
5. Is there a separately proved bridge from numerical inputs to the typed $\alpha/P/U$ primitives? Does a proposed proof file actually compile, or only pass byte checks?
6. What would **refute** the conclusion: a missing action, a changed deadline, an unobserved state, a nonrectangular uncertainty model, an infeasible constraint, or a failed theorem hypothesis?

## Reading key

**Definition** names an object. **Lean-checked in source CI** means a declaration is admitted by the pinned compiler with its actual assumptions; it does not imply that arbitrary external data satisfy those assumptions. **Exact numerical receipt** means the input-specific arithmetic was independently verified. **Research-only** means the theorem's mathematical scope exceeds the released CLI. **Open** names a missing generalization rather than a failure of a valid narrower theorem.

# C01. D0: fixed finite menus of admissible interventions

**Question.** Suppose an analyst has a short list of already-validated, stationary alternatives for a fictional emergency service. Which alternative yields the greatest probability of reaching a declared operating condition before entering a forbidden condition by a specified deadline?

The D0 object is a nonempty finite indexed menu. Every index $i$ denotes **one already-typed admissible strategic intervention** of a common `StrategicWorldModel`. Selecting $i$ fixes that replacement for all $T$ transitions. The world primitive $P$ remains unchanged by an admissible strategic replacement. An index is *not* a general policy that can switch models based on intermediate observations.

For disjoint goal $G$ and forbidden $D$, define the first-hit event

$$
E_{G\prec D,T}=\{(y_0,\ldots,y_T):\exists t\le T,\ y_t\in G,\ \forall j<t,\ y_j\notin D\}.
$$

Time zero counts. If the initial state is in the goal, success has already occurred. If a path first reaches forbidden before goal, it fails even if goal is reached later. The process need not physically absorb at either set: **terminal status is for evaluating the event**. With the induced kernel $K_i$, the objective for a specified initial $y$ is

$$v_i(y)=\Pr^{K_i}_y(E_{G\prec D,T}),\qquad i^*\in\arg\max_{i\in I}v_i(y).$$

`FrozenMenu.lean` defines `FrozenMenu`, `memberValue`, `optimalMember` and `optimalMember_dominates`; their theorem scopes are finite-menu membership and dominance. `RationalKernel.lean` defines the exact rational transition matrix and backward first-hit recursion. `FiniteEvaluation.lean` enumerates forward successor words. The D0 research documentation distinguishes the canonical finite-prefix correspondence, the constructed typed-world factorization, and the independent Python evaluator. The finite menu is a **quantifier boundary**, not a presentation convenience.

**Independent neutral calculation.** Let states be $s$ (interrupted), $g$ (restored), and $d$ (unavailable). With a two-transition deadline, consider two fixed alternatives. Alternative A moves from $s$ to $g$ with probability $1/4$, otherwise returns to $s$ with probability $3/4$; B moves from $s$ to $g$ with probability $1/2$, otherwise moves to $d$. Goal/forbidden states can be specified as absorbing for this particular illustrative example, although D0 does not require that convention. Then

$$v_A(s;2)=\frac14+\frac34\cdot\frac14=\frac7{16},\qquad
v_B(s;2)=\frac12.$$

Among the **declared two alternatives**, B is the D0 winner at horizon two. Nothing follows about a third, unlisted alternative. If every listed value equals zero, D0 implies no *listed* candidate succeeds under that event and deadline. It does not establish impossibility under all imaginable actions.

**Proof trail.** [`docs/D0_FROZEN_MENU.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/D0_FROZEN_MENU.md); `PermanssonResearch/ReverseSolver/` (modules: `FrozenMenu.lean`, `RationalKernel.lean`, `FiniteEvaluation.lean`, `FinitePrefixBridge.lean`, `EndToEndCertificate.lean`); `verification/research/d0_finite_solver.py`. D0-F's independent Python receipt is not a proof that a user-supplied numerical matrix equals an arbitrary external model's induced kernel.

**Failure test.** Remove a menu entry, switch the time horizon, or permit state-dependent switching. The resulting optimization problem is different. A comparison result remains correct only inside its original assumptions.

## C01.1. A menu also carries a compatibility obligation

A D0 menu index is already a typed admitted replacement. Constructing it from row patches requires more than normalizing the final matrix: simultaneous patches must agree wherever their regions overlap, and the frozen grammar must admit their selected block. C08.1 supplies an actual two-choice certified menu with distinct, overlapping compatible patches, along with a proof that two conflicting patches cannot occur together in any certified choice on that source.

The distinction also matters for uncertainty. Choosing a single whole model at time zero and selecting a new uncertainty row after each observation are different strategy classes. C07.1 gives a source-bound two-stage event with committed value $9/100$ and rectangular value $1/100$, including the bridge to the actual chronological game law. Neither extension changes D0's menu-relative optimality quantifier.

# C02. D1: state-dependent finite-horizon Bellman control

**Question.** What changes if the system can observe its current condition and choose an admissible control before each subsequent transition?

D1-A replaces a global frozen choice with a `FiniteControlSystem C n`. Each state $y$ has a nonempty local menu $C(y)$; every control supplies a certified exact rational transition matrix. A `StateFeedback` is a mapping from state to an admissible control. At each state it selects a row of the appropriate control matrix. In the constructed typed realization, these controls alter the action-selection mechanism while preserving the declared world-transition and strategic-update primitives.

For a goal/forbidden pair, D1-B's Bellman recursion is

$$
V_0(y)=\mathbf1_G(y),\qquad
V_{t+1}(y)=\begin{cases}
1 & y\in G,\\
0 & y\in D,\\
\displaystyle\max_{c\in C(y)}\sum_z K_c(y,z)V_t(z) & \text{otherwise}.
\end{cases}
$$

The schedule is indexed by **transitions remaining**. At elapsed time $k$ under original deadline $T$, the rule uses the remaining count $T-k$, before the next transition. This prevents a common error: restarting a deadline-$t$ problem is not necessarily the same as restricting a deadline-$T$ policy's observed prefix.

**Worked two-transition calculation.** Reuse the fictional $s,g,d$ system of C01. With one transition left, choose B: $V_1(s)=1/2$. With two left, choose A now and then the best one-transition continuation if the system returns to $s$:

$$\text{A first:}\ \frac14+\frac34\cdot\frac12=\frac58,
\qquad\text{B first:}\ \frac12.$$

Thus $V_2(s)=5/8$. The optimal nonstationary schedule outperforms the fixed B option $(1/2)$ and the fixed A option $(7/16)$. This is the repository's documented deadline-sensitive exact example. It is a **constructed mathematical witness**, not a claim that one choice is universally preferable in an actual service system.

D1-B proves optimality over its declared class of deterministic remaining-horizon Markov schedules. Later research source adds genuine nonstationary canonical prefix-law transport (`NonstationaryPrefixKernel.lean`, `NonstationaryForward.lean`, `NonstationaryOptimality.lean`). A local Bellman equation alone must not be silently presented as a path-measure theorem.

**Proof trail.** [`docs/D1_CONTROLLED_KERNEL.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/D1_CONTROLLED_KERNEL.md); [`docs/D1_BELLMAN.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/D1_BELLMAN.md); `PermanssonResearch/ReverseSolver/` (modules: `ControlledKernel.lean`, `Bellman.lean`, `BellmanOptimality.lean`, `NonstationaryPrefixKernel.lean`, `NonstationaryOptimality.lean`).

**Boundary.** “State-feedback optimal” does not mean optimal over all partial-information or adversarially changing environments. The released `finite-bellman` numerical profile is bounded and has its own input schema and independent checker; it is not an unrestricted implementation of every D1 research theorem.

# C03. D1: histories, nonstationarity, and typed path-law transport

The next question is whether a controller that remembers the **complete observed history** can outperform the Bellman representative. The history may contain information that a current-state-only rule discards; the theorem must quantify over a precisely described admissible class rather than appealing vaguely to “memory.”

`HistoryPolicy.lean` represents a history with $i$ elapsed transitions as the observations $y_0,\ldots,y_i$ and selects a control permitted at the final state. The original deadline $D$ stays fixed. The choice cannot look ahead to future observations. `HistoryPrefixKernel.lean` constructs genuine, normalized prefix laws. `HistoryPathAtoms.lean` proves path-atom/product identities. `HistoryContinuation.lean` carries an explicit unresolved/won/lost event status, so a previously completed first-hit event remains completed even if later physical states change. `HistoryForwardMeasure.lean` connects the real history-conditioned probability to the Bellman bound.

For the declared finite, fully observed rational first-hit problem, the source establishes

$$
\Pr^{\sigma}_{y,D}(E_{G\prec D_f,D})\le V_D(y)
\quad\text{for every admissible deterministic history policy }\sigma,
$$

with equality attained by embedding a maximizing remaining-horizon Markov schedule. Here $D_f$ denotes the forbidden set, to avoid confusing it with deadline $D$. The theorem proves **sufficiency for the chosen first-hit objective**, not equality of every policy's entire path law. A history policy can depend differently on two positive-probability prefixes that reconverge at the same current state and elapsed time. That behavior is allowed, even though an attaining Markov representative exists for this objective.

A second, critical interface is the **typed** history extension. `HistoryTypedFeedback.lean` constructs a feedback replacement from a full observed prefix, filling unused state rows legally without changing the currently selected row. `HistoryTypedKernel.lean` builds the actual history-conditioned $\alpha\rightarrow P\rightarrow U$ kernel with fixed $P,U$ at each history. `HistoryTypedPrefix.lean`, `HistoryTypedAtoms.lean`, `HistoryTypedTransport.lean` and `HistoryTypedHitting.lean` establish the finite-prefix transport and first-hit correspondence for the constructed `Unit × Fin n` realization. A history-dependent controller is not the same object as a single stationary D0 `AdmissibleStrategicIntervention`.

**Chronology exercise.** Consider a service whose maintenance protocol at time 1 depends on the original two-step deadline. After one observed transition the protocol still has **one** transition remaining. Do not rebuild a new horizon-one planning process and assume its starting information matches the original time-one history. The prefix within a fixed deadline and a fresh shorter problem may be different laws.

**Proof trail.** [`docs/D1_HISTORY_DEPENDENT.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/D1_HISTORY_DEPENDENT.md), [`docs/D1_TYPED_HISTORY_DEPENDENT.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/D1_TYPED_HISTORY_DEPENDENT.md), `PermanssonResearch/ReverseSolver/` (modules: `HistoryPolicy.lean`, `HistoryForwardMeasure.lean`, `HistoryTypedKernel.lean`, `HistoryTypedTransport.lean`, `HistoryTypedHitting.lean`).

**Boundary.** No result here identifies arbitrary external $\alpha/P/U$ models or establishes optimality of randomized, partially observed, or unrestricted controller classes. Those require different theorems, some of which appear in later chapters with their own assumptions.

# C04. D2: reaching, residing, avoiding, and switching

A condition can be reached without being sustained. For a fictional emergency communications service, “operating by Friday” and “operating continuously for the following three checks” are distinct measurable events. D2 therefore treats the literal path event as the authority and derives evaluators or monitor states from it.

For a target region $G$, entry deadline $T$ and residence length $m$ **in transitions after entry**, the *retryable entry-by residence* event is

$$
E_{\mathrm{res}}(G,T,m)
=\{\exists e\le T:\ \forall j\in\{0,\ldots,m\},\ Y_{e+j}\in G\}.
$$

It requires $m+1$ consecutive target observations, including the entry observation, and may inspect the path through transition $T+m$. A path beginning in $G$ can use entry $e=0$. A failed early visit may be retried. This differs from **first-ever-entry-only** residence, where the initial failed visit prevents a later retry. It also differs from *completed-by-$D$*, which requires $e+m\le D$ and therefore has an earlier effective entry deadline.

**Literal path exercise.** Let $G=\{\mathrm{on}\}$ and a four-observation path be `off, on, off, on`. Reaching $G$ occurs at observation one. Residence with $m=1$ is **not** achieved by observation three because there are no two consecutive `on` observations. For `off, on, on, off`, the same residence objective succeeds from entry one. For `on, off, on, on`, the retryable event succeeds at entry two, whereas a first-ever-entry interpretation would fail after the initial visit ended prematurely.

`ResidenceEvent.lean` proves a block-of-$m+1$ interpretation (`hasRun_iff_block`), initialization and deadline semantics. `ResidenceValue.lean` connects the literal event with rational forward enumeration, actual prefix-law event probability, and value recursion. `ResidenceContracts.lean` reuses the D1 first-hit result. The research documentation explicitly distinguishes product-clock **calculation and testing** from a general Lean proof reducing every controller to a minimal clock-state representation.

The released `finite-residence` application profile has a documented, bounded monitor: target and danger sets, `entry_by` or `completion_by`, and finite dwell counts. Its separate avoid/residence modes have specific danger-check ordering. **Through-horizon risk is not automatically evaluated** simply because an avoid label appears. Once a designated success event occurs, subsequent danger cannot be silently reintroduced into that earlier event unless a different property is defined.

**Proof trail.** [`docs/D2_RESIDENCE_OBJECTIVE.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/D2_RESIDENCE_OBJECTIVE.md); [`NUMERIC_RESIDENCE_NONLINEAR.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_RESIDENCE_NONLINEAR.md); `PermanssonResearch/ReverseSolver/` (modules: `ResidenceEvent.lean`, `ResidenceValue.lean`, `ResidenceContracts.lean`, `FirstEntryMonitor.lean`, `AvoidResidenceMonitor.lean`).

**Boundary.** Hitting, completion, retryable residence, first-ever entry, and avoiding a separate danger region are distinct estimands. The guide must not rename one output as another.

# C05. Risk constraints, occupancy flows, exact LP and infeasibility

Risk constraints are meaningful only when stated as actual inequalities on the **same modeled distribution** as the objective. A solution of an unconstrained problem need not satisfy a risk cap. Conversely, a failed bounded candidate search cannot be relabeled a proof that the feasible set is empty.

In the research flow model, a finite controlled system specifies time-dependent rational rows and permitted controls. A behavioral policy may depend on the complete observed state/control history. A flow includes state masses $x_t(y)$ and state-action masses $q_t(y,c)$ satisfying

$$\sum_c q_t(y,c)=x_t(y),\qquad
x_{t+1}(z)=\sum_{y,c}q_t(y,c)K_{t,c}(y,z),
\quad x_0(y)=\mu(y).$$

Nonnegativity and feasibility conditions are essential. `FiniteOccupancyReconstruction.lean` proves that feasible finite flows admit legal reconstructed behavioral policies, including a defined fallback on zero-mass histories. `FlowPolicyOptimality.lean` transports actual terminal scores to flow values and relates the rational optimizer to the complete admitted behavioral class in that finite research setting. The finite-polytope branch (`PolytopeCompleteness.lean`, `PolytopeOptimizer.lean`) establishes the existence and optimality of rational candidates in its explicit bounded rational inequality representation.

The released application makes narrower claims. Its `one-step-risk` profile constructs controlled next-state rows from the supplied typed $P,U$ and checks a one-step risk cap under an initial law. The engine returns a proposed primal/dual certificate; an independent checker **rebuilds the original model and its risk coefficients** and verifies the certificate. The consumer `lp-check` takes an existing `lp-propose` certificate; it is not a second optimizer with an unrelated request fixture.

**Worked neutral risk tradeoff.** For a hypothetical test service, suppose a conservative option yields quality score $4/5$ and failure probability $0$, while a trial option yields score $9/10$ and failure probability $1/10$. Mix the trial option with probability $p$. Then

$$R(p)=\frac45+\frac{p}{10},\qquad q(p)=\frac{p}{10}.
$$

A declared risk cap $q(p)\le1/20$ requires $p\le1/2$, and the best score in this illustrative one-stage linear model is $R(1/2)=17/20$. The unconstrained maximizer $p=1$ has score $9/10$ but is **inadmissible under the risk cap**. This is merely a two-option teaching model; it is not the repository's official packaged receipt and does not claim Lean compilation.

For infeasibility, the released `one-step-risk-infeasibility` profile computes the least admissible next-step risk from the original rows and proves a positive gap against the cap using a normalized Farkas-style receipt. The documented packaged example has least risk $7/16$ against cap $1/4$, a shortfall of $3/16$. That is stronger evidence than “the proposal search found nothing.”

**Proof trail.** `PermanssonResearch/ReverseSolver/` (modules: `FiniteOccupancyModel.lean`, `FiniteOccupancyReconstruction.lean`, `FlowPolicyOptimality.lean`, `PolytopeOptimizer.lean`, `PolytopeCompleteness.lean`); [`NUMERIC_RISK_OCCUPANCY.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_RISK_OCCUPANCY.md); `apps/permansson/application-successor/src/permansson_app/receipts/`.

**Boundary.** Finite flow optimization, one-step risk-cap optimization, through-horizon risk monitors, and exact infeasibility are different contracts. Do not promote a local LP receipt into an unbounded, long-horizon guarantee.

# C06. Beliefs, partial observation, information chronology and private draws

A controlled model can be mathematically incorrect even with perfectly normalized kernels if it gives a decision-maker information that is unavailable at decision time. This is an **information-structure problem**, not a numerical rounding problem. The repository contains several deliberately different information structures; the guide must not collapse them into “the controller knows the state.”

In the fully observed D1 model, the next control can depend on current $y$. In a partially observed model, a hidden state $z$ has a belief distribution $b(z)$, and a visible observation $o$ is generated by a declared channel. With observation likelihood $Q(o\mid z)$ and prior $b(z)$, Bayes filtering gives, for a positive-likelihood observation,

$$b(z\mid o)=\frac{b(z)Q(o\mid z)}{\sum_{z'}b(z')Q(o\mid z')}.$$

When the denominator is zero, the observation is **unreachable**, not a demand to divide by zero, invent a posterior, or grant additional information. `BeliefFilter.lean` constructs unnormalized forward masses independently of normalized posteriors and proves a factorization of the two, including a zero-likelihood branch. `BeliefChronology.lean` relates observable-word/hidden-endpoint marginals to the actual chronological law. This is important because an apparently plausible filter can still be paired with the wrong order of actions, observations, and state changes.

**Illustrative posterior.** Let a fictional pump system be healthy/damaged with prior probabilities $1/2$ each. A green diagnostic appears with probabilities $3/4$ when healthy and $1/4$ when damaged. Then $P(\mathrm{green})=1/2$, and the posterior probability of healthy given green is $3/4$. This statement concerns the diagnostic model alone; it does not tell us which repair to make. A decision rule requires a separate action-feasibility relation, transition law, reward, and observation-time convention.

The released `one-step-belief` profile has the order **hidden initial world → observation → shared admissible action → world update**. An action must be feasible in **every positive-posterior-support hidden state** compatible with that observation. The example shipped by the application uses a healthy/damaged system, green/red/unseen signals, and leave/repair choices. Its exact expected score is $13/16$ under observation-conditioned selection versus $3/4$ for its declared blind-policy benchmark; the difference $1/16$ is a bounded one-step value-of-observation calculation. The `unseen` signal has no posterior because it is unreachable. This does not prove the value of sensing generally, nor the value of a particular real sensor.

The `finite-belief-tree` profile is a distinct multistage bounded calculation. It cannot be described as if the one-step profile silently supported arbitrary observation histories. The `finite-private-stage` profile is different again: the second player observes the **mixed strategy** $p$ but not the privately realized action $c\sim p$. Its one-stage value is

$$\max_{p\in\Delta(C)}\min_{\theta\in\Theta}\sum_c p(c)Q(\theta,c).$$

This differs from a revealed-control model in which the second player observes $c$ before choosing $\theta$. `PrivateControlStageModel.lean` formalizes the chronology; `PrivateControlStageOptimizer.lean` constructs an exact finite rational candidate and verified bounds. The successor application's private-stage checker validates the returned controller and nature distributions independently.

**Proof trail.** `PermanssonResearch/ReverseSolver/` (modules: `BeliefHistory.lean`, `BeliefFilter.lean`, `BeliefChronology.lean`, `PrivateControlStageModel.lean`, `PrivateControlStageOptimizer.lean`); [`NUMERIC_BELIEF_CONTROL.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_BELIEF_CONTROL.md), [`NUMERIC_MULTISTAGE_BELIEF.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_MULTISTAGE_BELIEF.md), [`NUMERIC_PRIVATE_STAGE.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_PRIVATE_STAGE.md).

**Failure test.** Shift the observation to after the action; allow controls forbidden in a hidden state; or provide the private realization to the adversary. Each change defines a new game and may change the value even if all probabilities still sum to one.

## C06.1. Two reachable histories under one prior: D-06

The relevant counterexample compares histories generated by the **same model, same initial law and same chronological process**. It does not merely compare separate priors that produce the same current observation.

The fixture starts with a false hidden completion flag, draws a fair action, updates the flag to that action and emits a Unit-valued physical readout. The two action/readout histories each have probability $1/2$. Both end at the same current physical readout, but their completion-flag posteriors and completion values differ:

| Reachable history | Probability | Posterior completion flag | Completion value at time one |
|:--|--:|:--|--:|
| Action false, sole physical readout | $1/2$ | Point mass at false | $0$ |
| Action true, sole physical readout | $1/2$ | Point mass at true | $1$ |

These are time-one values with **zero transitions remaining**, obtained from the actual reachable histories. Since the current physical readout is the same in both rows, a function of that readout alone would have to return the same value twice. It cannot represent both $0$ and $1$. The controller uses its recorded action; it is not granted a peek at an unobserved hidden variable.

The existing older two-prior remembered-bit fixture and the hidden-state guessing fixture answer different questions. The former is not this one-prior reachable-history argument. The latter demonstrates how an unauthorized information advantage can turn a legitimate $1/2$ into a falsely claimed $1$. The zero-likelihood branch is another distinct control: an unreachable observation contributes zero expected reward and does not create a usable posterior.

The general finite belief theorem is a separate positive result. Under its chronology, feasibility and actual-law hypotheses, the declared sufficient belief state yields an attaining control representation for the specified objective. The counterexample only excludes the particular insufficient **current physical readout**. It does not prove that the full posterior is the unique or smallest possible sufficient statistic.

**Source trail.** [D-06 named scope and source-law addendum](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/tranche9_d06_scope_receipt_addendum.lean). The Tranche 9 packet includes 39 named declarations and three semantic compiler controls for this case. Its 10 new named facts include previously anonymous original fixture conclusions and the two reachable-value statements. These are source-case receipts, not independent scholarly acceptance or an enlargement of the released belief profile limits.

**Exercise.** Could the two values be represented by including the remembered action in the information state? **Answer:** yes for this fixture. The counterexample refutes dependence on the Unit physical readout alone; it does not rule out a smaller sufficient augmented statistic tailored to this model.

# C07. Robust alternatives, rectangular uncertainty and metric perturbation

Uncertainty about a transition kernel is not one universal object. Three mathematically distinct questions are: (i) how a fixed model's outcome changes under a bounded perturbation, (ii) the worst result among a **set of complete models chosen once**, and (iii) the worst result when an alternative mechanism can be selected separately at each chronological decision node. The third is *rectangular* uncertainty; it is generally more permissive to the uncertainty selector than the second.

In the finite rectangular research game, a state $y$ and control $c$ are followed by an allowed nature choice $\theta$ and a transition matrix $K_{c,\theta}$. The source explicitly states that nature observes the **realized control** before choosing its row and may choose again at later nodes. A finite-horizon value recursion takes the form

$$V_{t+1}(y)=\max_{c\in C(y)}\min_{\theta\in\Theta_t(y,c)}\sum_z K_{t,c,\theta}(y,z)V_t(z),$$

subject to the exact policy and chronology hypotheses of the relevant theorem. `RectangularFiniteGame.lean` and `RectangularGameLaw.lean` define the actual chronological two-party finite law and associated saddle relation. There are real behavioral-history quantifiers in those source files; their presence must not be erased when explaining the scope of a certificate.

For a **fixed declared controller**, the packaged `finite-robust-nature` numeric report distinguishes three outputs:

- `rectangular_optimal`: optimization over its stated controller class with rowwise nature choices;
- `fixed_policy_rectangular`: worst-case rowwise choices under the caller's fixed policy;
- `fixed_policy_committed`: a single complete model chosen at time zero under that same fixed policy.

For the same fixed policy and comparison state, the documented inequality is

$$V_{\mathrm{fixed,rectangular}}(y)\le V_{\mathrm{fixed,committed}}(y).$$

It does **not** follow that `rectangular_optimal` is also the solution of an independently optimized committed-model game. The two questions use different uncertainty strategy classes. `CommittedVsRectangularPathFixture.lean` supplies a concrete separating full-path event example; a scalar endpoint score may conceal such differences.

**Fixed-model metric perturbation addresses the first question above.** The `PermanssonResearch/Perturbation/` family develops finite primitive distances, total-variation controls, couplings, contractivity and occupation sensitivity. Perturbation certificates are conditional on stated norms, bounds, state correspondence and contraction or regenerative hypotheses. If a prefix-law error is bounded by $\varepsilon_T$, the interpretation must identify both the event and the horizon, not merely say “the model is within epsilon.” A long-horizon bound need not remain useful when errors accumulate or the required contraction fails.

**Neutral testing procedure.** On a fictional public-service model, pin two alternative stochastic matrices and evaluate their outcomes separately. Then construct the rowwise uncertainty family and document whether it permits switching models between observations. Report the resulting values under separate headings. Do not combine the worst number from one contract with the proof language of another.

**Proof trail.** `PermanssonResearch/ReverseSolver/` (modules: `RectangularFiniteGame.lean`, `RectangularGameLaw.lean`, `CommittedVsRectangularPathFixture.lean`), `PermanssonResearch/Perturbation/`, [`NUMERIC_ROBUST_NATURE.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_ROBUST_NATURE.md), [`NUMERIC_METRIC.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_METRIC.md).

**Boundary.** A robust calculation does not validate the set of alternative worlds chosen by the modeler. Different model-selection chronologies, metrics, and uncertainty couplings cannot be silently substituted.

## C07.1. An actual-law bridge for the committed/rectangular separation: D-05

The original two-stage source has two nature models, $\theta=0$ and $\theta=1$, whose success rates are reversed across stages:

| Complete model | First-stage success | Second-stage success | Both-stage success when committed |
|:--|--:|--:|--:|
| $\theta=0$ | $1/10$ | $9/10$ | $9/100$ |
| $\theta=1$ | $9/10$ | $1/10$ | $9/100$ |

A nature selector committed to either complete model gives the same survival-event probability $9/100$. A rectangular selector can choose $0$ first and $1$ second, giving $(1/10)(1/10)=1/100$. The new source bridge puts these quantities inside the existing `RectangularFiniteGame` and `RectangularGameLaw` interfaces.

The constructed game has one controller action, two physical states and horizon two. State $0$ is absorbing failure; state $1$ is still alive. From state $1$, the chosen nature row samples the original stage-specific success probability. The terminal reward is the indicator of state $1$. The comparison starts in state $1$ at time $0$, before any transitions. This construction preserves the expectation of the original event “both stages succeeded.” Its absorbing trace does not record a raw second Bernoulli outcome after an earlier failure, so it does not assert equality of differently typed full path laws.

The declaration `path_event_eq_game_payoff` identifies the original event expectation with `lawPayoff` for each of the four fixed row pairs. More strongly, the existing actual-law saddle theorem supplies

$$
\frac1{100}\le
\operatorname{lawPayoff}(\sigma,\eta)
\quad\text{for every admitted behavioral controller }\sigma
\text{ and nature strategy }\eta.
$$

Nature may use arbitrary admitted real weights and complete observed histories. There is only one controller action, so all behavioral controllers coincide. The specified false-then-true nature attains $1/100$, establishing the actual rectangular minimum over that full declared class. The committed minimum over the two complete models remains $9/100$.

Equal values for the chosen success event do not identify complete laws. In the original unabsorbed two-outcome path law, the atom $(\mathrm{false},\mathrm{true})$ has masses $81/100$ and $1/100$ for the two committed models. Thus their whole path laws differ despite agreeing on the success event.

**Source trail.** [tranche10_d05_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_d05_scope_receipt_addendum.lean). The namespace is `PermanssonResearch.ReverseSolver.D05ScopeReceiptAddendum`; central declarations are `path_event_eq_game_payoff`, `rectangular_nature_payoff_lower`, `rectangular_actual_minimum`, `committed_game_minimum` and `committed_path_laws_differ`. The event/expectation bridge closes a concrete interface gap; it does not solve a general optimized committed-model game or change the released `finite-robust-nature` reflection bound.

**Edition evidence.** `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 47 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_D-05_Receipt.json` (SHA-256 prefix `d89bd1432c5a`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`). 

**Exercise.** Does the equality of the two committed success probabilities imply their path laws agree? **Answer:** no. A single event can have the same probability under different laws; the explicitly unequal off-event atom refutes full-law equality.

# C08. Intervention grammars, interaction and constitution

The set of allowed modifications is itself mathematical structure. `PermanssonResearch/GrammarRobust/` distinguishes physical row patches (atoms), partitions of those atoms into declared semantic components, and a frozen predicate specifying which blocks of components are admitted. Even if two named components are each individually meaningful, their joint modification may be forbidden. Conversely, a joint modification may be admitted when neither singleton is.

Write $\Gamma$ for the set of admitted blocks $I$, and $J_I$ for the typed intervention generated by that block. Under a baseline path law $\mathbb P$, a declared path-law property $\psi$ and distance $d$, the measured effect is conceptually

$$\Delta_I(y)=d\!\left(\psi(\mathbb P_y),\ \psi(\mathbb P_y^{J_I})\right).$$

A positive finite-horizon effect is not automatically a certified Permansson Regime. Regime constitution additionally requires the relevant Exact GR, a declared comparison set $B_1$, an eligible strategic-generator change and the appropriate lower-bound or non-nullness condition under the exact formal definition. A *measurement ablation* that deletes evidence rows is not automatically such an intervention.

**Joint-only effect.** Consider a fictional service property with the following declared effect table:

| Admitted block | Effect value |
|:--|--:|
| $\varnothing$ | $0$ |
| $\{a\}$ | $0$ |
| $\{b\}$ | $0$ |
| $\{a,b\}$ | $1$ |

Neither singleton has a positive effect, but the joint block does. This is the research program's OR-type interaction idea. An AND-type constructed witness may produce two incomparable minimal positive singleton blocks; an XOR-type witness may **lose** a singleton effect when another component is added. These counterexamples make it invalid to assume monotonicity, additivity or that componentwise ranking exhausts the response geometry.

The `GrammarRobust` source includes actual Boolean baseline and intervention kernels, original-path-law margin constructions, refinement/coarsening transport, and counterexamples. It distinguishes *order isomorphism* (preserving proper-subblock order) from merely matching effect values under arbitrary relabeling. A coarse component can hide a finer positive dependency; minimality under a coarse grammar need not be global minimality in a refined grammar.

A separate `ConstitutiveQuasi/` family develops bounded finite-horizon error and robustness certificates. `ReverseSolver/ConstitutiveCertificateCheck.lean` contains a finite margin-receipt checker. The successor application's `finite-grammar`, `finite-adaptive-grammar`, `finite-cq1`, and related profiles expose only their **declared bounded numerical semantics**. They are not licenses to replace original path-law properties with an arbitrary score of convenience.

**Engineering reading.** Before describing a block as “minimal,” record (a) the frozen grammar, (b) the physical atom bank, (c) the comparison set, (d) the path-law property, and (e) the subblock ordering against which minimality is asserted. Without those five inputs, “minimal intervention” is ambiguous.

**Proof trail.** [Lane B grammar specification](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/LANE_B_PARTITION_GRAMMAR_CONSTITUTION.md); [CQ-1 certificate specification](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/CQ1_FINITE_CONSTITUTIVE_CERTIFICATE.md); `PermanssonResearch/{GrammarRobust,ConstitutiveQuasi}/`; `PermanssonResearch/ReverseSolver/` (modules: `ConstitutiveCertificateCheck.lean`, `ExecutableConstitutiveSelection.lean`).

**Boundary.** Grammar-relative optimality or minimality is not a universal physical minimum. Positive numerical effects do not remove the separate Exact GR and constitutive-policy proof obligations.

## C08.1. Compatible overlap, conflicting rows and actual menu admission: D-08

The concrete Tranche 9 menu is built from the original Boolean strategic-world model. One action patch is localized to a single state $q_1$; a wider patch acts on the full region. Their regions overlap and the patches are distinct, but both prescribe the same false action on the overlap. They therefore satisfy the compatibility premise required for simultaneous use. The constructed `CertifiedMenu` contains the unchanged choice and this compatible two-patch choice, with original-world preservation, exact typed induced rows and row normalization proved for both.

A different pair prescribes false and true on the same localized region. No choice in any `CertifiedMenu` on the source can contain both. Applying the raw list-fold operation in the two possible orders can still produce normalized kernels, and those kernels differ. Normalization therefore does not establish compatibility, simultaneous interpretability or certified-menu admission.

The compatibility construction uses the `RowPatch` interface. It does not silently replace the separate disjointness requirement of an `AtomicBank`; those types encode different assembly contracts.

Admission and effect are also independent questions. A restricted grammar may admit an action-only block and an update-only block while excluding their union. Separately, the original Boolean OR property has singleton margins $0$ and joint margin $1$. That joint-only **effect** is not a theorem that the frozen grammar admits the joint block, and joint-only **admission** would not itself prove a positive effect.

**Source trail.** [D-08 actual-menu addendum](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/tranche9_d08_scope_receipt_addendum.lean). The case packet covers 30 named declarations, including 14 new proved facts, and three semantic compiler controls: the conflicting pair cannot be compatible, the forbidden union cannot be admitted, and the zero OR singleton margin cannot be one.

## C08.2. Minimal does not mean unique, monotone or globally order-equivalent: B-02

The original Boolean atom bank and its actual one-step path-law properties already provide exact original constitutive margins. For the AND property, the action singleton and update singleton each have margin $1$ and are inclusion-minimal positive blocks. They are incomparable under inclusion. The joint block is positive but has a positive proper subblock, so it is not minimal. Consequently there is no unique minimal positive block in this example.

For the XOR property, the action singleton has margin $1$ while its admitted joint superset has margin $0$. Both the positivity predicate and the actual real-valued original margin fail upward monotonicity. These are claims about `blockMargin` on the original model, property and comparison set, rather than an unrelated hand-written Boolean predicate.

The new local-transport fixture fixes the physical partition and component map and changes only the second grammar's admission predicate:

| Grammar | Admitted blocks | Order structure |
|:--|:--|:--|
| Original fine grammar | $\varnothing,\{0\},\{1\},\{0,1\}$ | Four-element inclusion order with incomparable singletons |
| Restricted grammar | $\varnothing,\{0\}$ | Two-element chain |

The component map is the identity, and its lift is the identity on component subsets. At the selected action singleton $\{0\}$, every admitted strict lower fine block has a restricted preimage: its only strict lower subset is $\varnothing$. This is precisely the **local lower-coverage** hypothesis needed by `original_margin_minimal_iff_of_lower_coverage`. The original AND margin of the selected block is $1$, the empty block is not positive, and original-margin minimality transports at the selected block.

Global admitted-order equivalence still fails. The fine update singleton $\{1\}$ is admitted but has no restricted admitted preimage. More strongly, the source proves that no order isomorphism exists between the two admitted-block carriers: the restricted carrier is a chain, whereas the fine carrier contains incomparable elements. This is a genuine order-nonisomorphism result; it does not rely merely on a chosen component map being noninjective.

The conclusion is local and positive: the specified selected block's original margin and minimality transport under the exact lower-coverage hypothesis, despite the globally different admitted orders. It does not assert transport of every fine block, arbitrary coarsenings or an unrestricted notion of “the same intervention grammar.”

**Source trail.** [tranche10_b02_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_b02_scope_receipt_addendum.lean). In namespace `PermanssonResearch.Certification.Tranche10B02`, the central declarations are `two_incomparable_original_minima`, `no_unique_original_minimal_block`, `xor_original_margin_not_monotone`, `restricted_original_margin_eq`, `restricted_original_minimality_transport`, `admitted_orders_not_isomorphic` and `positive_local_transport_without_admitted_order_isomorphism`.

**Edition evidence.** `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 65 named declarations with allowed-axiom output and 5 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_B-02_Receipt.json` (SHA-256 prefix `5b1dd829d437`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`). 

**Exercise.** Why can local minimality transport while the full admitted orders are nonisomorphic? **Answer:** minimality of the chosen block only inspects its admitted proper subblocks. Those lower blocks are covered; unrelated admitted fine blocks outside the chosen lower set need not have preimages.

# C09. Quotients, abstract states, nonlinear properties and scope-specific witnesses

A representation may reduce a large state system to a smaller labeled model, but fewer states do not automatically mean equivalent behavior. A map $q:Y\to Q$ can collapse several source states into one abstract state. For an **exactly lumpable** Markov process, the projected next-state probability depends only on the image $q(y)$, not on which source state $y$ was used. Without such a condition, the projected process need not have an autonomous transition kernel on $Q$.

The `PermanssonResearch/Quotient/` family distinguishes exact and approximate transport, discounted path-law margins, geometric prefix error and adversarial counterexamples. Its Lean modules include `GeometricQuotient.lean`, `ApproxPrefix.lean`, `DiscountedCanonicalBridge.lean`, `Q01NonLumpableProjectionCountermodel.lean` and `Q05ActualOriginalMarginAdapter.lean`. Their hypotheses matter: a small one-step projected discrepancy under a declared coupling does not establish exact invariance or a common all-horizon law.

The successor application's `finite-quotient` and `finite-metric` profiles perform bounded operations with defined certificate semantics. They should be taught as **specialized numeric profiles**, not as an unqualified instruction to compress all unobserved institutional or strategic states into a single “pressure” variable.

A separate challenge is **nonlinear occupation**. Suppose a property depends nonlinearly on the stationary mass of a Boolean descriptor. Taking a weighted average of classwise descriptor probabilities and applying a nonlinear function may produce a different result from applying the function separately in each recurrent class and averaging afterward. For a function $f$, the two objects are

$$f\!\left(\sum_iw_ip_i\right)\quad\text{and}\quad\sum_iw_if(p_i),$$

which are not generally equal. The source's nonlinear Boolean and period-three constructions attack exactly these interpretation boundaries. `NonlinearPolicyClassComparison.lean` demonstrates a constructed distinction between phase-aware and phase-blind deterministic policy classes; it also contains the explicit theorem `no_universal_strict_score_gap`, preventing a single example from being promoted into universal strict superiority.

**Neutral arithmetic.** Let two equally weighted recurrent classes have descriptor shares $p_1=0$ and $p_2=1$, and $f(p)=p(1-p)$. Then $f((p_1+p_2)/2)=1/4$ whereas $(f(p_1)+f(p_2))/2=0$. Those are different properties, not competing estimates of one number.

**Proof trail.** `PermanssonResearch/Quotient/`, `PermanssonResearch/ReverseSolver/` (modules: `NonlinearBooleanClassFunctional.lean`, `NonlinearMultichainAggregationFixture.lean`, `NonlinearPolicyClassComparison.lean`); [`docs/LANE_E1_APPROX_QUOTIENT.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/LANE_E1_APPROX_QUOTIENT.md); [`NUMERIC_GRAMMAR_QUOTIENT.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_GRAMMAR_QUOTIENT.md); [`NUMERIC_RESIDENCE_NONLINEAR.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_RESIDENCE_NONLINEAR.md).

**Boundary.** A quotient can preserve one property and destroy another. A classwise nonlinear functional cannot be silently replaced by a function of the unconditional mean.

## C09.1. The original law, its descriptor and its nonlinear score: D-09

The original two-absorbing witness has two distinct physical recurrent classes. A constant descriptor can assign both classes the same descriptor target, but does not make the physical classes identical. The nonlinear-score calculation uses a separate observable, `observedPhysicalBool`, which distinguishes those physical states. The constant descriptor itself is not the source of the differing Boolean occupation scores.

For a Boolean occupation law with true-state mass $p$, the source uses

$$f(p)=1-\left|p-\frac23\right|.$$

The two absorbing paths have masses $p=0$ and $p=1$ and hence scores $f(0)=1/3$ and $f(1)=2/3$. Under the original equal-weight initial law, exactly one absorbing path is realized. The expected pathwise nonlinear score is

$$\frac12f(0)+\frac12f(1)=\frac12.$$

The stationary barycenter instead has true mass $1/2$, giving $f(1/2)=5/6$. Both arithmetic calculations are valid, but only $1/2$ is the declared original expected pathwise score. Replacing it by $5/6$ changes the property. The canonical full-path mixture identity and expected-score formula hold for every initial probability law in this two-state model; the equal mixture is a distinguishing instance.

A separate native policy comparison uses joint state $\mathrm{Fin}\,3\times\mathrm{Bool}$ and the original point start $(0,\mathrm{false})$. Its comparator class is all deterministic stationary physical-only policies $\mathrm{Bool}\to\mathrm{Bool}$. Their scores are at most $5/6$, and the specified alternating physical-feedback policy attains $5/6$. The specified phase-aware policy has score $1$.

| Witness | Initial-law and policy scope | Exact result |
|:--|:--|:--|
| Two absorbing physical classes | Every initial probability law; equal mixture is the diagnostic instance | Equal-mixture expected pathwise score $1/2$ differs from barycenter score $5/6$ |
| Native phase comparison | Original point start; deterministic stationary physical-only comparator policies | Comparator maximum $5/6$, attained; specified phase-aware score $1$ |

The phase-aware policy is stationary on the augmented state that includes phase. The second result does not quantify over arbitrary randomized or history-dependent policies, nor over every initial law. Its occurrence of $5/6$ is a different mathematical fact from the barycenter calculation.

**Source trail.** [D-09 complete named source probe](https://github.com/HMarcusWH/PermanssonLean/blob/4655c60b59716385fd1c87772b87912a3550840c/verification/research/tranche8_d09_scope_receipt_addendum.lean). Its 19 named declarations comprise 18 theorems and `booleanClassFunctional`. The controls reject collapsing the physical classes, substituting the barycenter score for the actual mixed-law score and inflating the phase-blind attainer to $1$.

## C09.2. Approximate compression and exact original margins

B06.1 supplies the complementary Q-05 example: the original canonical discounted whole-path margins are $19/90$ and $1/5$, with exact difference $1/90$. Its proof uses the full original comparison sets and the actual observed world coordinate after compression. This is a separate approximation/transport statement; neither the two-absorbing nonlinear calculation nor a finite set of numeric horizons can replace that source-law identification.

# C10. Exact rational evaluation and proof-carrying receipts

Most numerical input failures arise **before** optimization: negative matrix entries, non-unit row sums, implicit floating-point rounding, invalid indices, or unannounced conversions between strategic-model and rational-matrix semantics. The source therefore keeps strict rational input and mathematical correspondence as separate layers.

`RationalKernel.lean` defines `RationalMarkovMatrix n` with entries in $\mathbb Q$, nonnegativity for every entry and row-sum exactly one. `RationalHittingTarget n` contains goal and forbidden finite sets with a disjointness witness. The recursive first-hit value starts at the actual initial state at time zero:

$$H_0(y)=\mathbf1_G(y),\qquad
H_{t+1}(y)=\begin{cases}
1&y\in G,\\0&y\in D,\\\sum_z K(y,z)H_t(z)&\text{otherwise.}
\end{cases}$$

`FiniteEvaluation.lean` separately computes the sum of successful chronological word weights. Its equality theorem is a finite algebraic statement. `FinitePrefixBridge.lean` adds the distinct canonical measure correspondence for the constructed kernel. The difference between these stages is structural: a successful rational sum need not by itself prove correspondence with a general typed strategic-world process.

**Exact reproducibility requirement.** Represent one-half as a rational pair or an input-accepted exact rational serialization, not as an unrecorded IEEE floating-point approximation. For the one-state transition row $K=[1]$, exact row-sum checking should return $1$, not $0.9999999999999999$. For the earlier $s,g,d$ example, the exact two-step fixed-A value is $7/16$, the fixed-B value is $1/2$, and the adaptive D1 value is $5/8$; an independent enumerator should reproduce these fractions rather than a rounded decimal string.

`CheckedRationalInput.lean` and `C10ReceiptSemantics.lean` introduce checked finite inputs and exact certificate semantics for more specialized C10 constructs. `EndToEndCertificate.lean` includes a typed-world bridge in its **constructed research family**. The application successor provides source-bound Lean candidates for specific bounded profiles, a byte rechecker and separately executable Lean build commands. The ordinary numeric command **does not run Lean**. A receipt that passes numeric checking is therefore not entitled to report `kernel_checked_proof=PASS` without actual compiler evidence from the appropriate source-bound process.

For every submitted mathematical example, preserve a short artifact chain:

| Artifact | Required question |
|:--|:--|
| Source model | Does its $\alpha/P/U$ or rational matrix actually parse and satisfy the schema? |
| Numerical producer | What objective and finite scope were evaluated? |
| Independent receipt | Were the original input and claimed certificate recomputed independently? |
| Lean source candidate | Which precise theorem statement or reflection family was emitted? |
| Compiler record | Is there genuine execution evidence for **those exact bytes**? |
| Scientific report | Which dimensions remain not assessed or not identified? |

**Proof trail.** `PermanssonResearch/ReverseSolver/` (modules: `RationalKernel.lean`, `FiniteEvaluation.lean`, `FinitePrefixBridge.lean`, `CheckedRationalInput.lean`, `C10ReceiptSemantics.lean`, `EndToEndCertificate.lean`); [`docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/LANE_C10_EXACT_CONSTITUTIVE_EXECUTION.md); `apps/permansson/application-successor/src/permansson_app/` (modules: `engines/`, `receipts/`, `proof/`).

**Boundary.** Computable exact fractions and a Lean-checked abstract theorem are complementary evidence. Neither alone identifies a real-world probability law, and an emitted proof file is not a compiled proof.

## C10.1. What the new case packets bind

The later case packets use exact named source declarations, transitive-axiom output and targeted semantic compiler controls. E02.6 identifies their actual receipt status and Appendix J maps every original and later case to its source route. B07.1 illustrates the distinction between normalized finite atom arithmetic and the additional actual measure/event-TV bridge.

# C11. Exact graph reachability, recurrent classes and absorption

A transition matrix contains both **numbers** and a directed support graph. The graph has an edge $y\to z$ precisely when $K(y,z)>0$. Since the C10 support representation uses rational arithmetic, its edge test is exact rather than based on an adjustable floating threshold. `RationalSupportGraph.lean` builds the strict-positive relation and its finite transitive closure; the reflexive seed includes a path of length zero. Communicating classes arise from mutual reachability. A bottom strongly connected component (BSCC) has no positive-probability edge leaving it.

These constructions make it possible to distinguish three different long-run questions:

1. Which bottom recurrent classes exist in the finite graph?
2. With what probability is each class eventually reached, given an initial law?
3. What is the stationary distribution **inside** each selected class?

An absorption probability is not a stationary distribution. A class can receive one-half of the eventual selection probability while having an internal stationary distribution concentrated nonuniformly on its own members. In a multichain system, the unconditional limiting occupation law can depend on initial-state class-selection weights; it need not be identical for all admissible initial laws.

For class-absorption calculations, collapse each bottom recurrent class to a single absorbing label and retain the transient states. Let $Q$ be the transient-to-transient block and $R$ the transient-to-class block. The resulting reduced kernel has the form

$$K_{\mathrm{class}}=\begin{pmatrix}Q&R\\0&I\end{pmatrix}.$$

The vector of probabilities of absorption into a selected class satisfies the Dirichlet system

$$(I-Q)h=r,$$

where $r$ is that class's one-step transition-probability column. This reduction is used only for class-selection probabilities; stationary dynamics inside a selected class are computed from the original kernel. The C10 research source proves uniqueness under its graph/transience hypotheses and constructs exact rational candidate solutions using determinant, adjugate and Cramer's rule. A nonzero determinant and the correct boundary conditions are part of the certificate, not assumptions to be guessed from a numerical answer.

**Worked neutral example.** Let $t$ mean a temporarily interrupted information service and $a,b$ two distinct fully functioning service configurations. From $t$, the next step is $t$ with probability $1/2$, $a$ with probability $1/4$, and $b$ with probability $1/4$. Both $a$ and $b$ are absorbing. The probability of eventually reaching $a$ from $t$ is

$$h_a(t)=\frac14+\frac12h_a(t),\qquad h_a(t)=\frac12.$$

Similarly $h_b(t)=1/2$. The event “ever enter $a$ before $b$” and the event “eventually select class $a$” coincide for this explicitly absorbing construction. But merely knowing that the support graph has two BSCCs does not determine these weights. The rational transition entries matter.

`RationalBSCCPartition.lean`, `RationalAbsorptionSolve.lean`, `RationalCramerCertification.lean`, and `TypedStoppedClassSelection.lean` separate computed support classes, candidate solutions, verification, and canonical path-law transport. `C11StationaryFamily.lean` and the native C11 provider supply additional bounded stationary-family certificates. The fixed C10 six-state example and the separate C11 1–6-state family must not be treated as the same application profile.

**Proof trail.** `PermanssonResearch/ReverseSolver/` (modules: `RationalSupportGraph.lean`, `RationalBSCCPartition.lean`, `RationalDirichletUniqueness.lean`, `RationalAbsorptionSolve.lean`, `RationalCramerCertification.lean`, `TypedStoppedClassSelection.lean`, `C11StationaryFamily.lean`); [`docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/LANE_C11_CLASS_STATIONARY_CERTIFICATION.md); `apps/permansson/closure-successor/` and `closure-successor-c11/`.

**Boundary.** A rational BSCC partition is a mathematical description of a declared finite kernel. It does not establish empirical recurrence or a regime property in a different or changing model.

# C12. Infinite-horizon safety and controlled invariant cores

Finite-horizon survival is not the same as infinite-horizon safety. An operation can be very unlikely to fail over a short interval yet eventually fail with probability one under repeated independent exposure. The research library formalizes the distinction using true infinite-path events and their finite-horizon approximations.

Let $G$ be the declared safe region, and let $\sigma$ denote an admissible behavioral controller for the constructed finite rational model. The infinite event is

$$\mathrm{SafeForever}(G)=\bigcap_{t\ge0}\{Y_t\in G\}.$$

Finite-horizon safety values form a nonincreasing sequence, since satisfying an additional safety observation cannot create a new safe path. `InfiniteSafetyBellman.lean` defines finite-horizon recursion and its limit. `InfiniteSafetyPathSemantics.lean` connects actual path-law events to the recursion. `InfiniteSafetyOptimality.lean` proves, in its stated finite control setting, an upper bound over full-history real behavioral policies and attainment by a deterministic stationary selector. This is a stronger and differently quantified theorem than the ordinary bounded application `finite-safety` command.

A **controlled invariant** subset is one in which each state admits some control whose transition support remains entirely inside the subset. `GreatestControlledInvariant.lean` constructs a descending sequence by pruning states that cannot meet this support condition. In finite state space, the iteration stabilizes. The `invariantCore` corresponds, under the stated model hypotheses, to states permitting almost-sure safety forever. This is fundamentally a support-one statement; a tiny positive leakage probability is not “close enough” for an almost-sure invariant claim.

**Leakage counterexample.** A fictional redundant service stays online each period independently with probability $99/100$ and otherwise permanently fails. Starting online, the probability of remaining online for $T$ transitions is

$$\Pr(\mathrm{safe\ through\ }T)=\left(\frac{99}{100}\right)^T.$$

This can remain high at a small finite deadline, but

$$\lim_{T\to\infty}\left(\frac{99}{100}\right)^T=0.$$

Consequently this constructed model has zero probability of operating **forever** even though short-horizon safety is high. `InfiniteSafetyLeakage.lean` provides source-backed theorems expressing this distinction. A finite sample of no failures cannot refute the model's positive long-run leakage.

**Verification exercise.** Compare three properties for a proposed service state: (i) being safe at a specified terminal time, (ii) never leaving safe over the first $T$ transitions, (iii) never leaving safe over infinitely many transitions. They are not interchangeable. Ask whether any input row assigns even a tiny positive mass to a state outside the proposed invariant core.

**Proof trail.** `PermanssonResearch/ReverseSolver/` (modules: `InfiniteSafetyBellman.lean`, `InfiniteSafetyFiniteEvaluation.lean`, `InfiniteSafetyPathSemantics.lean`, `InfiniteSafetyOptimality.lean`, `GreatestControlledInvariant.lean`, `InfiniteSafetyLeakage.lean`) and the released `finite-safety` profile documentation.

**Boundary.** The existence of an infinite-horizon theorem in Research Lean does not mean that the released bounded CLI computes general infinite-horizon policies or that high finite safety certifies almost-sure invariance.

# C13. Occupancy polytopes, rational extreme points and certificates

Occupancy converts a finite controlled path problem into a set of mass-balance equations. It makes the quantitative object inspectable independently of the policy syntax. In a finite time-indexed model, let $q_t(y,c)$ denote the probability mass of being in state $y$ at time $t$ and selecting control $c$. For each feasible pair, $q_t(y,c)\ge0$. These variables define state masses and transitions by

$$x_t(y)=\sum_{c\in C_t(y)}q_t(y,c),\qquad
x_{t+1}(z)=\sum_{y,c}q_t(y,c)K_{t,c}(y,z).$$

The initial state law $\mu$ fixes $x_0$. Further linear objective or risk constraints yield a finite polytope. A feasible point and a globally optimal point are different claims. A candidate point must satisfy **all** mass equations and inequality constraints, and an optimality proof must compare against the declared entire feasible class.

`FiniteOccupancyModel.lean` defines `TimeSystem`, `BehavioralPolicy` and `Flow`. The paired history and marginal modules use the genuine controlled chronology, not an unattached algebraic vector. `FiniteOccupancyReconstruction.lean` proves that a feasible flow is realized by a legal controller and that the reconstruction preserves state/action marginals. Importantly, a zero-mass history still receives an admissible policy choice. The existence of the choice does not mean that an impossible history receives nonzero probability.

For the exact-polytope branch, a rational program can be written as $Aq\le b$, with a rational objective $c\cdot q$. Under the source's assumptions, the vertex-enumeration procedure considers rational candidate points obtained from active constraints. `PolytopeCompleteness.lean` establishes that its candidate construction covers the relevant vertices; `PolytopeOptimizer.lean` proves feasibility and global dominance for the returned rational optimum, or a precise none/infeasibility relation under the encoded polytope contract. This is not an efficiency guarantee for huge linear programs: exhaustive active-set enumeration has combinatorial cost.

**Elementary flow audit.** Let an initial service state have mass $1$ and two options $c_1,c_2$ with occupancy weights $q_0(s,c_1)=1/3$ and $q_0(s,c_2)=2/3$. The state mass equation is $1/3+2/3=1$. If one option moves to restored with probability $1$ and the other to restored with probability $1/2$, then the next restored-state mass is

$$x_1(g)=\frac13\cdot1+\frac23\cdot\frac12=\frac23.$$

A checker should calculate this from the **original transition rows and candidate occupancy**, not trust an asserted result field. The same flow variables can be used to test a separately declared risk event, but the flow must not be reused across a changed state partition without a valid transport theorem.

The released `lp-propose` and `lp-check` form a producer/consumer certificate chain. The application has additional one-step risk and risk-infeasibility profiles. Their bounds, inputs and receipt types differ from the research theorem over finite multistage flows. Volume D provides the per-command schema and example reference; Volume C explains the shared mathematical structure.

**Proof trail.** `PermanssonResearch/ReverseSolver/` (modules: `FiniteOccupancyModel.lean`, `FiniteOccupancyHistory.lean`, `FiniteOccupancyMarginals.lean`, `FiniteOccupancyReconstruction.lean`, `FlowPolytope.lean`, `FlowPolicyOptimality.lean`, `PolytopeCompleteness.lean`, `PolytopeOptimizer.lean`); [`NUMERIC_RISK_OCCUPANCY.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_RISK_OCCUPANCY.md); [`LP_CERTIFICATE_LEAN_BRIDGE.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/LP_CERTIFICATE_LEAN_BRIDGE.md).

**Boundary.** Rationality and global linear optimum are conditional on the precise finite polytope. A certificate is not a proof about unspecified constraints, omitted actions, or a different observation structure.

# C14. Multiagent protocols, autonomy and observation boundaries

Multiple agents require more than one action label. They may observe different state coordinates, react through different channels, and share a common world or common state whose evolution creates indirect dependence. A mathematical “open loop” comparison is meaningful only after specifying what information each participant is allowed to use and exactly which strategic-generator component changes.

The `PermanssonResearch/MultiAgent/` source begins with typed two-player generator assembly (`ProductGame.lean`) and defines protocol constructors (`Protocols.lean`). Its closed-loop protocol replaces the designated participant while allowing the other to use the original reactive rule. The open-loop constructor installs an allowed anchor for the other participant. **Both retain the same frozen world primitive $P$** and are not licenses to modify the physical state transition for convenience.

The source distinguishes a merely local, strictly nonreactive anchor from an **autonomous locked sub-menu**. A strictly nonreactive anchor can still respond indirectly through a common state $S_0$ that itself depends on another participant. The stronger autonomous sub-menu adds common-state exogeneity and excludes that channel. That distinction is a formal information boundary, not an editorial synonym. Typed feasibility for these anchors has additional declared constraints; it is not automatically embedded into every Lean protocol definition.

The research has explicit inequalities relating closed-loop and open-loop effect differences to an adaptation or protocol gap. Those are **bounds**, not general proof that a second participant always reinforces, opposes or stabilizes the first. The Boolean witness constructions show which interpretation is supported in a concrete typed model and where a strict MA2-type assertion remains unavailable or obstructed. `StrictMA2Obstruction.lean` supplies support-sensitive path-law arguments; it does not turn an observed pair of actions into causal mediation in the real world.

**Neutral organizational thought experiment.** Two municipal services share a public status dashboard and independently manage their staffing. Service B may be prohibited from reading A's private operational state while still responding to a public budget balance influenced by A. Calling B “nonreactive” without specifying whether the common budget state is endogenous could change the model class. The formal distinction is whether the anchor reads or can be affected by that channel, not whether the modeler subjectively considers B independent.

The released `finite-multiagent` profile is a specific bounded numerical protocol comparison. A successful receipt does not establish arbitrary multiagent equilibrium, full legal feasibility, all-initial constitution, or opponent behavioral identification. Different protocols and initial laws need separate input proofs and report fields.

**Proof trail.** [`docs/LANE_F1_MULTIAGENT_PROTOCOLS.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/LANE_F1_MULTIAGENT_PROTOCOLS.md); `PermanssonResearch/MultiAgent/` (modules: `ProductGame.lean`, `Protocols.lean`, `AdaptationBound.lean`, `StrictMA2Obstruction.lean`, `AutonomousMarginalLaw.lean`, `PrivateClock.lean`, `NatPrivateClock.lean`, `FiniteProductProtocols.lean`); [`NUMERIC_MULTIAGENT.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NUMERIC_MULTIAGENT.md).

**Boundary.** A multiagent result must say who observes what, when, and what primitive changes. “The other player reacts” is not a formally sufficient model specification.

## C14.1. Player renaming acts on every mechanism input: F-01

For asymmetric multiagent models, renaming the players changes the positions of the coordinates read by action selection, private updates, common updates and the physical kernel. The actual player-swap constructors exchange the private-update rows and pull back their full inputs through the swap. Common updates and physical rows also receive the correctly reindexed input. No physical symmetry premise is needed for this coordinate change.

A protocol intervention and a coordinate change have distinct meanings. The protocol intervention retains its declared physical primitive $P$. The coordinate change reindexes the arguments of $P$ along with the rest of the representation. Leaving these inputs in their old order generally produces a different process.

The original asymmetric common/world fixture uses Unit private states, so it cannot expose a nontrivial private-output distinction. The additive Boolean-private witness addresses that precise limitation. One private update reads the first action and the other reads the second. The rows differ at $(\mathrm{false},\mathrm{true})$ and vary between $(\mathrm{false},\mathrm{false})$ and $(\mathrm{true},\mathrm{true})$. At the tested live input, the correctly reindexed new first private update gives true-event mass $0$; omitting the input swap would give $1$. These updates depend on actions; dependence on previous private-state values is not asserted.

The F-01 receipt distinguishes five source scopes:

| Source group | Result and retained boundary |
|:--|:--|
| Original asymmetric common/world fixture | Concrete Boolean/Unit rows and canonical transport from point and non-Dirac starts |
| Private/common/physical row pullbacks | Generic constructor identities plus the nonconstant Boolean-private example |
| General finite player-swap transport | Kernel/path-law correspondence for every initial probability law under the stated type and measurability premises |
| Indexed examples and binary reduction | Actual Fin3 protocol/physical rows; a separate Fin2 indexed-to-binary transport theorem |
| Matched measurable protocols | Both treated players, fixed physical primitive and original-margin transport in the conditional-product Fin2 mechanism class |

Arbitrary initial probability laws can contain initial-coordinate correlations. That quantifier does not remove the conditional-product restriction on the protocol mechanisms. Conversely, conditional-product mechanisms do not require every initial distribution to be a product law. In the actual Fin3 example, the closed-loop action vector gives the physical true-event probability $0$ and the open-loop vector gives $1$; this is not a theorem reducing every three-player system to two players.

**Source trail.** [F-01 mechanism and scope addendum](https://github.com/HMarcusWH/PermanssonLean/blob/4655c60b59716385fd1c87772b87912a3550840c/verification/research/tranche8_f01_scope_receipt_addendum.lean). Its 37 named declarations include ten new proved facts. Three semantic controls reject omitted common/physical reindexing, omitted private reindexing and substitution of the open-loop value for the original Fin3 closed-loop value. “F-01” here is a certification case identifier, not the historical casebook chapter F01.

## C14.2. Equal unmarked marginals can conceal different marks: M-02

The actual-history fixture evaluates the original `oneStepHistoryKernel.map opponentMark`. It proves that two declared mechanisms have the same fair unmarked next-key law while a marked diagonal event has probabilities $1$ and $0$. The mark retains the relevant action/state correlation that the unmarked marginal discards. Equal unmarked state distributions therefore do not establish equality of marked histories or equality of mechanisms.

There are two separate source constructions. `M02ActualMarkedHistoryFixture` compares **two separately strictly nonreactive anchors** with different private update mechanisms. Its key declarations are `strictAnchor_isStrict`, `markedLaw_actual_source_atom`, `actual_unmarked_next_key_laws_equal`, `actual_marked_diagonal_separation` and `update_mechanisms_differ`. That fixture does not exhibit one fixed reactive opponent while holding all mechanisms common.

`MarkedStrategicPathCountermodel` supplies the separate reactive witness. Its opponent update reads the other player's current action, so it can give different updates at the same permitted anchor-update key. The source explicitly proves failure of `IsStrictlyNonReactive`. It must not be counted as an example satisfying the strict autonomy premise.

The strict no-separation result requires its actual autonomy hypotheses: an exogenous common update (`IsExogenousCommon`), strict nonreactivity of both anchors, and baseline-supported agreement for **both** action and update mechanisms for each anchor. Dropping update agreement while retaining only equal unmarked laws changes the theorem's premises.

**Source trail.** [M02ActualMarkedHistoryFixture.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/PermanssonResearch/MultiAgent/M02ActualMarkedHistoryFixture.lean), [MarkedStrategicPathCountermodel.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/PermanssonResearch/MultiAgent/MarkedStrategicPathCountermodel.lean), [AutonomousMarkedKernel.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/PermanssonResearch/MultiAgent/AutonomousMarkedKernel.lean) and [AutonomousSupportClosure.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/PermanssonResearch/MultiAgent/AutonomousSupportClosure.lean). This edition's M-02 receipt status is `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 29 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_M-02_Receipt.json` (SHA-256 prefix `ca5969c76844`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`). The two witnesses jointly clarify the original scope; they are not spliced into a stronger single-model theorem that neither source states.

**Exercise.** If both unmarked marginals are fair, why can the marked diagonal probabilities differ? **Answer:** the same two marginal distributions can be coupled differently. A mark can observe the correlation between action and next key even when either unmarked next-key marginal alone is unchanged.

# C15. Economic examples, X1 and specialized theorem scopes

The repository contains mathematical developments that are neither part of the original frozen core nor direct general-purpose successor application profiles. Their presence matters to the guide because otherwise a reader may assume that all proved results share the same numerical interface, the same state ontology, or the same class of initial laws.

`PermanssonResearch/EconomicWitness/` defines a **constructed economic strategic-world witness**, its exact-regime properties, full-strategy traces, and constitutive comparisons. For example, `ExactRegime.lean` contains `original_exactGR` and `original_confirmatoryGR`; those are claims about the **explicitly defined model and specification**, not proof that a historical market has the same kernel. A paper-level economics analogy should therefore be labeled constructed, conditional or empirically evaluated as appropriate.

The `PermanssonResearch/X1/` family contains typed models, fixed parameter tables, exact transition-matrix calculations, occupation and intervention numerics, full-strategy certificates, and margins. The existence of modules such as `InterventionNumerics.lean`, `FullStrategyCertificate.lean` and `ExactMargins.lean` does not entitle the guide to say that an X1 calculation is available as one of the 26 released successor CLI profiles. X1 is a distinct research scope with its own hypotheses and proof chain.

Other specialized families—`MultipleLimit`, `Perturbation`, `Quotient`, `GrammarRobust`, `ConstitutiveQuasi` and purpose-built counterexample fixtures—should be referenced at the point they qualify or challenge a broader statement. A counterexample is a positive research result: it may prove that a desired generalization **cannot** hold, rather than reporting unfinished work.

**Three-level reading exercise.** Compare these statements:

1. “The Lean source proves that the explicitly constructed economic witness satisfies an Exact GR predicate.” This is a precise, source-testable model theorem.
2. “The research numerics evaluate a specified X1 model with rational parameters.” This is a finite mathematical calculation under an X1 model definition.
3. “An observed economy or conflict therefore occupies that exact regime.” This is a separate empirical conclusion requiring evidence not supplied by the first two claims.

Statements 1 and 2 can be true while statement 3 is unsupported. The guide should not erase that distinction, nor make empirical identification a prerequisite for studying the valid conditional mathematics.

**Proof trail.** `PermanssonResearch/` (modules: `EconomicWitness/`, `X1/`, `MultipleLimit/`, `Perturbation/`, `Quotient/`); `paper/supporting/specialized_theory/`; [`docs/V020_IMPLEMENTATION_INDEX.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/V020_IMPLEMENTATION_INDEX.md); [`docs/FORMALIZATION_MAP.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/FORMALIZATION_MAP.md).

**Boundary.** A theorem with specialized parameters and an explicit constructed witness is not a universal theorem about every admissible game. The strongest accurate claim is the one the Lean declaration actually proves.

# Exercises, independent arithmetic and interpretation keys

The exercises use fictional service systems. Their goal is to verify mathematical literacy and explicit scope, not to recommend intervention in a real conflict. A runnable exact-Fraction answer-check script accompanies this volume.

## Exercise C-A. Fixed-menu and feedback control classes

For the three-state $(s,g,d)$ example in C01–C02, calculate (i) the best fixed alternative among A and B at horizon two, and (ii) the best state- and remaining-horizon-dependent schedule. State whether the second result contradicts the D0 optimum.

**Answer.** Fixed A gives $7/16$, fixed B gives $1/2$, so D0 selects B with $1/2$. D1 can choose A with two transitions remaining, then B if it returns to $s$, obtaining $5/8$. There is no contradiction: the policy classes are different.

## Exercise C-B. Residence versus first entry

Classify `off,on,off,on,on` for target `on`, entry deadline $T=3$, residence $m=1$. Distinguish the retryable entry-by event from first-ever-entry residence.

**Answer.** The retryable event succeeds at entry $e=3$ using observations three and four. The first-ever-entry-only interpretation fails because the first visit at observation one does not last through observation two. This answer assumes the finite observation word is indexed from zero.

## Exercise C-C. Risk-constrained mixture

Two hypothetical service modes have scores $4/5$ and $9/10$, and risks $0$ and $1/10$. Calculate the maximal expected score under risk cap $1/20$.

**Answer.** Mix the riskier mode with $p\le1/2$; the optimal mixture is $p=1/2$, giving score $17/20$ and risk $1/20$. The unconstrained best score $9/10$ violates the cap.

## Exercise C-D. Bayes and impossible observations

With equal healthy/damaged prior probability and green likelihoods $3/4$ and $1/4$, compute the posterior chance of healthy after green. Explain what to do when an observation has probability zero.

**Answer.** The posterior is $3/4$. A zero-probability signal has no conditional posterior under ordinary division; a sound implementation records it as unreachable rather than assigning a fabricated distribution.

## Exercise C-E. Initial classes and absorption

A transient service state has transition probabilities $1/2$ to itself, $1/4$ to stable configuration A, and $1/4$ to stable configuration B. Find both eventual absorption probabilities.

**Answer.** Each is $1/2$. The bottom-class partition alone does not identify those weights; the transition matrix does.

## Exercise C-F. Why finite survival cannot certify invariance

A service survives each transition with probability $99/100$ and fails irreversibly otherwise. Calculate two-step survival and the probability of survival forever.

**Answer.** Two-step survival is $9801/10000$. Infinite survival is zero. A numerical finite-horizon survival near one is not an exact invariant-core certificate.

## Exercise C-G. Interpret a certificate label

An output passes exact numerical receipt verification and contains an emitted Lean candidate file; `lean_status` remains `NOT_EXECUTED`. May the report say that Lean independently compiled the numerical instance?

**Answer.** No. A source-bound, byte-rechecked candidate is not a compiler run. Actual compilation and separate evidence authentication must be recorded for the exact bytes in scope.

# Guide source crosswalk and version discipline

The following source families and reference documents are the authority for chapter verification. Source paths are interpreted against their explicitly identified source layer: original v1.0 references retain the frozen baseline, while v1.1 additions use their stated later commit pins. A Markdown hyperlink is a convenience, not proof of semantic correspondence.

| Chapter | Core mathematical source | Associated application or evidence |
|:--|:--|:--|
| C01 | `ReverseSolver/FrozenMenu.lean`, `RationalKernel.lean`, `FinitePrefixBridge.lean` | D0 research specification; frozen-menu numeric |
| C02 | `ReverseSolver/ControlledKernel.lean`, `BellmanOptimality.lean` | D1 Bellman specification; finite-bellman |
| C03 | `ReverseSolver/HistoryForwardMeasure.lean`, `HistoryTypedTransport.lean` | D1 history and typed-history documentation |
| C04 | `ReverseSolver/ResidenceEvent.lean`, `ResidenceValue.lean` | D2 residence specification; finite-residence |
| C05 | `ReverseSolver/FlowPolicyOptimality.lean`, `PolytopeOptimizer.lean` | one-step-risk, risk-infeasibility, LP checks |
| C06 | `ReverseSolver/BeliefChronology.lean`, `PrivateControlStageModel.lean` | belief and private-stage profiles |
| C07 | `ReverseSolver/RectangularFiniteGame.lean`, `RectangularGameLaw.lean` | robust-nature and metric profiles |
| C08 | `GrammarRobust/`, `ConstitutiveQuasi/` | grammar, adaptive grammar, CQ-1 profiles |
| C09 | `Quotient/`, `NonlinearPolicyClassComparison.lean` | quotient, metric and nonlinear profiles |
| C10 | `ReverseSolver/RationalKernel.lean`, `EndToEndCertificate.lean` | numeric receipts and Lean candidates |
| C11 | `ReverseSolver/RationalBSCCPartition.lean`, `TypedStoppedClassSelection.lean` | C10/C11 separate providers |
| C12 | `ReverseSolver/InfiniteSafetyOptimality.lean`, `GreatestControlledInvariant.lean` | finite-safety scope distinction |
| C13 | `ReverseSolver/FiniteOccupancyModel.lean`, `PolytopeCompleteness.lean` | risk and LP certificates |
| C14 | `MultiAgent/Protocols.lean`, `StrictMA2Obstruction.lean` | finite-multiagent |
| C15 | `EconomicWitness/`, `X1/`, `MultipleLimit/` | research witnesses, not general numeric profiles |

Throughout this table, unprefixed `ReverseSolver/` refers to `PermanssonResearch/ReverseSolver/`; `GrammarRobust/`, `ConstitutiveQuasi/`, `Quotient/`, `MultiAgent/`, `X1/` and `EconomicWitness/` refer to subdirectories of `PermanssonResearch/`. The source manuscript and Research Lean CI remain separate from the published successor numeric wheel. Historical status paragraphs within individual documents are *version history*, not substitutes for checking the pinned source tree.

# Connections to Volumes D, E and F

This volume explains how to formulate and recognize the mathematical objects; it does not attempt to reproduce 26 command-line schemas in prose or invent a universal cross-profile API. **Volume D** documents all 26 numeric commands, schemas, C10/C11 usage and packaged examples; **Volume E** covers independent receipts, proof evidence, compiler replay, federation and release/CI identities; **Volume F** provides neutral exercises and archival source interpretation without elevating descriptive indices to identified transition laws.

**Reference-edition status.** C01–C15 retain their original source-scope technical explanations and add the explicitly identified v1.1 examples. The original v1.0 editorial review changed no source code or Lean proofs; the later source additions and their compiler evidence are recorded separately in A03.1 and E02.6. Internal source/editorial review does not constitute independent mathematical certification.


\newpage

# Volume D — Executable Exact Numerical Application

> **Executable reference scope.** This volume documents the implemented numeric application at the frozen source baseline, with reproducible **fictional/noncombat** examples. It does not identify real conflict dynamics, recommend operations or establish any empirical or scientific certification.
>
> **Source baseline:** [`HMarcusWH/PermanssonLean`](https://github.com/HMarcusWH/PermanssonLean/tree/89ac97cb8bcaad0c47c421209dd2e103db6d60ee) at commit `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`, Git tree `cf3d19b5eaa3756fe5c2e392367b9066330e1a4b`. Numeric application v0.2.0 is released from earlier commit `63a66c82a9ece4361f646ee13b6711192f831406`. A successful independent numeric receipt is not an authenticated instance Lean run.

# How to use Volume D

The preceding volumes established the formal objects and their proof boundaries. Volume D answers a different question: **what can a reader execute with the published application, what input must be supplied, and what independent evidence is returned?** The code here is an example of a mathematical instrument, not an instrument for identifying or selecting offensive military operations. Every exercise uses the repository's fictional finite models or neutral public-service analogies.

The source of truth for the software interface is the packaged application at `apps/permansson/application-successor/`, its [capability registry](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/src/permansson_app/data/capabilities.json), its CLI implementation `src/permansson_app/__main__.py`, and the [reviewer guide](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/REVIEWER_GUIDE.md). In particular, **26 exact numeric commands** and **two native C10/C11 providers** are not 28 interchangeable profile types. The two native providers run through the separate `run` route and a source-pin check; the remaining 26 are independently budgeted finite commands.

The standard chain is:

```text
Declared source model + scope-specific schema
       ↓ strict read, schema and semantic validation
Exact-rational numerical producer
       ↓ reported receipt
Independent source-separated checker
       ↓ status and certificate
Scientific report (all evidence gates kept separate)
       ↓ optional source-bound Lean candidate, byte recheck
       ↓ optional separate pinned Lean compile / axiom audit
Qualified interpretation of precisely the declared model
```

Do not skip a level. A passing checker is not a compiler record. A compiled Lean instance is not an identified external system. A theorem over a finite listed choice set does not assert anything about unlisted choices. See [`EVIDENCE_AND_RECEIPTS.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md).

# D01. Executing the released application and validating input

## D01.1. Reproducibility contract

Use the release's actual environment: Linux with CPython **3.12 or 3.13**, exact-rational JSON, a **new output directory**, and the profile-specific command. Version `0.2.0` was published November 1, 2026 from commit `63a66c82a9ece4361f646ee13b6711192f831406`; the later repository documentation-only checkpoint audited for this book is `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`. Do not substitute a moving `main` silently for a pinned release when comparing bytes.

A clean source-checkout route is:

```bash
python -m pip install './apps/permansson/application-successor[full-schema]'
permansson-app about
permansson-app capabilities
permansson-app resources --full --output /tmp/perma-d-resources
```

A published-wheel route begins by downloading the wheel, source distribution, `SHA256SUMS` and release manifest from the [v0.2.0 release](https://github.com/HMarcusWH/PermanssonLean/releases/tag/permansson-app-v0.2.0), verifying `sha256sum -c SHA256SUMS`, and installing the verified wheel. The release README records the exact wheel name, hash-locked dependency option and release boundary. `permansson-app about` prints the imported module location: when validating an installed wheel, reject a run whose package is actually imported from the checkout.

`resources --full` exports the packaged examples and schemas. Readers can therefore reproduce the exercises without inventing model inputs. No source file needs to be modified to run them. Paths below assume:

```bash
EX=/tmp/perma-d-resources/examples
```

A successful `finite-kernel` run:

```bash
permansson-app finite-kernel "$EX/finite_world.v1.model.json" \
  --output /tmp/perma-d-kernel
cat /tmp/perma-d-kernel/independent_check.json
cat /tmp/perma-d-kernel/scientific_report.json
```

The output directory is a **write-once result location**. An existing directory, symlinked output scope, invalid input, or exhausted budget must fail without producing a misleading final receipt. For a second run, use a *different* directory.

## D01.2. The common JSON philosophy

The first example's top-level format is `Permansson.App.FiniteStrategicWorld.v1`. Its six required keys are `format`, `states`, `feasible`, `alpha`, `P` and `U` (the names in the actual schema are case-sensitive). The state sets are separately typed `strategic`, `world`, `actions`, rather than one undifferentiated list. `feasible` records the legal action menu at each joint state; `alpha` gives an exact probability distribution over actions; `P` gives the physical successor distribution conditional on `(s,x,a)`; and `U` gives the strategic successor conditional on `(s,x,a,x')`. The induced kernel has entries

$$K((s,x),(s',x'))=\sum_{a\in\mathcal F(s,x)}\alpha(a\mid s,x)P(x'\mid s,x,a)U(s'\mid s,x,a,x').$$

Always check *all* source rows are normalized before interpreting `K`. A uniform `alpha` example is not a license to ignore the action distribution. `P` and `U` remain distinct by design: the order of one transition is **action selection, physical update, strategic update**. The source implementation is `src/permansson_app/finite_world.py`, the independent checker is `src/permansson_app/receipts/finite_world.py`, and the formal bridge document is `docs/FINITE_WORLD_LEAN_REIFICATION_V1.md`.

Exact rational numbers are strings such as `"1/2"`, `"0"`, and `"-3/4"`, not JSON floating-point approximations. The canonical typed-rational identity is not the historical Application Standard's older digest. The source rejects duplicate keys and nonfinite numeric values; individual schemas reject extra fields and invalid dimensions. A JSON document can pass JSON syntax and still fail mathematical validation (for example, a row summing to `3/4`). See `strict_json.py`, `schema_validate.py`, `semantics.py` and `docs/SEMANTIC_DIGEST_PROFILE.md`.

## D01.3. The 27-schema map

There are **27 schema files**, not 26; the extra structures include the native request/result envelopes and shared region/model definitions. Each executable profile uses its own request-specific schema, often with a nested `finite_world.v1` model. The authoritative schema registry is `src/permansson_app/data/schemas/` and the dynamic parser lives in `__main__.py`. Some schemas are wrappers with `allOf`/`$ref` or other composition, so a shallow scan for top-level `required` is insufficient; runtime semantic checks remain mandatory even after draft-2020-12 validation.

A dependable human checklist before a run:

1. Pick **exactly one** capability and inspect its declared `scope` in `data/capabilities.json`.
2. Validate that the nested model uses the correct `format`, complete finite typed inventories and normalized rational rows.
3. Confirm the **information timeline**: whether an observation precedes a control, whether nature sees a mixed strategy or realized action, and whether feedback changes with the deadline.
4. Confirm time semantics: horizon `0` includes the initial state; first hit differs from residence and never-exit mass.
5. Confirm the **quantifier boundary**: listed frozen alternatives, all permitted deterministic controls, an explicitly bounded randomized policy class, or classwise stationary laws.
6. Run a fresh directory; read both `independent_check.json` and `scientific_report.json` before the producer's proposed optimum.

## D01.4. Whole-run budget and failure behavior

The published numeric application is Linux-only because the subprocess budget uses Linux process limits. The [packaged limits](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/EXAMPLES_AND_LIMITS.md) specify: request size up to **128 KiB**, canonical input rationals bounded to **256 bits** per numerator/denominator, result readback rationals bounded to **14,000 bits**, and some intermediates limited to **8,192 bits**. The whole-run defaults are **300 seconds wall time**, **240 seconds CPU**, **2 GiB address space**, **32 MiB total and per-output file**, and **1 MiB stdout/stderr capture**. Configured limits may be lowered, not raised, by `PERMANSSON_RUN_BUDGET`. Development `lean-emit`/`lean-recheck` and native `run` have different budget boundaries.

Numeric commands have structured failure codes such as `BUDGET_TIMEOUT`, `BUDGET_CPU`, `BUDGET_MEMORY`, `BUDGET_OUTPUT`, `BUDGET_STREAM`, `PLATFORM_UNQUALIFIED`, input/schema errors, and certificate failures. Exit status `2` is a failure, not a weak form of verification. Do not put placeholder results in the output folder after a failed run.

**Exercise D01-A (no model editing).** Export resources, run the packaged `finite_world.v1.model.json`, and compare `independent_check.json` with the engine receipt. The local source check performed for the source baseline produced `status: PASS`, `checked_atoms: 16`, `proof_status: NOT_EXECUTED`. Those fields are a bound exact numerical consistency check, *not* a newly compiled Lean theorem. Repeat with `permansson-app about` and record the imported package path and Python version.

**Source trail:** `application-successor/README.md`, `docs/EXAMPLES_AND_LIMITS.md`, `docs/CAPABILITY_SCOPES.md`, `src/permansson_app/` (modules: `__main__.py`, `strict_json.py`, `schema_validate.py`, `finite_world.py`, `budget.py`, `report.py`); release tag `permansson-app-v0.2.0`.

# D02. Finite dynamics: kernels, survival, occupation, exit and perturbation

This group evaluates a specified finite model; it does **not** silently turn a proposed intervention into an optimizing controller. The common formal source is the typed joint kernel, but each profile asks a different question and returns a different certificate.

## D02.1. Induced joint kernel — `finite-kernel`

Input: a complete typed `finite_world.v1` file. Output: the induced transition matrix and a `finite_world` receipt. Checker: `receipts.finite_world.check_finite_receipt`; Lean candidate family: `finite-world`. The independent checker reconstructs every joint-state transition atom, not merely the row sums. The packaged `2×2` strategic/world example has **four joint states and 16 matrix entries**, independently checked in the historical source run documented for v1.0.

Mathematically, source-model checking and generating a stochastic matrix are not the same as deriving the causal factors from a matrix. Many different `(alpha,P,U)` factorizations can induce the same `K`; their admissible intervention semantics need not coincide. A `K` alone is insufficient to assert a typed held-fixed intervention.

## D02.2. Finite killed survival — `finite-survival`

The request declares baseline and comparison models, a finite region, a target and a complete set of comparison states, and a horizon through **32** for up to **12** joint states. It calculates the exact survival table in a region using a killed kernel, with the finite comparison margin at each declared starting state. The source `engines/finite_survival.py` and `receipts/finite_survival.py` compute and recheck the same mathematical object using separate implementations. A finite survival difference is **not** infinite-time persistence, QSD uniqueness or Exact GR/PR certification.

## D02.3. Long-run occupation in a finite multichain — `finite-occupation`

For each finite bottom recurrent class the engine computes its stationary law, plus exact start-specific absorption probabilities. The returned **expected limit laws** mix the random limiting class laws with their absorption weights. Do not conflate the average of a random limiting law with the realized limiting class on a particular trajectory. The primary code is `engines/occupation.py`, with rational linear algebra in `engines/rational_linear.py` and an independent `receipts/occupation.py` checker. The package's `finite_world.v1.model.json` is the model input.

**Neutral interpretive example.** A fictional help desk may settle permanently into one of two service modes. A start-specific probability of eventual entry into each recurrent class is not a prediction of which class an individual observed execution will choose, and no arbitrary finite observation establishes stationarity by itself.

## D02.4. Exit destinations and nonexit mass — `finite-exit`

This command takes **two positional input files**: the typed model plus `finite_region.v1.json` specifying the region and deadline. The checker verifies finite-horizon survival and the first-exit-by-destination subprobability vector. **Never normalize away never-exit mass.** If, by a given deadline, probability `1/5` remains inside, the first-exit destination masses add to `4/5`, not to `1`; scaling them to one answers a different conditional question. The receipt captures the distinction, and the `exit` bridge binds the region file as well as the model.

```bash
permansson-app finite-exit "$EX/finite_world.v1.model.json" \
  "$EX/finite_region.v1.json" --output /tmp/perma-d-exit
```

## D02.5. Finite total-variation perturbations — `finite-perturbation`

A perturbation request supplies **two fully typed finite models** with the same ordered joint-state inventory, a declared region, two starting laws and horizon `h ≤ 32`. It checks exact killed-process survival differences, every row TV distance, and a coupling bound of the form

$$\lvert p_h - q_h\rvert \le \min\{1,\operatorname{TV}(\mu,\nu)+h\max_y\operatorname{TV}(K(y,\cdot),L(y,\cdot))\}.$$

The inequality is a finite-horizon result. It does not establish robustness of limiting distributions without additional hypotheses. In the packaged example the numerical receipt passes, but the example is **outside the corresponding Lean reflection bound**; the checked bridge is demonstrated separately in narrower replay fixtures. The correct report is numerically verified, not instance-Lean compiled.

**Exercise D02-A.** Run `finite-occupation` and `finite-exit` with the packaged files, locate the recurrent-class weights and never-exit mass, and explain why neither is an unconditional claim that a real service will permanently remain in the region. **Exercise D02-B.** Inspect the `finite-perturbation` output and distinguish the exact measured row-TV from the derived finite-time upper bound; record the effect of changing only the deadline.

**Proof and code references:** `engines/{finite_survival,occupation,exit,robustness}.py`, `receipts/{finite_survival,occupation,exit,robustness}.py`, `docs/NUMERIC_FOUNDATIONS.md`, and bridge documents `MENU_LEAN_BRIDGE.md`, `OCCUPATION_LEAN_BRIDGE.md`, `EXIT_LEAN_BRIDGE.md`, `PERTURBATION_LEAN_BRIDGE.md`.

# D03. Finite optimizers: menus, feedback, safety, residence and stationary objectives

The difference among these profiles is not a technical nuisance; it is the central mathematical substance. Each calculation is **relative to a declared controller class, observation structure and objective**.

## D03.1. Explicit frozen alternatives — `frozen-menu`

The input enumerates **one to eight** complete admissible alpha/U interventions, with the physical transition `P` and feasibility held fixed. The finite objective is survival or exit through a declared horizon. The result lists the exact value of each candidate and **every tied optimum**. It cannot assert optimality outside the enumerated menu. `engines/menu.py` is the producer; `receipts/menu.py` checks the entire result.

## D03.2. Fully observed hitting — `finite-bellman`

With up to **12 joint states** and **24 transitions**, the input specifies a goal and forbidden set, fully observed admissible controls, and a deadline. The source computes the backward recurrence

$$V_{t+1}(y)=\begin{cases}1&y\in G,\\0&y\in D,\\\displaystyle\max_{a\in\mathcal F(y)}\sum_{y'}K_a(y,y')V_t(y')&y\notin G\cup D.\end{cases}$$

Here `K_a` is derived from the source's **P then U** rows for the chosen action. The baseline `alpha` is not silently redefined as an optimal controller. The checker validates **every horizon/state value and all tied optima**, not just a reported terminal scalar. The permitted class is finite fully observed, deterministic, remaining-horizon Markov schedules; the related research theorems are treated separately in Volume C.

## D03.3. Greatest almost-sure controlled invariant core — `finite-safety`

Given a declared safe set, repeatedly remove every state that lacks a permitted action whose successor support remains inside the current set. The descending pruning terminates on a finite set. The output provides the complete pruning iterates and a stationary witness for the **greatest almost-sure safety core**. A state outside the core can still have a nonzero probability of surviving for some time; exclusion means the prescribed **probability-one invariant** criterion cannot be met, not that every path immediately fails. The packaged example is numerically verified but exceeds its Lean reflection bound; test fixtures separately cover small instances.

## D03.4. Residence and deadlines — `finite-residence`

A residence request specifies a target, danger set, initial law, horizon semantics, and a *dwell number of transitions*. The source supports distinct first-entry, retryable and avoid monitors, up to **eight joint states**, deadline **eight**, and dwell **four**. The event “hit target once” is not “remain in target for `m` successive transitions.” Read `deadline_semantics` before interpreting an answer: being resident by a completion deadline differs from first entering by a deadline with observation extending beyond it. The independent checker recomputes the monitor-state recursion and terminal accounting. The packaged residence example is outside the bridge's instance reflection bound.

## D03.5. Classwise nonlinear stationary selection — `nonlinear-stationary`

The implementation enumerates feasible deterministic stationary policies on up to **eight joint states**, capped at **64 policies**, and evaluates the particular coded classwise functional **`F(p) = 1 - |p - 2/3|`** on stationary classes before averaging over absorption weights. It does not accept an arbitrary user-defined nonlinear utility or optimize over every history-dependent strategy. Check the actual `functional_id`, `policy_class`, stationarity and normalization in the JSON request. Averaging first and applying a nonlinear function later would generally change the answer: `E[F(X)] ≠ F(E[X])`.

**Exercise D03-A.** Run `finite-bellman` and `frozen-menu` on their separate packaged inputs. Compare the admissible controller classes and explain why their optimum numbers cannot be directly ranked as if they shared one strategy space. **Exercise D03-B.** Use the elementary values `p_1 = 1/2`, `p_2 = 1` with equal class probabilities to show that `E[1-|p-2/3|] = (5/6+2/3)/2=3/4`, while `1-|E[p]-2/3|=11/12`; this is an illustration of order of operations, not the packaged nonlinear model's computed result.

**Source trail:** `engines/{menu,hitting,safety,residence,nonlinear}.py`, `receipts/{menu,control,safety,residence,nonlinear}.py`, `docs/NUMERIC_FOUNDATIONS.md`, `docs/NUMERIC_RESIDENCE_NONLINEAR.md`, and related bridge documents.

# D04. Linear certificates, one-step risk, and independent infeasibility

A solver's claimed optimum or impossibility is trustworthy only if the claim has a checkable witness under the stated constraints. This chapter introduces three related but distinct constructions: a general exact LP, a one-step occupancy/risk model whose optimization is expressed as an LP, and a direct certificate that a one-step risk cap is impossible under the declared policy class.

## D04.1. Exact rational LP — `lp-propose`

The model schema `lp.v1.schema.json` requires `format`, `variables`, `objective`, `bounds`, and `constraints`. Variables and coefficients are explicit rational values. The engine `engines/lp.py` enumerates bounded exact candidates (at most **six variables**) and proposes certificates. In the packaged model, variables `x,y` have nonnegative lower bounds, objective `maximize x+y`, and the sole nontrivial constraint `x+y ≤ 1`. A proposed primal value of one is valid, but equality alone is insufficient evidence of optimality: a verifier must also check primal feasibility, dual feasibility, and matching objective values.

```bash
permansson-app lp-propose "$EX/lp.v1.model.json" \
  --output /tmp/perma-d-lp
cat /tmp/perma-d-lp/independent_check.json
```

The **negative case** is as important as a certificate: a bounded search that cannot find one returns `NO_CERTIFICATE_FOUND`. That is not a mathematical proof that the original LP is infeasible. Feasibility and optimality are distinct claims, and an LP's reported optimum cannot be substituted for the physical controller returned by a separate model.

## D04.2. Exact LP verifier — `lp-check`

`lp-check` is an **independent consumer** of a supplied optimality or Farkas infeasibility certificate. It does **not** have a separate packaged standalone input fixture. The command takes the original LP input **and the certificate object itself**. `lp-propose` writes an *envelope* named `proposal.json`, containing `status` and nested `receipt`; supplying that whole envelope directly to `lp-check` fails with `LP_CERT: unknown certificate family`. Extract its actual `receipt` into its own JSON file before verifying:

```bash
python - /tmp/perma-d-lp/proposal.json /tmp/perma-d-lp-certificate.json <<'PYCODE'
import json, sys
with open(sys.argv[1], encoding='utf-8') as f:
    envelope = json.load(f)
with open(sys.argv[2], 'w', encoding='utf-8') as f:
    json.dump(envelope['receipt'], f, indent=2)
    f.write('\n')
PYCODE
permansson-app lp-check "$EX/lp.v1.model.json" \
  /tmp/perma-d-lp-certificate.json --output /tmp/perma-d-lp-verified
cat /tmp/perma-d-lp-verified/independent_check.json
```

The checker verifies the claimed certificate directly, without calling the `lp-propose` producer. When the source and supplied certificate disagree, failure is correct. A case of the wrong certificate family must also fail. The latest dedicated verification pass for this project checked the real producer-to-consumer handoff and a malformed-family rejection, separately from the packaged walkthrough.

For an LP in standard primal/dual form, weak duality says any feasible primal objective is bounded by any feasible dual objective (with the inequality direction determined by maximize/minimize conventions). **Equality plus both feasibilities** proves a global optimum over the declared feasible set. A Farkas ray is instead a separating certificate of infeasibility. The Lean `lp` bridge reflects these rational objects into the finite problem and transfers the corresponding exact theorem, within its supported bounds.

## D04.3. One-step occupancy — `one-step-risk`

The request includes the complete model, initial joint-state law, terminal reward function, `risk_states` and a rational `risk_cap`. At an observed initial state, the controller may randomize over feasible actions. A single physical/strategic transition occurs; the controlled law is recomposed from the **original P and U**, not from a replaced or empirically fitted transition matrix. The profile permits at most **four joint states** and **five occupancy variables**. The checker validates the underlying flow, primal/dual certificate and realized next-state risk.

For the packaged synthetic example, the state starts `safe` and a hypothetical gamble action enters `danger`. The cap is `1/2`. The checked solution randomizes with probability `1/2` and has both expected terminal reward `1/2` and risk probability `1/2`. This is a deliberately simple teaching witness about a mathematical constraint, not a recommended action or an externally measured risk.

## D04.4. Proved risk-cap infeasibility — `one-step-risk-infeasibility`

This is not the fallback behavior of a failed optimizer. It is its own registered profile with an exact witness: for each initial state, calculate the least next-step risk achievable by any feasible action; weight these floors by the specified initial law; and show that the resulting lower bound is **strictly greater than the declared cap**. Randomization cannot beat the minimum at any state. Formally, if `r(y,a)` is the actual P/U probability of entering the designated risk set,

$$L=\sum_y \mu(y)\min_{a\in\mathcal F(y)} r(y,a), \qquad L>c \implies \Pr(\text{risk at step 1})>c$$

for every allowed fully observed randomized state-feedback controller. The checker validates the per-state floors, all attaining actions, the total and the strict shortfall. The packaged example reports **`L=7/16`**, whereas **`c=1/4`**, so the exact shortfall is `3/16`. The source intentionally refuses an infeasibility receipt if a feasible policy does exist.

**Exercise D04-A (two certificates).** Run `lp-propose`, supply its receipt to `lp-check`, and compare the two independent-check statuses. Then run `one-step-risk-infeasibility` and manually check `7/16 - 1/4 = 3/16`. Explain why a failed search is weaker than a checked Farkas-style certificate. **Exercise D04-B (scope test).** Extend the model by one transition and change the objective from risk at step 1 to risk at step 2, allowing an intermediate observation. Does the step-1 risk floor by itself bound the new terminal risk? **Answer:** no. The original step-1 bound still holds, but the step-2 objective requires the additional transition law and the controller's observation chronology to be modeled explicitly.

**Source trail:** `engines/{lp,lp_types,risk_occupancy,risk_infeasibility}.py`; `receipts/{lp,risk_occupancy,risk_infeasibility}.py`; `docs/NUMERIC_FOUNDATIONS.md`, `docs/NUMERIC_RISK_OCCUPANCY.md`, and `docs/` (files `LP_CERTIFICATE_LEAN_BRIDGE.md`, `FLOW_LEAN_BRIDGE.md`, and `RISK_INFEASIBILITY_LEAN_BRIDGE.md`).

# D05. Information, robust uncertainty, private draws and finite protocols

The five profiles in this chapter differ by **who observes what, at which point in the timeline**. Swapping those chronologies changes the optimization problem even if one reuses the same probability table. Work with supplied synthetic inputs rather than trying to manufacture real-world parameter estimates.

## D05.1. One-step partially observed decision — `one-step-belief`

A hidden world state `x` is drawn from the declared prior. An observation `o` is drawn from `Q(o|x)` **before** the chosen action. The controller selects one action legal for every hidden state compatible with the observed signal. The single transition then follows `P`, followed by `U`; the terminal reward applies after the transition.

The source supports one strategic state, **one to three hidden world states**, a bounded set of observations and actions, exact Bayesian posteriors on reachable signals, and complete enumeration of the bounded deterministic observation-contingent policies. If a signal has zero unconditional likelihood, its posterior is **undefined**, not a uniform distribution. If no action is jointly legal on an observation's positive-support hidden states, the input must fail rather than invent an action.

The packaged equipment-health example has hidden `healthy/damaged`, signals `green/red/unseen`, and actions `leave/repair`. Its checked observation policy chooses **leave after green**, **repair after red**, and obtains expected reward **`13/16`**. The best single blind action yields **`3/4`**, giving a one-step value of information **`1/16`**. The `unseen` signal is unreachable and deliberately has no posterior. This is not a complete multi-stage POMDP.

**Research cross-reference.** C06.1's one-prior reachable-history witness concerns remembered actions and a hidden completion flag. It does not enlarge this one-step command's information chronology or size limits.

## D05.2. Bounded observation-history tree — `finite-belief-tree`

This is a distinct profile, with **one to three transitions**, at most **two strategic** and **three hidden world states**, and at most **three observations/actions**. At each stage, the actual chronology is **observation → selected action → P → U**. The controller may condition on the complete observation history; feasibility must hold over the hidden-state support at that node. The producer uses exact Bayesian dynamic programming and the checker independently verifies unnormalized flows and replayed paths across the permitted deterministic tree policies.

The packaged example's optimum is **`55/64`**. It is a result over its bounded exhaustive policy family, not every imaginable continuous-state or infinite-horizon partially observed control system. Compare the one-step and multi-stage commands as separate implementations: the former's value-of-information witness does not substitute for a pathwise tree certificate.

**Research cross-reference.** C06.1 explains the actual reachable-history value separation and the separately scoped belief-sufficiency theorem. Current-readout insufficiency is compatible with an attaining sufficient belief representation.

## D05.3. Rectangular versus committed nature — `finite-robust-nature`

The input contains a baseline typed model, up to **six** admissible complete alternative physical `P` models, a fixed deterministic Markov policy, terminal rewards and a horizon through **12**. A *rectangular* nature may select its complete physical row after each observed control and state, whereas a *committed* nature must choose one whole `P` model at time zero. These are not the same uncertainty set. The application computes distinct finite rational comparisons and their complete horizon tables; it does **not** optimize the controller over all committed-nature games. The packaged robust-nature example is numeric-only relative to its narrower Lean reflection bound.

**Research cross-reference.** C07.1 adds the actual-law two-stage rectangular-game bridge, with committed value 9/100 and rectangular minimum 1/100. This source proof does not change the released profile's reflection bounds or claim general controller optimization against committed nature.

## D05.4. Nature sees a mixture, not the realized control — `finite-private-stage`

This one-stage game is not D05.3's revealed-control model. The controller announces a rational mixture over available controls; nature chooses a parameter while knowing the mixture **but before the private control draw**. With payoff table `Q(theta,c)`, the value is

$$v=\max_{p\in\Delta(C)}\min_{\theta\in\Theta}\sum_c p(c)Q(\theta,c).$$

The packaged `calm/boost/hold` by `dry/wet` example has a **two-sided, exact saddle certificate**:

- controller mixture `p=(1/2,1/2,0)`, guaranteeing value **`1`** against both nature parameters;
- nature mixture `q=(3/5,2/5)`, holding all pure controls to at most **`1`**;
- best pure control `hold`, whose worst-case payoff is **`1/2`**; thus randomization gain is **`1/2`**.

The independent checker verifies every inequality of both mixtures, not just the declared scalar optimum. The proof needs no unexamined minimax-theorem invocation because the two witnessed inequalities force matching lower and upper bounds. The limits are **one stage** and at most **four controls/four nature parameters**. The historical local execution documented for v1.0 reproduced the receipt values above with `independent_check.status=PASS`.

```bash
permansson-app finite-private-stage "$EX/private_stage.v1.json" \
  --output /tmp/perma-d-private
cat /tmp/perma-d-private/private_stage_receipt.json
cat /tmp/perma-d-private/independent_check.json
```

## D05.5. Finite two-player protocol — `finite-multiagent`

The registered profile represents a bounded two-player typed protocol. Each player has private-state and action tables; the application also receives a common update and physical kernel. It computes the baseline joint law and two distinct replacement mechanisms: **closed-loop** (one player's selection mechanism replaced while feedback remains) and **open-loop** (a declared anchor profile plus replacement). It checks the full joint kernel and row total variation while keeping `P` unchanged. The supported profile uses small matched private-state/action dimensions (each at most two). It does **not** cover the richer asymmetric types, private clocks and related research witnesses already proved elsewhere in `PermanssonResearch/MultiAgent/`.

**Exercise D05-A.** Recompute the Bayes posterior for `green` in the packaged one-step example, then explain why `unseen` must not be assigned a posterior. **Exercise D05-B.** Check `p=(1/2,1/2,0)` and `q=(3/5,2/5)` directly against the `private_stage` payoff matrix. **Exercise D05-C.** Write a paragraph on why nature observing the realized control, observing the announced mixture, and committing to one model before seeing future states are mathematically different protocols.

**Source trail:** `engines/` (modules: `belief.py`, `belief_tree.py`, `robust_nature.py`, `private_stage.py`, `multiagent.py`); the correspondingly named `receipts/` checkers; `docs/` (modules: `NUMERIC_BELIEF_CONTROL.md`, `NUMERIC_MULTISTAGE_BELIEF.md`, `NUMERIC_ROBUST_NATURE.md`, `NUMERIC_PRIVATE_STAGE.md`, `NUMERIC_MULTIAGENT.md`); their Lean bridge documents.

# D06. Typed intervention structure, constitutive certificates and special numerical analysis

This chapter groups seven different source-backed procedures. None can be replaced by “take the best-looking matrix.” Typing, admitted actions, invariance of the world model, equivalence-class transport, metric assumptions and specialized algebraic premises all matter.

## D06.1. Explicit patch grammar — `finite-grammar`

A patch-grammar input contains baseline alpha/P/U, a declared list of typed strategic patches, an explicit **admitted block family**, a comparison region/states/horizon, a finite value type and four-corner interaction requests. It compares only admitted blocks. The implementation enumerates all **inclusion-minimal positive** blocks in its declared grammar and calculates finite survival/exit effects and four-corner interactions. An unadmitted combination of two individually permitted patches must not be inferred to be permitted. The result does not by itself certify Exact PR.

**Research cross-reference.** C08.1 separates overlap compatibility from block admission; C08.2 treats original-margin minimality and local transport between nonisomorphic admitted orders. The numerical command still uses its explicitly supplied finite grammar.

## D06.2. Adaptation among admitted blocks — `finite-adaptive-grammar`

The request wraps the patch-grammar model. Before each transition, the controller may select **one complete admitted block** using observed history. The source computes a Bellman table over joint state and a *still-inside* flag, so a survival or exit event is not accidentally reset following an earlier exit. It compares the adaptive optimum against every frozen admitted block and reports the adaptivity gain. Limits: up to **eight blocks**, **12 joint states**, **eight transitions**. The packaged exercise's adaptive value is **`9/16`**, compared with **`3/8`** for its best fixed admitted block. That comparison cannot be used to smuggle in a never-admitted joint block.

**Research cross-reference.** The source-certified compatible-overlap menu in C08.1 is a positive construction. Its conflicting-patch rejection and joint-block exclusion are distinct negative results; normalized raw fold rows do not supply a certified admitted choice.

## D06.3. Strongly lumpable typed quotient — `finite-quotient`

The request supplies surjective mappings on the **strategic and world coordinates separately**, and the map must strictly reduce the joint state space. A quotient must be **strongly lumpable** for the baseline **and every declared intervention**, not merely for one favored starting distribution. For any fine states `y1,y2` with the same coarse image, and each target coarse block `B`, the aggregated transition sums must agree:

$$\sum_{z\in B}K(y_1,z)=\sum_{z\in B}K(y_2,z).$$

Only then do the relevant finite survival/exit evaluations transport consistently between fine and coarse representations. This profile does not construct a coarse typed `(alpha,P,U)` generator or establish regime claims beyond its finite transported event.

## D06.4. Finite CQ-1 constitutive certificate — `finite-cq1`

This request declares baseline and treated typed models, a region, basin, complete comparison set, property set, horizon and positive margin parameter `eta`. The allowed intervention changes **alpha and/or U**, holding `P` and action feasibility fixed. The engine computes killed survival inside the region, finite persistence conditions, prefix property survival under both models at **every declared comparison state**, and a **uniform comparison margin**. Limits are **12 joint states** and horizon **16**. A certificate of this explicitly finite condition is not an Exact Generated Regime or a universal constitutive PR claim.

## D06.5. CQ-1 transport under declared TV budgets — `finite-cq1-transport`

The request wraps a CQ-1 certificate and a nearby declared pair of typed models with compatible state, feasibility and physical `P`. It calculates the **exact maximum induced-row total-variation differences** `delta` between reference and approximate models. For a length `L`, a geometric discrepancy envelope is

$$e_L=1-(1-\delta)^L.$$

The resulting persistence and comparison-margin budgets account for those perturbations. A transported positive margin has the schematic form `kappa - e_0 - e_J`; it is accepted only if its actual required strict inequality holds. The application also recomputes the approximate pair's finite values as a consistency check. The packaged example reports a nominal margin **`8/25`**, an exact row discrepancy **`1/50`**, and transported margin **`301/1250`**. These are **distances between supplied models**, not estimates of the real world's uncertainty or missingness.

## D06.6. Metric contraction and specialized algebra — `finite-metric`, `finite-algebra`

`finite-metric` accepts a declared metric on up to **four joint states**. It computes exact finite Kantorovich/Wasserstein-1 row distances and checks optimal couplings **and attaining 1-Lipschitz potentials**. It identifies the contraction factor `rho`, row defects `delta` against a perturbed model, invariant laws where the required hypotheses hold, their exact distance, and the A3-style bound `delta/(1-rho)` **only when `rho < 1`**. A bound using `1/(1-rho)` without strict contraction is invalid.

`finite-algebra` covers four specialized matrix/vector witness families: seam equation and common mode; LDL positive-semidefinite witness with shell Schur complement; singular compatibility via preimage gap or incompatible kernel vector; and Gram gap/witness/perturbation threshold. The source limits dimensions to **four** and uses rational matrix witnesses; identifying an external operator or mechanism with those matrices remains a separate premise. Do not imply that this one command proves all of the research-only infinite-dimensional or external strategic-world extensions.

**Exercise D06-A.** Verify the quotient block-mass identity on a toy four-state stochastic matrix with two coarse blocks. Demonstrate that one unequal block sum invalidates strong lumpability even if two chosen starting states happen to have equal finite survival. **Exercise D06-B.** Simplify `1-(1-1/50)^2` exactly and explain why a finite-time TV envelope is not automatically a confidence interval. **Exercise D06-C.** Identify which premises are needed to interpret `delta/(1-rho)` as a bound, rather than a formally written fraction.

**Source trail:** `engines/` (modules: `grammar.py`, `adaptive.py`, `quotients.py`, `cq1.py`, `cq1_transport.py`, `metric.py`, `algebra.py`), their separate `receipts/` implementations, the matching `NUMERIC_*.md` documents and Lean bridge documents under `docs/`. See also `PermanssonResearch/ApplicationBridge/` for the proof-side correspondence.

# D07. Separate native C10/C11 providers, source pins and proof replay

## D07.1. Two kinds of application capability

The successor registry has two `capabilities` entries separate from the `exact_profiles` map. These are the historical native providers, wrapped without rewriting them:

- `c10.fixed_six_state.numeric.v1`: the **single fixed six-state** C10 intervention/comparison setup;
- `c11.stationary_1_to_6.numeric.v1`: exact rational **one-to-six-state** stationary-law computation, including periodic and multichain examples.

They use `permansson-app run <request>` with `--source-root <root>` and `--output <new directory>`, not `finite-*` entry points. The native request schema carries `format`, `capability` and a relative `input_file`. The wrapper resolves the declared provider, checks its stored SHA-256 source pins, copies the input bytes to a private frozen file, runs the native producer with the bounded runner, independently verifies the resulting numerical receipt, and checks that source and input bytes did not change. It returns `application_result.json` with separate numerical and scientific statuses.

For an exact source checkout:

```bash
ROOT=/path/to/PermanssonLean
permansson-app run "$EX/c10.request.json" --source-root "$ROOT" \
  --output /tmp/perma-d-c10
permansson-app run "$EX/c11.periodic.request.json" --source-root "$ROOT" \
  --output /tmp/perma-d-c11-periodic
permansson-app run "$EX/c11.multiclass.request.json" --source-root "$ROOT" \
  --output /tmp/perma-d-c11-multiclass
```

Do not confuse numerical C10/C11 wrapping with the native providers' own **`--mode replay`**. A clean pinned Git checkout, authentic source identity, pinned Lean compiler, generated Lean proof and axiom audit are additional conditions for true proof replay. The successor's default numeric wrapper deliberately keeps `lean_status=NOT_EXECUTED`.

## D07.2. C10 is not a universal finite-input optimizer

The C10 closure successor `apps/permansson/closure-successor/` accepts only the original **frozen six-state rational model** with six named interventions and the complete comparison starts `[1,2]`. Even another well-formed matrix is unsupported unless a separate typed adapter theorem is established. The existing `C10SixStateBridge` and its reified golden instance are an explicit bounded model, not an inference from arbitrary JSON.

Its native `VERSION.json` still records `DRAFT__COMPILER_CI_PENDING` despite subsequent passing compiler-backed tests. This historical field has not been silently promoted to independent application acceptance. See `apps/permansson/closure-successor/README.md`.

## D07.3. C11 has its own stationary-law scope

The independent C11 provider lives under `apps/permansson/closure-successor-c11/`. Its native model accepts **exactly** `n`, `matrix`, `descriptor`; `n` is one through six, each stochastic row is a rational vector, and the descriptor is Boolean by state. Periodic and multiple bottom recurrent classes are covered by the provided examples. A valid C11 stationary proof is about the **reified rational matrix**, not an automatically reconstructed causal strategic generator, policy family or real-world process.

## D07.4. Optional bounded Lean reflection of the 26 profiles

For a supported numeric profile, the source-bound candidate path is:

```bash
permansson-app finite-private-stage "$EX/private_stage.v1.json" \
  --output /tmp/perma-d-proof-numeric
permansson-app lean-emit --family private-stage "$EX/private_stage.v1.json" \
  /tmp/perma-d-proof-numeric/private_stage_receipt.json \
  --output /tmp/perma-d-proof-candidate
permansson-app lean-recheck --family private-stage "$EX/private_stage.v1.json" \
  /tmp/perma-d-proof-numeric/private_stage_receipt.json \
  --candidate /tmp/perma-d-proof-candidate
```

Only **after** a successful byte check and a built `PermanssonResearch` library does the separately invoked `lake env lean <candidate.lean>` establish a kernel-checked result for the literal data; the Research replay harness also audits printed theorem axioms and rejects meaningful mutations. The application does not authenticate that external compiler event. Four packaged examples (`finite_safety`, `finite_perturbation`, `residence`, `robust_nature`) exceed their Lean reflection bounds even though the numeric examples pass; the corresponding bridges are exercised on separate in-bound fixtures.

For a full reproducibility run, reuse the existing source tool rather than constructing an unreviewed tutorial runner:

```bash
python apps/permansson/application-successor/scripts/end_to_end.py \
  --report /tmp/perma-d-end-to-end.json
# With pinned lake available and the Research library built:
python apps/permansson/application-successor/scripts/end_to_end.py --lean
```

The script covers 25 *primary* numeric examples, plus three native C10/C11 requests. The 26th profile, `lp-check`, is a separate certificate consumer and must be tested as `lp-propose → lp-check`. A numeric result is never reclassified as a compiled proof by omission of `--lean`, and a source ZIP alone does not authenticate a Git head.

## D07.5. Review gates and answer key

A complete output package should retain: original input and source identity; schema and scope; the exact receipt; the independent-check result; `scientific_report.json`; optional Lean candidate and byte-recheck metadata; the separately authenticated compiler log and axiom report **if actually executed**; and a limitation statement. The scientific report keeps nine original certificate dimensions unassessed (`null`) rather than claiming `VALID` or `CERTIFIED`. Independent mathematical acceptance and empirical identification are independent projects.

**Exercise D07-A.** Read the three native request files and identify why C10 supports a single fixed six-state case whereas C11 supports a bounded stationary matrix family. **Exercise D07-B.** Explain what evidence changes on a successful `lean-emit`, `lean-recheck`, and separate compiler run, and what does **not** change in the original `scientific_report.json`.

**Source trail:** `apps/permansson/{closure-successor,closure-successor-c11}/README.md`; `application-successor/src/permansson_app/` (modules: `runner.py`, `source.py`, `contracts.py`, `capabilities.py`, `replay.py`, `report.py`); `application-successor/docs/` (modules: `NATIVE_PROOF_REPLAY.md`, `REVIEWER_GUIDE.md`, `EVIDENCE_AND_RECEIPTS.md`); `PermanssonResearch/ApplicationBridge/`; `verification/research/test_application_*_live_lean.py`.

# Volume D — answer key and review checklist

**D01-A:** `independent_check.json.status` is the decisive independent numerical status; `lean_status` remains `NOT_EXECUTED`. `about` identifies the actual package location. **D02-A:** recurrent-class absorption weights and never-exit mass are different events; neither identifies an observed system. **D02-B:** row-TV is an input-pair discrepancy and the event bound is a derived upper bound whose horizon dependency must be respected. **D03-A:** frozen menus and feedback controllers optimize over distinct admissible classes. **D03-B:** the provided `p_1,p_2` yield `3/4` versus `11/12`, demonstrating noncommutation.

**D04-A:** matching checked primal/dual values establish the declared LP optimum; the exact risk shortfall is `3/16`. **D04-B:** the first-step risk bound remains valid; a second-step risk objective requires new transition and information semantics. **D05-A:** a zero-likelihood observation has no defined posterior. **D05-B:** both saddle sides meet value `1`; the mixture gain over the best pure control is `1/2`. **D05-C:** reveal, mixture-private and committed uncertainty are different mathematical games. **D06-A:** strong lumpability requires every pair within every fiber to have matching destination-block sums. **D06-B:** `1-(49/50)^2 = 99/2500`, a deterministic mathematical discrepancy envelope. **D06-C:** strict `rho<1`, a valid declared metric, exact coupling/dual witnesses, and appropriate invariant-law assumptions must all hold. **D07-A:** native provider scopes are source-versioned and do not inherit arbitrary successor profile inputs. **D07-B:** byte binding and compiler evidence raise the evidence level of an instance only when each step is genuinely executed; the application report still does not attest that compiler run.

**Reviewer checklist:** verify every example's source identity, JSON schema and dimension bounds; read the CLI's exact status as well as the independent checker's status; check no LP or infeasibility assertion relies on an unsuccessful proposal; inspect policy class, observation chronology and finite/infinite horizon; verify an emitted Lean candidate's bytes before compile; check actual compiler logs and axiom allowlist when compilation is claimed; distinguish published v0.2.0 numeric scope from unreconciled native-provider acceptance; leave scientific and empirical-identification flags unchanged unless independently established.


# Appendix D-A. Complete implemented 26-profile crosswalk

This table is generated from the **actual registry** and the audited engine/fixture/bridge crosswalk at the frozen source commit. Each command is documented in [`CAPABILITY_SCOPES.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/CAPABILITY_SCOPES.md). The 25 primary command fixtures are run by `scripts/end_to_end.py`; `lp-check` takes a certificate from `lp-propose`.

| Command | Packaged example | Producer / independent receipt checker | Lean family |
|---|---|---|---|
| `finite-adaptive-grammar` | `adaptive` | `adaptive.py` / `adaptive.py` | `adaptive` |
| `finite-algebra` | `algebra` | `algebra.py` / `algebra.py` | `algebra` |
| `finite-belief-tree` | `belief_tree` | `belief_tree.py` / `belief_tree.py` | `belief` |
| `finite-bellman` | `control_hitting` | `hitting.py` / `control.py` | `control-table` |
| `finite-cq1` | `cq1` | `cq1.py` / `cq1.py` | `cq1` |
| `finite-cq1-transport` | `cq1_transport` | `cq1_transport.py` / `cq1_transport.py` | `cq1-transport` |
| `finite-exit` | `finite world + region` | `exit.py` / `exit.py` | `exit` |
| `finite-grammar` | `grammar` | `grammar.py` / `grammar.py` | `grammar` |
| `finite-kernel` | `finite_world` | `finite_world.py` / `finite_world.py` | `finite-world` |
| `finite-metric` | `metric` | `metric.py` / `metric.py` | `metric` |
| `finite-multiagent` | `multiagent` | `multiagent.py` / `multiagent.py` | `multiagent` |
| `finite-occupation` | `finite_world` | `occupation.py` / `occupation.py` | `occupation` |
| `finite-perturbation` | `finite_perturbation` | `robustness.py` / `robustness.py` | `perturbation` |
| `finite-private-stage` | `private_stage` | `private_stage.py` / `private_stage.py` | `private-stage` |
| `finite-quotient` | `quotient` | `quotients.py` / `quotients.py` | `quotient` |
| `finite-residence` | `residence` | `residence.py` / `residence.py` | `residence` |
| `finite-robust-nature` | `robust_nature` | `robust_nature.py` / `robust_nature.py` | `robust-nature` |
| `finite-safety` | `finite_safety` | `safety.py` / `safety.py` | `safety-core` |
| `finite-survival` | `finite_survival` | `finite_survival.py` / `finite_survival.py` | `survival` |
| `frozen-menu` | `finite_menu` | `menu.py` / `menu.py` | `menu` |
| `lp-check` | `LP certificate` | `lp.py` / `lp.py` | `lp` |
| `lp-propose` | `lp` | `lp.py` / `lp.py` | `lp` |
| `nonlinear-stationary` | `nonlinear` | `nonlinear.py` / `nonlinear.py` | `nonlinear` |
| `one-step-belief` | `belief` | `belief.py` / `belief.py` | `belief` |
| `one-step-risk` | `risk_occupancy` | `risk_occupancy.py` / `risk_occupancy.py` | `flow` |
| `one-step-risk-infeasibility` | `risk_infeasibility` | `risk_infeasibility.py` / `risk_infeasibility.py` | `risk-infeasibility` |

A fixture key like `belief` means the source `belief.v1.json`, `finite_world` means `finite_world.v1.model.json`, and `lp` means `lp.v1.model.json`; full names remain in the companion CSV and source example directory. The module column shows **filenames only**, to remain readable on paper. The complete tracked paths are in the companion `Permansson_Verified_26_Profile_Integration_2026-11-19.csv`: producers normally live in `src/permansson_app/engines/`, independent checkers in `src/permansson_app/receipts/`; `finite_world.py` is the producer outside `engines/`. The two-file `finite-exit` input and extracted `lp-check` certificate are demonstrated in D02/D04. The table gives the **entry point**, not an assertion that every bridge supports every numerically valid fixture. Four packaged examples exceed their bridge reflection limits and remain numeric-only for that particular fixture (`finite_safety.v1.json`, `finite_perturbation.v1.json`, `residence.v1.json`, `robust_nature.v1.json`). The command's exact dimension and objective limits are not inherited from neighboring profiles.

## D-A.1. Exact CLI status and reflection expectation

`end_to_end.py` requires each command's exact expected CLI status and independent-check status. The right column gives **CLI field/value → checker status**; `same` means the exact same string must appear in the checker response, not that the separate checks are interchangeable. Every status is drawn from the current `PROFILES` registry in the walkthrough.

| Command | CLI result → independent checker |
|---|---|
| `finite-kernel` | `numeric_status: EXACT_RATIONAL_VERIFIED` → `PASS` |
| `finite-survival` | `numeric_status: FINITE_SURVIVAL_TABLE_VERIFIED` → `same` |
| `finite-occupation` | `numeric_status: EXACT_RATIONAL_VERIFIED` → `PASS` |
| `finite-exit` | `numeric_status: EXACT_RATIONAL_VERIFIED` → `PASS` |
| `frozen-menu` | `numeric_status: FROZEN_MENU_OPTIMUM_VERIFIED` → `same` |
| `finite-bellman` | `numeric_status: EXACT_FINITE_BELLMAN_CHECKED` → `PASS` |
| `finite-safety` | `numeric_status: EXACT_ALMOST_SURE_SAFETY_CORE_VERIFIED` → `PASS` |
| `finite-perturbation` | `numeric_status: FINITE_PATH_TV_BOUND_VERIFIED` → `PASS` |
| `finite-residence` | `numeric_status: PASS` → `same` |
| `nonlinear-stationary` | `numeric_status: PASS` → `same` |
| `finite-grammar` | `numeric_status: PASS` → `same` |
| `finite-adaptive-grammar` | `numeric_status: PASS` → `same` |
| `finite-quotient` | `numeric_status: PASS` → `same` |
| `one-step-risk` | `numeric_status: PASS` → `same` |
| `one-step-risk-infeasibility` | `numeric_status: INFEASIBILITY_VERIFIED` → `same` |
| `finite-robust-nature` | `numeric_status: PASS` → `same` |
| `finite-private-stage` | `numeric_status: PASS` → `same` |
| `one-step-belief` | `numeric_status: PASS` → `same` |
| `finite-belief-tree` | `numeric_status: PASS` → `same` |
| `finite-cq1` | `numeric_status: PASS` → `same` |
| `finite-cq1-transport` | `numeric_status: PASS` → `same` |
| `finite-metric` | `numeric_status: PASS` → `same` |
| `finite-algebra` | `numeric_status: PASS` → `same` |
| `finite-multiagent` | `numeric_status: PASS` → `same` |
| `lp-propose` | `status: CHECKED_OPTIMAL_CANDIDATE` → `OPTIMAL_VERIFIED` |
| `lp-check` | `status: OPTIMAL_VERIFIED` → `same` |

## D-A.2. Independent checker source rule

The `receipts/` modules are not wrappers around the engine's returned value. They separately reconstruct the mathematical claims or verify independently checkable certificates: LP dual feasibility, the Farkas ray, all Bellman table rows, complete survival or occupation probabilities, robust saddle sides, and exact transport budgets. The checker must not call or reuse its profile's result-producing algorithm. Shared types, constants and input parsers are permitted and must be reviewed as shared dependencies. The release tests include tamper and malicious-input rejection.

# Appendix D-B. The 27 versioned schema files

The table below is an **index to the actual schema files**, not a replacement for Draft 2020-12 reference expansion and the runtime semantic validator. Some schemas use nested `$ref`, combinators or branch-specific constraints; do not infer that `required: none` means an unconstrained request.

| Schema file | Top-level required fields explicitly declared |
|---|---|
| `adaptive.v1.schema.json` | `format`, `grammar` |
| `algebra.v1.schema.json` | *Composed/branch-specific; inspect schema* |
| `belief.v1.schema.json` | `format`, `model`, `prior`, `observations`, `likelihoods`, `terminal_rewards` |
| `belief_tree.v1.schema.json` | `format`, `model`, `horizon`, `prior`, `observations`, `likelihoods`, `terminal_rewards` |
| `c10.native.schema.json` | *Composed/branch-specific; inspect schema* |
| `c11.native.schema.json` | `n`, `matrix`, `descriptor` |
| `control_hitting.v1.schema.json` | `format`, `model`, `goal`, `forbidden`, `horizon` |
| `cq1.v1.schema.json` | `format`, `baseline`, `intervention`, `region`, `basin`, `comparison`, `property_set`, `horizon`, `eta` |
| `cq1_transport.v1.schema.json` | `format`, `cq1`, `approximate` |
| `finite_menu.v1.schema.json` | `format`, `baseline`, `region`, `start_state`, `horizon`, `value_type`, `direction`, `menu` |
| `finite_perturbation.v1.schema.json` | `format`, `baseline`, `alternative`, `region`, `initial_baseline`, `initial_alternative`, `horizon` |
| `finite_region.v1.schema.json` | `format`, `joint_states`, `horizon` |
| `finite_safety.v1.schema.json` | `format`, `model`, `safe` |
| `finite_survival.v1.schema.json` | `format`, `baseline`, `treated`, `target`, `region`, `comparison_states`, `horizon` |
| `finite_world.v1.schema.json` | `format`, `states`, `feasible`, `alpha`, `P`, `U` |
| `grammar.v1.schema.json` | `format`, `baseline`, `patches`, `admitted_blocks`, `region`, `comparison_states`, `horizon`, `value_type`, `four_corners` |
| `lp.v1.schema.json` | `format`, `variables`, `objective`, `bounds`, `constraints` |
| `metric.v1.schema.json` | `format`, `baseline`, `perturbed`, `metric` |
| `multiagent.v1.schema.json` | `format`, `labels`, `players`, `common_update`, `world`, `treated_player`, `replacement`, `anchor` |
| `nonlinear.v1.schema.json` | `format`, `model`, `descriptor_true_states`, `initial_law`, `functional_id`, `policy_class` |
| `private_stage.v1.schema.json` | `format`, `labels`, `payoff` |
| `quotient.v1.schema.json` | `format`, `baseline`, `interventions`, `quotient`, `region`, `comparison_states`, `horizon`, `value_type` |
| `request.v1.schema.json` | `format`, `capability`, `input_file` |
| `residence.v1.schema.json` | `format`, `model`, `target`, `danger`, `mode`, `deadline`, `deadline_semantics`, `dwell_transitions`, `initial_law` |
| `result.v1.schema.json` | `format`, `capability`, `numeric_status`, `lean_status`, `scientific_claims_verified`, `empirical_identification`, `artifacts` |
| `risk_occupancy.v1.schema.json` | `format`, `model`, `initial_law`, `terminal_rewards`, `risk_states`, `risk_cap` |
| `robust_nature.v1.schema.json` | `format`, `baseline`, `nature_models`, `fixed_policy`, `horizon`, `terminal_rewards`, `comparison_states` |

`finite_world.v1.schema.json` declares the required keys `format`, `states`, `feasible`, `alpha`, `P`, `U`, but also constrains the interior rows and typed indexing. `request.v1.schema.json` is the native numeric request envelope; `result.v1.schema.json` is a reporting envelope; `c10.native.schema.json` and `c11.native.schema.json` are not arbitrary 26-profile wrappers. All files are located in `apps/permansson/application-successor/src/permansson_app/data/schemas/`.

# Appendix D-C. Source, review, and verification reading list

For implementation review, start in this order:

1. **Contract and version:** application [`README.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/README.md), `pyproject.toml`, `docs/RELEASE_ACCEPTANCE.md`, `docs/ACCEPTANCE_STATUS.md`.
2. **Scope and examples:** `src/permansson_app/data/capabilities.json`, `docs/CAPABILITY_SCOPES.md`, `docs/EXAMPLES_AND_LIMITS.md`.

   The packaged example directory is `src/permansson_app/data/examples/`.
3. **Actual computation:** `src/permansson_app/__main__.py`, `engines/`, `finite_world.py`, `receipts/`, `strict_json.py`, `schema_validate.py`, `budget.py`.
4. **Mathematical integration:** `PermanssonResearch/ApplicationBridge/`, `src/permansson_app/proof/`, and the `docs/*_LEAN_BRIDGE.md` files.
5. **Reproduction and integrity:** `scripts/end_to_end.py`, `scripts/inventory.py`, `verification/research/test_application_*_live_lean.py`, `docs/REVIEWER_GUIDE.md`.
6. **Native providers:** `closure-successor/` and `closure-successor-c11/` are separate from the historical `application/` standard.

\newpage

# Volume E — Verification, Evidence and Certification

> **Verification scope.** This volume explains verification, source identities, evidence handling, and the boundaries of certification for the repository as it exists. It uses synthetic mathematical instances and read-only inspection workflows; it does not supply operational conflict-targeting or attack-optimization procedures.
>
> **Frozen source:** `HMarcusWH/PermanssonLean` main commit `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`.

> **Git tree:** `cf3d19b5eaa3756fe5c2e392367b9066330e1a4b`.

> **Numerical release:** v0.2.0 is a distinct earlier tag at `63a66c82a9ece4361f646ee13b6711192f831406`.

# How to use this volume

Volumes A–C describe the mathematical objects and formal results. Volume D describes the executable numerical application. This volume explains a harder question: **What evidence justifies saying a particular result was correctly computed, proved for its literal model, reproduced at an identified Git commit, or independently accepted?** These are different predicates. Keep them separate when reading the rest of the guide and when producing a report.

The definitive source sequence is: [Reviewer Guide](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/REVIEWER_GUIDE.md), [Evidence and Receipts](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md), [Native Proof Replay](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NATIVE_PROOF_REPLAY.md), and the source code named in each chapter. Every reference to `src/permansson_app/` below is relative to `apps/permansson/application-successor/` unless explicitly stated otherwise.

| Question | Evidence source | What it cannot establish by itself |
|---|---|---|
| Were exact numerical outputs recomputed? | `independent_check.json`, checker implementation | That the inputs describe reality or Lean compiled this instance |
| Is candidate Lean text byte-bound to a request? | `lean-emit` and `lean-recheck` | That the compiler executed or a theorem was independently reviewed |
| Does a literal theorem instance compile? | Separately run pinned Lean plus permitted-axiom audit | Model/data identification, source of input, publication approval |
| Did exact-head GitHub checks pass? | Identified GitHub job and SHA | A later commit, a separate instance, or a paper interpretation |
| Is evidence authentic enough for a consumer? | Independent digest pins and trusted provenance | Who the reviewer was unless separately authenticated |
| Is the application release qualified? | Owner-controlled release manifest and qualification jobs | Scientific validation or independent mathematical certification |

# E01. Independent numerical checking and exact receipts

## E01.1. Why a second calculation matters

A finite mathematical engine may compute a value by dynamic programming, table enumeration, Gaussian elimination, rational linear optimization, or path recursion. A reviewer should not rely solely on the engine's proposed answer. In this application, the checkers under `src/permansson_app/receipts/` are separate source modules: they reconstruct the relevant values or check a compact witness rather than merely repeating an engine-supplied status. The intended architectural rule is that a profile's checker reconstructs the claim or checks its certificate without calling the profile's result-producing algorithm; it may share input parsers, types and constants. See the repository's [reviewer anatomy](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/REVIEWER_GUIDE.md).

For a finite transition row, the elementary normalization obligations are

$$
K_{ij}\ge 0,\qquad \sum_j K_{ij}=1.
$$

For a finite-horizon probability, the receipt must also identify the initial distribution, time convention, event, and quantifiers. An exact rational, such as $7/16$, is a mathematical value only *under that particular model and event definition*. The checker cannot turn $7/16$ into an empirically estimated chance.

## E01.2. Two independent verification styles

**Recomputation.** For finite Bellman tables, killed survival, exit routing, occupation, and many other profiles, the verifier reconstructs all table rows. In a transition model with initial vector $\mu$, row-stochastic matrix $K$, and event indicator column $1_G$, a one-step claim may be independently checked as $\mu K1_G$. For a constructed two-state example,

$$
\mu=(1,0),\qquad K=\begin{pmatrix}3/4&1/4\\1/2&1/2\end{pmatrix},\qquad
\mu K1_{\{0\}}=3/4.
$$

The same computation becomes a genuinely different event under a different time index or absorbing-state convention. Verification therefore includes **semantic scope**, not arithmetic alone.

**Certificate checking.** Other profiles return a checkable witness. For example, a rational linear program can be expressed as

$$
\max c^\top x\quad\text{subject to }Ax\le b,\ x\ge0.
$$

A feasible primal $x$ and feasible dual $y\ge0$ with $A^\top y\ge c$ and $c^\top x=b^\top y$ certify optimum by weak duality, without trusting the producer's search method. A one-step infeasibility result uses a verified Farkas witness; a private-stage saddle needs both sides of the mixed-strategy guarantee; a Bellman witness must satisfy every admitted-control recurrence. These are **different certificate types**. Do not infer one from another.

## E01.3. An actual run's output contract

The successor writes a receipt, an independently computed check, and a versioned report into a **new output directory**. For an example using its packaged finite-world fixture:

```bash
# From a supported Linux environment with the source application installed.
permansson-app resources --full --output /tmp/permansson-e-resources
permansson-app finite-kernel \
  /tmp/permansson-e-resources/examples/finite_world.v1.model.json \
  --output /tmp/permansson-e-kernel
cat /tmp/permansson-e-kernel/independent_check.json
cat /tmp/permansson-e-kernel/scientific_report.json
```

The command example is for a synthetic, prepackaged model. `finite-kernel` is part of the 26-profile registry. The independent status is expected to be `PASS` for its released fixture; consult the actual receipt for the precise number of checked atoms and the exact request identity rather than copying a number from this book.

The checker-status vocabulary is profile-specific, including `PASS`, `OPTIMAL_VERIFIED`, `INFEASIBILITY_VERIFIED`, `FINITE_SURVIVAL_TABLE_VERIFIED`, and `FROZEN_MENU_OPTIMUM_VERIFIED` for eligible reports. Those strings are **not** interchangeable success flags; the reader must compare them to that profile's contract and expected output. See `src/permansson_app/report.py`.

## E01.4. False positives a reader must reject

A report that contains correct-looking rational values but no independent check cannot be upgraded to verified. A certificate from the wrong request identity cannot be reused. A partial candidate search that times out is not an infeasibility proof. A result exceeding Lean's small-instance reflection limit can still have an exact independently checked numeric answer, but it lacks *that instance's* reflected Lean result. This is an expected scope boundary, not a contradiction.

**Exercise E01-A.** An engine claims $5/8$ for a fictional one-step event. An independent checker recomputes $4/8$ using the same declared row and initial law. Which claim can be reported as independently verified? **Answer:** neither numerical result is accepted as an agreed receipt until the discrepancy is resolved. The producer's status cannot override the checker.

**Source path checklist:** `src/permansson_app/engines/`, `src/permansson_app/receipts/`, `src/permansson_app/finite_world.py`, `src/permansson_app/identity.py`, `src/permansson_app/report.py`, `docs/EVIDENCE_AND_RECEIPTS.md`, and each profile's `docs/NUMERIC_*.md`.

# E02. Lean source-bound correspondence and replay

## E02.1. Four different checks

The application has **24 source-bound Lean bridge families** under [`PermanssonResearch/ApplicationBridge/`](https://github.com/HMarcusWH/PermanssonLean/tree/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonResearch/ApplicationBridge). Matching Python emitters live under `src/permansson_app/proof/`. A reflected file is a proposed theorem about **literal finite input tables**. It is not by itself an authenticated theorem execution report.

1. **Input parsing** establishes that a bounded request satisfies its strict schema and semantic limits.
2. **Numeric verification** establishes the exact receipt's declared model result by independent recomputation or certificate checking.
3. **Source recheck** reconstructs the emitted Lean text from those exact request and receipt bytes and verifies the candidate bytes and metadata.
4. **Pinned Lean compilation and axiom audit** separately check the generated instance declarations on the specified toolchain. Authenticating who executed that compiler is another evidence question.

The application deliberately keeps `lean_status = NOT_EXECUTED` in an ordinary numeric receipt even after `lean-emit` and `lean-recheck` pass. These commands do not secretly call `lake`. The [Native Proof Replay guide](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/NATIVE_PROOF_REPLAY.md) documents the workflow.

## E02.2. Source-bound but not source-authenticated

A candidate generated from a request/receipt pair can be byte-bound to it. A cryptographic hash is useful evidence of byte equality, but the digest must be compared with a hash obtained through a separately trusted channel. A hash enclosed within an untrusted bundle does not authenticate the bundle's origin. These distinctions recur in E03, E05, and E07.

For an eligible profile, the documented command sequence is:

```bash
permansson-app <profile-command> request.json --output run
permansson-app lean-emit --family <family> request.json \
  run/<receipt>.json --output candidate
permansson-app lean-recheck --family <family> request.json \
  run/<receipt>.json --candidate candidate
lake build PermanssonResearch
lake env lean candidate/Reified<Family>.lean
```

The tokens in angle brackets are **placeholders**, not executable literal filenames. In `--candidate candidate`, the first token is the option and the second is the chosen directory name. Check the bridge's `docs/*_LEAN_BRIDGE.md` for the profile-specific receipt filename, `--family` value, dimension limits, and resulting `Reified*.lean` path. The numeric `finite-exit` command uses the `exit` candidate family, which additionally requires `--region`; a user cannot assume every family shares exactly the same arguments. The pinned toolchain is Lean **4.34.0**.

The repository also supplies `scripts/end_to_end.py --lean` and live regression tests under `verification/research/test_application_*_live_lean.py` to perform the complete sequence on the packaged fixtures. Reuse those rather than constructing an unreviewed secondary compiler driver.

## E02.3. What Lean checks — and what it does not

The generated candidate includes theorem-specific `#print axioms` audits. The accepted transitive axiom set is restricted to `propext`, `Classical.choice`, and `Quot.sound`. The test suite rejects `sorry`, `admit`, custom axiom shortcuts, and semantically altered candidate statements. Positive compilation plus a correctly targeted **negative mutation** is stronger evidence that the intended declaration was actually checked, though neither substitutes for a separate authenticity or paper-to-proof review.

An instance may prove a universal statement relative to a declared finite model: e.g. the given Bellman value is optimal over all the represented admissible behavioral histories. But that is *the bridge's theorem statement*, not a license to remove the information assumptions, time horizon, state limits, or model factorization when explaining it in prose.

The `lean-emit` reflection limits are often tighter than the numerical engine limits. The published examples for finite safety, perturbation, residence, and robust nature exceed their particular bridge-reflection bounds, despite having verified numeric outputs. The guide must not present those example outputs as instance-compiled results.

## E02.4. The repository's actual proof/evidence split

The original `PermanssonLean/` root is the frozen theory lineage; `PermanssonResearch/` extends it with current research, including the bridge modules. The separate `PermanssonResearch.lean` library root is explicitly built by the Research Lean CI workflow. Seven standalone witness `.lean` files are compiled in regression tests; the remaining `PermanssonLean_root_imports_snapshot.lean` is a synchronized import snapshot, not an independent theorem to compile.

The CI checks for the audited commit are already recorded; a green Research Lean workflow proves that the **library declarations at that head** built. It does not, by itself, authenticate the newly emitted candidate in the user's output directory. A candidate needs its own replay and evidence trail.

## E02.5. Reader review checklist

For each of the 24 bridge families, record the input schema, the typed model constructed, the theorem statement actually transferred, the quantifiers, the decision/checking lemma, the reflection bounds, the exact test method, the negative mutation, and the report's `lean_status`. These may differ across families. In particular, frozen-menu optimality remains menu-relative; one-step flow is not multi-stage occupancy; a CQ-1 finite constitutive certificate is not automatically an Exact GR; and a policy class is not enlarged by the presence of a compiler.

**Exercise E02-A.** An application returns an exact receipt, `lean-recheck` passes, but no compiler run was provided. Report `numerical_verification = PASS`, `kernel_checked_proof = NOT_EXECUTED` (if that is the independent check's actual outcome) and **do not** call the instance Lean-verified. A separate pinned and auditable compilation is still required.

## E02.6. New research-case receipts and the unchanged application reproduction

The v1.1 additions are research declarations and verification probes. Their compiler receipts are separate from the **21 application-generated candidates** that were only emitted, byte-rechecked and tamper-tested in the v1.0 installed-wheel reproduction. A successful new research probe does not retrospectively compile those application instances.

The assembly's source/evidence ledger identifies each case's named declarations, source bytes and actual receipt state. A verification-only `.lean` probe is not included merely because `lake build PermanssonResearch` succeeds; its dedicated harness must run. Every claimed named axiom receipt must be present exactly once, the positive compile must succeed, and a semantic negative must fail on its intended mathematical assertion. Missing imports, malformed files, timeouts and resource exhaustion do not count as semantic rejection.

| Case | Source/receipt state used by this edition |
|:--|:--|
| Q-05 | Merged source and focused original-margin/whole-path replay recorded in the Tranche 7/8 packet. |
| F-01 | Merged Tranche 8 source packet: 37 named declarations and three semantic compiler controls. |
| D-09 | Merged Tranche 8 source packet: 19 named declarations and three semantic compiler controls. |
| D-08 | Merged Tranche 9 source packet: 30 named declarations and three semantic compiler controls. |
| D-06 | Merged Tranche 9 source packet: 39 named declarations and three semantic compiler controls. |
| D-05 | `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 47 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_D-05_Receipt.json` (SHA-256 prefix `d89bd1432c5a`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`). |
| B-02 | `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 65 named declarations with allowed-axiom output and 5 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_B-02_Receipt.json` (SHA-256 prefix `5b1dd829d437`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`). |
| Q-03 | `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 51 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_Q-03_Receipt.json` (SHA-256 prefix `0f60c35c1e85`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`). |
| Q-04 | `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 65 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_Q-04_Receipt.json` (SHA-256 prefix `fd2cc0cf72c7`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`). |
| M-02 | `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 29 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_M-02_Receipt.json` (SHA-256 prefix `ca5969c76844`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`). |

The complete 56-case source crosswalk in Appendix J preserves each frozen acceptance status. A direct named-source receipt establishes that the named declarations compile with their stated assumptions; it does not automatically demonstrate every prose criterion, execute every historical mutation or authenticate an independent reviewer.

### Receiptless finite-world source candidates

The general E02.2 template is for a family that accepts a receipt. The actual `finite-world` family is an exception: it binds the model alone and rejects an extra receipt argument. Its exact shape is:

```bash
permansson-app lean-emit --family finite-world request.json --output candidate
permansson-app lean-recheck --family finite-world request.json --candidate candidate
```

For the `exit` family, the model, receipt and `--region region.json` are all required. The profile command is `finite-exit`, while the source-candidate family is `exit`; the family name is not another profile command. Likewise `finite-world` is a candidate family, while `finite-kernel` is the numerical command. Both source-candidate commands still leave compiler execution to a separate replay.

**Interface verification.** This edition's accompanying interface audit checks the 26 released profile commands, the actual released CLI argument parsers, named fixture files and pinned repository links from release source `63a66c82a9ece4361f646ee13b6711192f831406`. That is source/argument validation, not a new installation or numerical execution.

# E03. Evidence, scientific reports, and independent acceptance

## E03.1. Three independent questions

A reader must answer three questions separately: *Is the result correct for its declared mathematics?* *Is the evidence genuinely tied to the relevant source, byte sequence, compiler and reviewer?* *What authority has accepted the claim or software release?* They are not consecutive values of a single Boolean flag.

The implementation enforces this separation in the following components:

- `src/permansson_app/report.py` produces the numerical **`Permansson.App.ScientificReport.v2`**.
- `src/permansson_app/reports.py` produces the assessment-only **`Permansson.App.ScientificEvidenceReport.v1`**.
- `src/permansson_app/evidence.py` and `src/permansson_app/replay.py` implement strict, externally pinned evidence checks; `src/permansson_app/acceptance.py` makes selected-scope acceptance assessments without issuing release authorization.

Do not merge the `scientific_certificate_dimensions` dictionaries of the two report versions. They are **different contracts**. In `ScientificReport.v2`, nine scientific certificate dimensions from the legacy vocabulary are all `null` unless externally assessed. In `ScientificEvidenceReport.v1`, nine evidence-index axes (`scope`, `source`, `model`, `premises`, `numeric`, `lean`, `independent_review`, `empirical`, `publication`) use explicit states such as `UNASSESSED`, `SUPPORTED`, and `BLOCKED`. Even nine `SUPPORTED` assessment axes do not issue authorization.

## E03.2. What the ordinary numeric report really says

`numeric_application_report()` requires a valid model semantic identity, actual computation receipt, and a successful *profile-appropriate* independent checker status. It records hashes of canonical receipt and checker bytes, then emits these distinct fields:

| Report key | Meaningful default in `ScientificReport.v2` |
|---|---|
| `mathematical_implementation` | `NUMERIC_ONLY` |
| `numerical_verification` | Specific independently verified result status |
| `kernel_checked_proof` | `NOT_EXECUTED` |
| `independent_mathematical_certification` | `NOT_ASSESSED` |
| `application_release_acceptance` | `NOT_ASSESSED` |
| `empirical_identification` | `NOT_IDENTIFIED` |
| `publication_approval` | `NOT_ASSESSED` |
| `scientific_claims_verified` | `false` |
| `scientific_certificate_dimensions` | Nine `null` entries |

This is **not a degraded report**. It is a well-scoped report that declines to claim results absent from its evidence chain. A numeric run can be successful even though none of the higher-level scientific gates has been assessed.

## E03.3. Independent pins and evidence records

The versioned `Permansson.App.EvidenceRecord.v1` contains an exact source commit, source tree, subject digest, capability, execution profile, platform, method IDs, status, artifact digest, producer and optionally reviewer. `EvidenceSet.from_external_hashes()` requires a consumer-owned mapping of record IDs to trusted digests; it rejects missing or extra records, duplicate IDs and mismatched hashes. A self-contained untrusted bundle cannot manufacture independent authorization by including its own expected hashes.

The `ReplayTarget` additionally binds the emitted Lean source digest, theorem-type digest, declaration name, and toolchain. `evaluate_replay()` requires three distinct attested records: `lean_compiler`, `axiom_audit`, and `negative_mutation`, all agreeing on the same canonical transcript and source. It accepts only zero compiler/audit exits and permitted axiom names. Its successful status is deliberately **`INSTANCE_COMPILER_EVIDENCE_MATCHED_REVIEW_REQUIRED`**, not `CERTIFIED`.

That assessment **does not run Lean** and does not authenticate the origin of the independent pins. It asks a consumer to bring already-authenticated evidence and checks strict binding relationships within it. Separate trust in the pin channel remains necessary.

## E03.4. Concrete consumer assessment interfaces

The implemented read-only CLI is `python -m permansson_app.governance_cli` and its exact subcommands are:

```text
claims-list --output NEW_DIR
provenance-check graph.json --output NEW_DIR
domain-import archive.zip --case CASE [--cutoff AWARE_TIMESTAMP] --output NEW_DIR
release-assess target.json evidence.json \
    external_pins.json policy.json --output NEW_DIR
replay-assess target.json transcript.json evidence.json \
    external_pins.json --output NEW_DIR
```

These are typed validation/assessment entry points. Do not call their `PASS`/success responses a remote compiler run, an accepted theorem, or a publication approval. `release-assess` checks evidence completeness under a specified policy. It does not approve a release; an independently governed activation channel is required.

## E03.5. Conditional status, not automatic promotion

The finite numeric application and historical Application Standard are different. The latter's `validity` and orthogonal certificate vocabulary belongs to its own draft v0.1.0 schema. The successor's numeric and evidence-index reports use their own version tags. None automatically transforms into the other. E08 provides the formal comparison.

**Exercise E03-A.** Someone attaches three `PASS` evidence records, sets `scientific_claims_verified = true`, and includes expected hashes generated by the same untrusted archive. Reject the conclusion. The records lack independently pinned authentication; and editing a report status does not execute the evidentiary gates or grant certification.

## E03.6. The 56-case status register remains a separate record

The new edition integrates stronger source results and more precise replay evidence without altering the frozen decision register:

| Register | Frozen disposition | Count |
|:--|:--|--:|
| Original cases | `PENDING` | 15 |
| Original cases | `PARTIAL_SCOPE` | 30 |
| Later claims | `SOURCE_PRESENT_REVIEW_PENDING` | 11 |
| Total | Separate cases/claims | 56 |

These categories describe the preserved acceptance record. They are not counts of missing theorems. For example, Q-05 now has original canonical output and full-comparison margin identities; M-02 has actual marked-history source fixtures; F-05 has a positive-support mediation witness; and X-04 has a tied-start domain fixture. Earlier absence descriptions are superseded to those precise extents by the later sources and their dated addenda.

Conversely, a compiled narrower statement does not automatically satisfy a broader frozen criterion. Appendix J records the original criterion, source routes, scoped progress and remaining review boundary for every entry. Internal source review, an autonomous agent's review and owner-controlled CI are not independent scholarly case-acceptance decisions. The edition records no invented reviewer identity, signature or acceptance promotion.

# E04. Case-artifact intake, chronology and provenance

## E04.1. An evidence inventory is not a model fit

The repository already has six source-specific evidence-profile definitions in `src/permansson_app/domain/registry.py`, not one universal spreadsheet importer. They are wired through `domain/importer.py` and the bounded ZIP indexer `domain/bundle.py`. The supported profile keys are `russia_ukraine`, `hormuz`, `iran`, `midr`, `brown_mackay`, and `cross_conflict`. The adapter recognizes release-local artifact names. It does not create new transition-law probabilities or replace one companion's evidence conventions with another's.

A useful teaching pipeline therefore has three separately recorded stages:

$$
\begin{aligned}
\text{Source archive bytes} &\longrightarrow
\text{checked artifact inventory}\\
&\longrightarrow\text{reviewed observation set}.
\end{aligned}
$$

A fourth operation, **causal parameter identification**, is distinct research and **is not implemented by this importer**. The guide does not require that operation for conditional calculation from already-declared mathematical inputs. It simply prevents an evidence inventory from being mislabeled a fitted generator.

The six case inventories are as follows. These are evidence categories, not operational recommendations:

| Key | Required release-local artifact family | The importer does *not* conclude |
|---|---|---|
| `russia_ukraine` | Frozen analysis spec, event ledger, weekly state ledger, daily hindcast transitions | That weekly coded states are calibrated causal $\alpha/P/U$ parameters |
| `hormuz` | Frozen spec, event ledger, weekly modeled output | That descriptive histories are prospective predictions |
| `iran` | Final structured update, typed measurements, successor summary | That a counterfactual simulation equals observed transition dynamics |
| `midr` | Release spec, support/gain matrix, transition semantics, claim ledger | That dependency weights are transition probabilities |
| `brown_mackay` | Frozen spec, primary results, independent check, gate results | That a specialized report imports into universal GR/PR certification |
| `cross_conflict` | Geometry summary, weekly geometry matrix, refined synchronization episodes | That correlation, lag, or local geometry establishes causation |

These names and required suffixes are defined in the source [domain registry](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/src/permansson_app/domain/registry.py), not inferred from filenames in a manuscript. The overview [DOMAIN_IMPORTS.md](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/DOMAIN_IMPORTS.md) explains the public contract.

## E04.2. Read-only ZIP safety is part of scientific reproducibility

The source bundle reader limits archive member count, expanded bytes, per-member bytes and compression ratio; it validates member paths, duplicate/case-insensitive filename collisions, symlink policy and SHA-256 member digests. The importer inspects specifically selected CSV or JSON files and assigns a role. It **does not execute** code, notebooks, HTML, Lean, or scripts contained in the archive. The selected tabular files are limited to 2 MiB for parsing; larger members may still be represented by hashes but are not silently parsed as full datasets.

This is a scientific integrity rule as well as a software-security rule: two readers must not silently choose different copies of a duplicate source path or depend on executable analysis scripts that were not reviewed as data. If multiple members match one required suffix, the importer raises an ambiguity error instead of choosing one.

## E04.3. Chronology: event time is not observation availability

The domain clock module `src/permansson_app/domain/clock.py` distinguishes `event_at` from `known_at`, together with chronology lanes `retrospective`, `hindcast`, and `prospective`. A prospective observation additionally needs a frozen specification and evaluation start. A cutoff may include a record only if its `known_at` timestamp is parseable, timezone-aware, and not later than the cutoff.

The conservative rule is

$$
\operatorname{available}_t(r)=1 \quad\text{only when}\quad
\operatorname{knownAt}(r)\le t
$$

with sufficient timestamp metadata. It is **not** appropriate to replace missing `known_at` with `event_at`, publication date, file creation time, or today's date. Those are different clocks.

In the source-provided Russia–Ukraine companion, the event file uses date-only `known_at` values such as `2013-11-21`. The generic successor importer requires a timezone-aware instant. Under an explicit cutoff, the earlier audit found all 328 rows unresolved on that field. This does not mean the companion's own analysis is invalid. It means a **case-specific timestamp translation has not been implemented in the generic adapter**. Report the unresolved count; do not normalize it without defining the source's date convention and time zone.

## E04.4. Run a source-only import

```bash
python -m permansson_app.governance_cli domain-import \
  /path/to/a/known-companion.zip \
  --case brown_mackay \
  --output /tmp/permansson-e-domain
cat /tmp/permansson-e-domain/domain_import.json
```

Choose a fresh output path that does not already exist; the command creates the directory. Use an archive already known to match the corresponding profile. The example is an **inventory inspection**, not a request to run methods contained inside the ZIP. The expected complete-bundle status is `EVIDENCE_ONLY_NOT_CAUSALLY_IDENTIFIED`. Incomplete bundles are labeled `INCOMPLETE_EVIDENCE_BUNDLE`. The importer returns `causal_alpha_P_U_identified = false` and `empirical_exact_GR_PR_certified = false`.

## E04.5. Provenance graphs and frozen information

The separate `governance_cli provenance-check` accepts a versioned `Permansson.App.ProvenanceGraph.v1` with exactly `format`, `nodes`, `cutoff`, and `evaluation_start`, then delegates to `src/permansson_app/provenance.py`. A successful graph consistency check tells the reader about declared chronology and source dependencies; it does not authenticate a source organization or prove an empirical effect.

**Exercise E04-A.** A retrospective event occurred on June 1, was first available to analysts on June 9, and the frozen evaluation cutoff is June 5. Is it a permissible pre-cutoff information input? **Answer:** no. By the declared `known_at` clock, June 9 is later than June 5 even though `event_at` is earlier.

# E05. Federation, detached integrity, and release boundaries

## E05.1. Three meanings of the word 'source'

A repository Git commit identifies a tracked tree; a detached file hash identifies bytes; a distribution tag identifies a published package release. None of these alone establishes that an untrusted sender is authorized to speak for an organization. The source pin in `src/permansson_app/versioning.py` has exactly `repository`, `commit`, `tree`, `application`, `research`, and `paper`. It rejects malformed hashes or an unknown repository string. As its docstring notes, syntactically valid source hashes are **not authenticated source identities**.

The versioning profile deliberately keeps the frozen v0.1.8 theory, the current research library, and the published application version separate. It is unsound to rewrite all three versions as “v0.2.0” simply because both a research companion and a numeric application have releases containing that number.

## E05.2. A read-only federation contract is not a live provider

`src/permansson_app/federation/` has four substantive modules:

| Module | Implemented responsibility |
|---|---|
| `contracts.py` | Typed source/capability/mode/subject/artifact contract |
| `compatibility.py` | Compare exact contract against **consumer-owned** expectations and capability allowlist |
| `exchange.py` | Verify detached manifest, exact file list, source and artifact digests |
| `local_engine.py` | Scope-limited read-only metadata operations |

The mode separates numeric from evidence-only exchanges. A compatible exchange cannot expand the consumer's capability allowance, cause remote code execution, or turn a numeric receipt into a compiled theorem. The [federation contract documentation](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/FEDERATION_CONTRACT.md) explicitly states that these are local contracts, **not an active connection to an external intelligence or data provider**.

## E05.3. Detached bundle verification

The bundle interface in `src/permansson_app/bundle.py` uses `Permansson.App.DetachedBundleManifest.v1`. A consumer can independently verify an exact inventory against a separately trusted SHA-256 of the manifest. Boundedness is part of the contract: at most 128 files, 4 MiB per file, and 32 MiB aggregate bytes; path traversal, symlinked inputs, missing/extra files and altered bytes fail closed.

A detached bundle verification can return `HASH_INTEGRITY_VERIFIED`, with `origin_authenticated = false` and `mathematical_claims_verified = false`. These are not inconsistent: byte integrity under an independently supplied manifest hash is not an authenticated publishing identity.

An instructive demonstration of this boundary is possible with one local text file (no domain or military data required): create a detached manifest from the file using `create_detached_manifest()`, obtain its digest using `canonical_bytes()`, and verify it with `verify_detached_bundle()`. Change one byte and run the verifier again: a correctly implemented checker must reject the mismatch. The accompanying QA script tests precisely this read-only behavior using a fictional note.

## E05.4. The numeric release is narrower than the repository

The released successor distribution is `permansson-application-successor-recovery` **0.2.0**, tag [`permansson-app-v0.2.0`](https://github.com/HMarcusWH/PermanssonLean/releases/tag/permansson-app-v0.2.0), built from `63a66c82a9ece4361f646ee13b6711192f831406`. Its selected release scope is **26 exact finite numeric profiles**, for Linux CPython **3.12** and **3.13**. Native C10/C11 tools, instance Lean replay, Windows/macOS, and scientific/empirical claim acceptance are **not** covered by this selected release policy. They may have other source tests, but they do not inherit the published numeric-release status.

The release used an owner-dispatched workflow, governed by `OWNER_ENGINEERING_POLICY`, not a claim of independent security review. The tag published a wheel, source distribution, `release-manifest.json`, and `SHA256SUMS`; see [`RELEASE_ACCEPTANCE.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md). The document records the GitHub release run **41313849870**, two installed-distribution qualification platforms, and **260 selected evidence records** (26 capabilities × five evidence categories × two platforms).

A reviewer must not substitute a later `main` test success for evidence about earlier release assets. Conversely, the released tag does not replace a later `main` source audit. The guide cites both exact identities.

## E05.5. Published release versus general acceptance

The release gate in `verification/application_successor/release_gate.py` binds the owner dispatch, exact source, build and qualification outputs, and downloaded GitHub artifact hashes. The generic `release-assess` interface validates selected evidence against a policy but does **not** activate or authorize a release on its own. The published release is an observed fact of the owner-controlled workflow; it is not a scientific certification of all repository mathematics.

**Exercise E05-A.** A transfer bundle has a matching internal hash and a green source-build indicator. May a consumer call its origin authenticated? **Answer:** no, not without an independently trusted hash/origin channel and the applicable source policy. Hash agreement inside the same bundle is self-referential.

# E06. Verification workflows and adversarial test design

## E06.1. The verification stack is layered

Use [`verification/README.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/verification/README.md) as the general index, then the successor's reviewer guide for its specific tests. The repository has separate systems for the original Application Standard, research Lean, original Lean, executable destructive regressions, repository integrity, source-bound bridge replay, installed distributions, and release metadata. They test **different assertions**.

| Layer | Implemented entry point | Result you may infer |
|---|---|---|
| Original theorem source | `lake build` plus original Lean CI | Original declarations compile on the pinned toolchain |
| Research theorem source | `lake build PermanssonResearch` plus Research Lean CI | Research declarations and bridge modules compile at that head |
| Original Application Standard | `verification/application_gate.py`; `application/tests/` | Draft contract structural rules and fixtures are consistent |
| Destructive regression | `verification/destructive/suite/run_all.py` | Selected numerical/destructive cases pass |
| Repository synchronization | `verification/repository_gate.py` | Committed source, artifacts, hashes and specified imports meet the gate |
| Numeric application | `apps/permansson/application-successor/tests/`; `scripts/end_to_end.py` | Registered profile example runs, receipt checks, source-bound candidate behavior |
| Research instance replay | `verification/research/test_application_*_live_lean.py` | Specific reflected candidate instances compile and mutations fail as specified |
| Numeric release | `verification/application_successor/` | Selected release policy, installed-distribution behavior and artifact identity |

A failed layer must not be hidden by an unrelated passing layer. A research theorem build cannot replace a numerical receipt check. A reporter cannot use the Linux release's verified wheel hash or release qualification as proof that arbitrary user-provided inputs are physically accurate.

## E06.2. Reproducing the actual source tests

From the frozen root checkout, the source guide specifies:

```bash
lake build
lake build PermanssonResearch
python -B -m unittest discover \
  -s apps/permansson/application-successor/tests
python apps/permansson/application-successor/scripts/end_to_end.py --lean
python apps/permansson/application-successor/scripts/inventory.py --check
python verification/repository_gate.py
```

The `--lean` walkthrough requires a working pinned Lean toolchain. Without that toolchain, use the numeric walkthrough and cite an actual exact-head GitHub Research Lean workflow separately; **do not** report a fresh local Lean build. The installed-wheel test is also different from invoking source code in place; `end_to_end.py --app /path/to/venv/bin/permansson-app` records and checks the installed import location.

The original v0.1.8 destructive suite lives under `verification/destructive/suite/`, with named runs 17–30. Its historical aggregate check counts are archived evidence, not a claim that the current author reran those checks during manuscript production. The older `Run 34` artifact/package verification is also separate from ordinary repository gate execution.

## E06.3. Historical v1.0 CI is bound to its source SHA

At the frozen `main` commit `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`, all six recorded core workflows succeeded:

- Original Lean: [run 41321594907](https://github.com/HMarcusWH/PermanssonLean/actions/runs/41321594907)
- Research Lean: [run 41321594868](https://github.com/HMarcusWH/PermanssonLean/actions/runs/41321594868)
- Executable verification: [run 41321594951](https://github.com/HMarcusWH/PermanssonLean/actions/runs/41321594951)
- Application contract: [run 41321594921](https://github.com/HMarcusWH/PermanssonLean/actions/runs/41321594921)
- Research integrity: [run 41321594885](https://github.com/HMarcusWH/PermanssonLean/actions/runs/41321594885)
- Integrity portability: [run 41321594901](https://github.com/HMarcusWH/PermanssonLean/actions/runs/41321594901)

These refer to the exact commit, not to a hypothetical later head. The prior verification audit accounts for **784 tracked `.lean` files** through the two library-root builds, seven separately compiled witness tests, and one repository import-list snapshot checked as synchronization evidence. This is verified compilation coverage, **not** an assertion that every speculative or manuscript-level proposition has a formal theorem.

## E06.4. Negative mutation and failure localization

Negative tests must change an actual semantic premise — e.g., a model row, declared value, policy class, constraint, objective, or typed intervention — and demonstrate that the intended theorem fails. Merely creating a syntax error proves less. The live Lean bridge tests therefore require a targeted theorem failure and reject unrelated compiler errors. The application also tests tampered receipts, extra fields, disallowed model sizes, unsafe paths and budget violations.

To substantiate source-to-theorem binding, retain both a positive witness and a relevant semantic negative control. An example that succeeds even after an adversarially changed theorem statement would not establish the intended source-to-theorem binding.

## E06.5. How to report incomplete checks

An interrupted command is `NOT_COMPLETED`, not passed. A skipped test may be acceptable only when the selected policy allows it; otherwise it is missing coverage. A time-limited search that cannot produce an optimum certificate does not establish infeasibility. A local candidate source recheck without Lean is `SOURCE_RECHECK_PASS`, not `COMPILED`. A successful Research Lean library build is `LIBRARY_COMPILED_AT_SHA`, not `APPLICATION_INSTANCE_AUTHENTICATED`.

**Exercise E06-A.** A source-run walkthrough passes 25 profiles, while the released `lp-check` is only reached by passing the certificate extracted from `lp-propose`. Must the audit include that consumer path? **Answer:** yes. The repository's exact 26-command registry distinguishes the certificate-producing and certificate-consuming commands. The pre-PDF audit separately tested the `lp-propose` → extracted receipt → `lp-check` route with an invalid certificate rejection.

## E06.6. Replay status for this additive edition

The six workflows and 784-file coverage count in E06.3 describe the historical v1.0 baseline `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`. The original application release, the Tranche 8/9 merged source and the Tranche 10 source additions have their own identities. A later receipt is reported only for the source bytes and commit it actually checked.

**Latest added-source commit:** `23e6a57b381363cf20751a18337ca927cd393a6c`; tree `e3211713f1ef508ea891f534509116accaad56a4`.

**CI/integration state supplied for this edition:** PR126 passed all six workflows and all nine check runs. Research run 44639175231 passed 2,260 tests in 2,998.737 seconds. GitHub checked synthetic merge e1adca3ae51ea5e220573171ef5ef53a7c6c3654 against base 4d2f0367a37e47c3c4f10fb17baad575521c6f11. PR126 merged as c5a36cd6189e2a249d5f4bc11f31698917dc8b10 on 20 November 2026 at 01:50 Europe/Stockholm. Candidate, synthetic test merge and actual merge share tree e3211713f1ef508ea891f534509116accaad56a4. The separate clean committed local replay passed eight tests in 94.745 seconds with unchanged inputs and clean worktrees. The newly triggered postmerge workflows are recorded separately; they were queued at the initial merge observation.

The five focused packets each passed clean local replay and authenticated PR126 CI, retaining 257 named declaration occurrences (256 distinct names) and 17 semantic controls. The separate all-56 packet retains 136 distinct names, 139 case-owned occurrences, 77 provider artifacts and 167 source/meta pins, and executes zero semantic controls itself. All 23 new CI compiler-stage hashes and their allowed-axiom output were verified. The internal clause review, supplementary E-04 local Lean controls and C11-02 local Python checker control have separately identified records. None is an independent case-acceptance decision.

**All-56 named-source receipt:** CI_AND_CLEAN_COMMITTED_NAMED_SOURCE_REPLAY_PASS. All 56 frozen entries have selected named-source coverage in both clean committed replay and authenticated PR126 CI: 136 distinct declarations, 139 case-owned route occurrences, 77 provider artifacts and 167 source/meta pins. This direct packet executed zero semantic controls. Internal clause inspection, criterion-specific controls and independent acceptance are separately recorded. Receipt: `PR126_Tranche10_All56_Receipt.json` (SHA-256 prefix `cf69c15c398d`). Receipt: `PR126_Completed_CI_Verification.json` (SHA-256 prefix `ee1d3e0d92b9`). Receipt: `Tranche10_All56_Clean_Receipt.json` (SHA-256 prefix `b49c6683a7ee`).

The focused Tranche 8 replay covered 37 F-01 names and 19 D-09 names with six semantic controls. Tranche 9 covered 30 D-08 names and 39 D-06 names with six semantic controls. These are distinct case packets, not a running total of all project theorems. Appendix J and the accompanying JSON retain the mapping to original criteria.

The following focused reproduction entry points are identified by the source/evidence record. Run them from the identified checkout with its unchanged toolchain and dependency manifest. The receipt states above identify what was actually executed; listing a command here does not itself assert its success.

```bash
python3 -m unittest verification.research.test_cert_tranche10_five_case_scope_addendum -v
python3 -m unittest verification.research.test_cert_tranche10_all56_named_sources -v
```

A source-context artifact identifies the checkout and job context; the compiler transcript identifies the actual declaration checks. Both matter when a CI result is asserted. Preserve the PR head, any synthetic test merge, actual merged commit and tree identity separately. A missing PR-only C10 artifact on a main push is not a missing result for an unrelated case probe.

# E07. Historical releases, archives, and provenance

## E07.1. Release objects are not interchangeable

The repository contains several preserved lineages and independently versioned outputs. Their identities and scopes must not be collapsed into the newest application version.

| Object | Primary source | Intended role | Important boundary |
|---|---|---|---|
| Original theory v0.1.8 | `paper/`, `PermanssonLean/`, `provenance/v0.1.8/` | Frozen mathematical exposition and corresponding formal source | Later research amendments do not retroactively change this release |
| Research companion v0.2.0 | `release/v0.2.0/` | Versioned manuscript, theorem map and reviewed research evidence | Different release from numeric app 0.2.0 |
| Archival supplement | `archival/v0.2.0/` | Captured Git ancestry, original artifacts, reviews and offline reproduction materials | Adds provenance, not additional theorems |
| Mathematical closure candidate | `release/mathematical-closure-1/`, `research_papers/mathematical_closure/` | Draft claims, seal preparation and controlled reproduction process | The included README labels it **DRAFT / NOT ACCEPTED / NOT PUBLISHED** |
| Numeric application 0.2.0 | `apps/permansson/application-successor/`, release tag `permansson-app-v0.2.0` | Qualified installed finite-numeric distribution | Owner engineering release, not independent certification |

An archive may record an accepted historical source, a later maintenance commit, and a newly built supplement within the same repository checkout. Always identify the **specific object**, its bytes, source SHA and acceptance scope before describing it as accepted or released.

## E07.2. Research companion: statement-level provenance

The research release in [`release/v0.2.0/README.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/release/v0.2.0/README.md) has its own `manuscript.json`, generated PDF/TeX, `theorem-map.json`, review evidence, and acceptance logic. The builder's draft mode can express pending claims; the final mode enforces a reviewed policy with 17 claim anchors and explicit open boundaries. One may cite a proved source-qualified statement, an assumption-scoped theorem, or an `OPEN` boundary; one must **not** make every item in the integration specification sound completed.

The research companion's PDF and TeX are output representations of a structured manuscript. The build checks metadata and content against a frozen policy; human page-level visual review is an additional publishing responsibility. Neither a rendered PDF nor an arbitrary new PDF of this guide is itself a formal proof.

## E07.3. Archival supplement and Git history

The archival directory contains `history.bundle`, `objects.jsonl`, `refs.json`, source receipts, an archive manifest, and `OFFLINE_REPRODUCTION.md`. This preserves independently inspectable historical Git objects, source receipts and review captures for the accepted v0.2.0 research lineage. The source [`archival/v0.2.0/README.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/archival/v0.2.0/README.md) distinguishes **historical release objects** from subsequent preservation tooling. The accepted historical release SHA named there is `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618`; this is not the current `main` head or the numeric application's release tag.

To audit an archive, work from the original immutable bytes. Verify the manifest, source object inventory, actual Git bundle, expected refs, recorded evidence captures and the tools' own source snapshot. A successful reproduction of archived objects confirms continuity of that evidence chain; it does not independently endorse every scientific conclusion in the documents.

The companion's `publication-candidate/` ZIP and accompanying SHA sidecar are historical transport artifacts, not a place to insert new paper claims. If a new guide supplements them, it needs its own version and manifest rather than modifying old archival bytes.

## E07.4. Mathematical closure has a stronger, still-open acceptance contract

[`release/mathematical-closure-1/README.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/release/mathematical-closure-1/README.md) states that the full mathematical-closure release candidate is not accepted or published. Its procedure distinguishes postmerge pre-seal reproduction, candidate ZIP seal, independently authenticated post-seal archive replay and release readiness. It explicitly rejects promotion from a locally fabricated ZIP, synthetic log, or improperly authenticated GitHub run.

That status is compatible with **many accepted Lean theorems elsewhere in the repository**. A full 45-original-case/11-later-claim certification umbrella is a separate review contract. The guide may explain those research claims with their actual hypotheses, but it must not call the umbrella complete merely because the checked library compiles.

## E07.5. V0.1.8 paper-provenance hashes

`provenance/v0.1.8/` contains named SHA records for the paper PDF, TeX source, portable test suite and release ZIP, plus a build audit. Each is a distinct object and a distinct assertion. The original PDF's hash verifies that a file is identical to the specified byte sequence; it does not identify the latest live source automatically. See [`provenance/README.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/provenance/README.md).

## E07.6. A reader's provenance record

For every result cited in the guide, preserve at least these fields (some are `null` when inapplicable):

```text
object_kind: formal theorem | numerical calculation | archived paper | release asset
repository: HMarcusWH/PermanssonLean
commit: exact Git SHA
source_tree: exact Git tree SHA
source_path: file or theorem declaration
release_tag: exact tag, if published
artifact_sha256: original exact bytes
verification_method: actual tool/test/workflow
verification_run: actual job or local log path
statement_scope: quantifiers, horizon, information and model class
acceptance_status: exact selected policy/status, not a generic PASS
open_boundaries: what the record does not show
```

**Exercise E07-A.** A document labeled `v0.2.0` is cited. Is that sufficient to determine whether it came from the research companion or numeric application? **Answer:** no. Require the repo path, commit/tag, manifest and artifact digest. These release tracks share a version string but not an acceptance policy.

## E07.7. Additive edition provenance

The original v1.0 source, its installed-release evidence and the Tranche 8/9 integration addenda remain historical artifacts. The preserved v1.1 manuscript was assembled from their pinned bytes plus identified new inserts; its builder records those input hashes and source objects. The v1.1.1 editorial edition is derived from that manuscript through a separate assertion-guarded change ledger. The source-history ledger in A03.1 distinguishes published PR heads from actual merged commits. An agent's internal review is a source/editorial activity and is not an independent acceptance signature.

# E08. Legacy Application Standard versus successor contracts

## E08.1. The original draft standard is a semantic application contract

The original [`application/APPLICATION_STANDARD.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/application/APPLICATION_STANDARD.md) declares **Permansson Application Standard 0.1.0**, status `DRAFT`, compatible with theory v0.1.8, and scope `APPLICATION_CONTRACT_NOT_THEOREM_EXTENSION`. It is a structured specification for submitted applications and their supporting artifacts. It is **not** an earlier version of the successor's exact-rational runtime that can accept the same CLI request unchanged.

A complete legacy bundle names `application.json`, referenced content-hashed artifacts, regime assertions, semantic pipeline, frozen intervention protocols, provenance graph, identified-set report, and an application certificate. Five domain schemas (`application_certificate`, `semantic_pipeline`, `intervention_protocol`, `provenance_graph`, `identified_set`) combine with common and envelope schemas. Structural JSON Schema validation is only one stage; the application validator additionally checks cross-object consistency.

The legacy validator can be run from the repository root:

```bash
python -m pip install -r application/requirements.txt
python application/validator/validate_application.py \
  application/examples/grounded_pr_minimal/application.json --json
```

For this synthetic source fixture, the documented expected output includes `contract_valid = true` and `scientific_claims_verified = false`. The validator does not execute the cited mathematical argument, estimate data, authenticate a historical registration, or certify a submitted PR theorem.

## E08.2. The original frozen pipeline digest

The `PERMANSSON_PIPELINE_V1` identifier binds a defined payload: the theory and standard version, a semantic pipeline object (excluding specific receipt fields), the ordered intervention family minus declared assessment annotations, and the sorted map of referenced artifact IDs to byte hashes. Its serialization uses a specifically versioned Python `json.dumps(...)` convention with sorted keys, ASCII escaping and compact separators. **It is not RFC 8785/JCS.**

This is deliberately different from the successor's `TypedRationalJCS.v1` semantic identity and optional `Permansson.App.SemanticsJCS.v1` digest implementation. In particular, the optional semantics digest is not silently retrofitted into all old receipts and bundles. `docs/SEMANTIC_DIGEST_PROFILE.md` states that the profile is available without switching existing identities.

Hash stability is not legal or chronological registration. The source explicitly notes that **a hash is not an authentic timestamp**. A changed pipeline's inputs require a new identifier and a new interpretation of the freeze/selection history, not a revised old certificate with the same printed ID.

## E08.3. Orthogonal certificate tuple: explicit legacy values

The original standard's nine fields use the following vocabulary:

| Dimension | Examples of permitted values | What structural validation does *not* imply |
|---|---|---|
| `validity` | `VALID`, `INVALID` | Valid certificate assertions from validator success |
| `epistemic_mode` | `FORMAL_THEORETICAL`, `EMPIRICAL_CONFIRMATORY`, `ASSUMPTION_CONDITIONAL`, `EMPIRICAL_EXPLORATORY` | Transfer among epistemic modes |
| `selection_status` | `FROZEN_REGISTERED`, `HELD_OUT_OR_SELECTION_ADJUSTED`, `POST_HOC_EXPLORATORY` | An authenticated freeze date |
| `identification_status` | `POINT_IDENTIFIED`, `SET_IDENTIFIED`, `STRUCTURALLY_UNRESOLVED` | Causal identification |
| `statistical_status` | `NOT_APPLICABLE`, `RESOLVED_AT_DECLARED_COVERAGE`, `STATISTICALLY_UNRESOLVED` | Quantified coverage automatically |
| `provenance_status` | `SUPPORTED`, `INSUFFICIENT`, `NOT_APPLICABLE` | Authenticated external source identity |
| `substantive_pr_status` | `ROBUST_PR`, `ROBUST_NONCONSTITUTIVE_UNDER_FROZEN_PROTOCOL`, `PR_STATUS_AMBIGUOUS`, `NOT_EVALUATED` | A universal PR or no-PR theorem |
| `direction_status` | `POSITIVE`, `NEGATIVE`, `DIRECTION_AMBIGUOUS`, `NOT_APPLICABLE` | A universal signed difference |
| `uniform_gap_status` | `ESTABLISHED`, `UNRESOLVED`, `NOT_APPLICABLE` | A common positive margin from a pointwise difference |

The important point is not the list of words itself, but **who has grounds to assert them**. The validator permits a structurally valid document to say `validity = INVALID`, or that an identified-set analysis is unresolved. It does not convert `contract_valid` into `validity = VALID`, `ROBUST_PR`, or `ESTABLISHED`.

## E08.4. Why the two application contracts must remain separate

| Contract | Input | Primary result | Scientific promotion |
|---|---|---|---|
| Legacy Application Standard v0.1.0 | `application.json` plus scoped artifacts and protocols | Structural/semantic validation and reporting tuple | None by validation alone |
| Successor exact numeric application v0.2.0 | Strict versioned finite-profile input, exact rational rows | Numeric receipt, independent check, `ScientificReport.v2` | None by numeric check alone |
| Successor evidence assessment | Consumer-owned source pin, expected evidence digest map, policy/replay target | `ScientificEvidenceReport.v1` or typed assessment status | None by mere presence of `SUPPORTED` evidence axes |

A migration, if ever needed, requires an explicit translation specification: what typed state/feasibility, primitive slots, initial laws, property functional and frozen protocol mean; what cannot be represented in the finite numeric engine; and which certificate dimensions remain not assessed. The current guide **does not claim a universal legacy-to-successor importer**.

## E08.5. Close the evidence loop without overstating it

A fully auditable *conditional* calculation can now be organized into seven source-linked records:

1. A precise question with explicit mathematical event or functional and quantifier scope.
2. A checked input schema and semantic identity, with assumed rather than inferred model primitives labeled.
3. An exact engine receipt with its declared status and resource limits.
4. A separate independent check or certificate verification.
5. An optional source-bound Lean candidate, byte-rechecked against the original input and receipt.
6. A separately executed pinned Lean instance, where within reflection bounds, with axiom audit and an authenticated evidence record if such authentication exists.
7. A report preserving numeric, theorem, review, release, data identification, and publication statuses **without automatic promotion**.

That loop is the verification architecture for the mathematical tutorial. It does not require an empirical project to have been completed before a finite model is computed; it requires the authors to say which conclusions are conditional on declared assumptions. The reader should be able to inspect the exact paths and claims that support each line in the result.

**Exercise E08-A.** A legacy `grounded_pr_minimal` fixture passes the draft structural validator. Can it be supplied unchanged to the successor's `finite-cq1` CLI and reported as a Lean-proved, real-world PR? **Answer:** no on all counts. The accepted input contracts differ; the old structural validator proves neither a finite CQ-1 instance nor external identification; Lean proof requires its own correctly typed instance and separate check.

# Appendix E-A. Full source and trust-boundary crosswalk

The eight chapters above follow *actual source implementation ownership*. This crosswalk names the shortest defensible route for a reviewer. Directory-level references are intentional where multiple modules share the responsibility. Unprefixed paths begin at repository root. `app:` denotes `apps/permansson/application-successor/`; `pkg:` denotes its `src/permansson_app/` package directory. Each non-root path carries its own prefix.

| Chapter | Canonical source modules or documents | Verification target |
|---|---|---|
| E01 | `pkg:engines/`, `pkg:receipts/`, `pkg:report.py`, `app:docs/EVIDENCE_AND_RECEIPTS.md` | Independent numeric receipt and status semantics |
| E02 | `PermanssonResearch/ApplicationBridge/`, `pkg:proof/`, `app:docs/NATIVE_PROOF_REPLAY.md` | Candidate bytes, Lean proof bounds, axiom audit, mutation tests |
| E03 | `pkg:evidence.py`, `pkg:replay.py`, `pkg:reports.py`, `pkg:report.py`, `pkg:acceptance.py`, `pkg:governance_cli.py` | Externally pinned evidence, nine-axis report and assessment-only semantics |
| E04 | `pkg:domain/registry.py`, `pkg:domain/importer.py`, `pkg:domain/clock.py`, `pkg:domain/bundle.py`, `pkg:provenance.py`, `app:docs/DOMAIN_IMPORTS.md` | Bounded ZIP, known-at scope, selected source profiles |
| E05 | `pkg:federation/`, `pkg:bundle.py`, `pkg:versioning.py`, `app:docs/FEDERATION_CONTRACT.md`, `app:docs/RELEASE_ACCEPTANCE.md`, `verification/application_successor/` | Consumer scope, offline manifest, release authority |
| E06 | `verification/README.md`, `verification/research/`, `verification/destructive/`, `verification/repository_gate.py`, `app:scripts/end_to_end.py`, `app:scripts/inventory.py`, `app:tests/` | Reproducibility and adversarial tests |
| E07 | `release/v0.2.0/`, `release/mathematical-closure-1/`, `archival/v0.2.0/`, `provenance/v0.1.8/`, `research_papers/mathematical_closure/` | Historical source identities, independent release scopes |
| E08 | `application/APPLICATION_STANDARD.md`, `application/schemas/`, `application/validator/`, `pkg:reports.py`, `pkg:report.py`, `app:docs/SEMANTIC_DIGEST_PROFILE.md` | Explicit distinction among legacy and successor contracts |

# Appendix E-B. Reviewer decision table

| Evidence observed | State the reviewer may record | State the reviewer must not infer |
|---|---|---|
| JSON schema valid | Request structurally parsable | Kernel properly represents any external system |
| Exact finite engine output | Producer's conditional rational result | Independently checked result |
| Separate receipt checker passes | Named calculation/certificate agrees | Lean instance compiled, independent scholarly acceptance |
| `lean-recheck` passes | Candidate bytes matched request and receipt | Compilation authenticated |
| Pinned Lean instance compiles and axiom audit passes | Checked declaration for literal data | Empirical model identification, publication approval |
| External pinned evidence set passes | Exact expected records match pinned bytes | Trusted reviewer identity unless channel independently authenticated |
| Generic `release-assess` succeeds | Selected assessment is complete/eligible as specified | Owner/independent activation occurred |
| Owner numeric release published | Specified distribution and platform were qualified/published | All research claims certified |
| Historical paper archived | Specified bytes and provenance preserved | Every possible proof obligation discharged |

# Appendix E-C. Source status and exercises — short answer key

**E01-A:** disagreement means no accepted independent numerical equality. **E02-A:** source binding without compilation is not instance proof. **E03-A:** self-asserted statuses and self-pinned hashes are insufficient. **E04-A:** information was unavailable by the cutoff. **E05-A:** hash integrity needs an independent origin channel. **E06-A:** a separate certificate consumer must be tested as its own registered command. **E07-A:** same version string is not the same release. **E08-A:** structural validation does not transfer between application models, much less to empirical claims.

## Preparing the final manuscript

A publication reviewer should walk backward from every bold scientific or mathematical assertion: **reported conclusion → exact theorem or numeric certificate → input semantics and assumptions → source module/declaration → source commit and artifact digest → applicable verification run**. If any link is missing, qualify the assertion rather than fill it with confidence language. A good result is allowed to be conditional, negative, unassessed, or outside a particular bridge's reflection bound. The objective of this volume is a reader who can tell those situations apart.



\newpage

# Volume F — Case Studies, Reproducibility and Research Boundaries

> **Case-study scope.** Volume F completes the guide’s case-study, exercise, and extension chapters. Its casebook is descriptive and source-critical; its exercises use synthetic service-system or repository-provided finite mathematical instances. The document is not an operational military planning manual and does not prescribe targeting, campaign optimization, strike decisions, or attack sequencing.
>
> **Source identity.** Repository: `HMarcusWH/PermanssonLean`, source at `main@89ac97cb` (full SHA and Git tree in Appendix F-C). The owner-engineering numeric application 0.2.0 was released from `63a66c8`, not from the later documentation-only checkpoint. Original source files, research theorem modules, numeric application and historical companions have distinct authorities.

# How to read Volume F

Volumes A and B define the strategic-world mathematics; C develops the reverse solver and specialized research families; D shows what the released finite application can execute; E explains independent checking, Lean source binding, evidence and release status. **This final volume is the synthesis**: which historical research artifacts can be inspected read-only, how to reproduce the released mathematical examples, what a calculation actually licenses a reader to conclude, and what would require a separate engineering or scientific project.

Use a five-part reading discipline: **(i)** the exact source/version; **(ii)** the data or declared mathematical model; **(iii)** the computed statement; **(iv)** independent check/proof status; **(v)** the boundary on interpretation. The order is as important as the content: no evidence type automatically upgrades another.

# F01. Historical evidence: a read-only casebook

## F01.1. Purpose and status of the casebook

This chapter **does not replay historical conflicts as a control policy**. It shows how to read six external research packages and how to avoid mistaking a descriptive event ledger, static exposure diagram, or calibrated simulation for a typed `StrategicWorldModel` with independently identified primitives. External PDFs and companions are project-supplied research products; they are not tracked modules in the repository Git tree. For software ingestion, consult [domain/registry.py](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/src/permansson_app/domain/registry.py) and [DOMAIN_IMPORTS.md](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/DOMAIN_IMPORTS.md).

The importer is a **read-only bounded evidence inventory**. It validates archive paths, member hashes, size limits, declared required assets and the presence of selected CSV/JSON evidence roles. It does not execute code within imported archives, replay historical companions' own calculations, create a fitted `alpha/P/U` model, prove Exact GR, or provide a causal interpretation. In this sense *imported* means *inspectable under a typed intake contract*, not *scientifically certified*.

| Case key in `domain/registry.py` | Supplied research source | What can be inspected | What must **not** be inferred |
|---|---|---|---|
| `russia_ukraine` | Russia–Ukraine v0.2.1 + FOI v0.4.1 | Event ledger, declared as-of timing, candidate-state reconstruction, hindcast and sensitivity | Identified causal `alpha/P/U`; certified Exact GR/PR; a real-time predictive or military operating rule |
| `hormuz` | Hormuz v1.1.1 | Recurrent candidate regions, source/attribution sensitivities and censoring | A certified bilateral generated regime or an identified intervention effect |
| `iran` | Iran v0.2 / January v0.1.1 | Assumption-conditional simulations, outcome definitions, calibration and negative witnesses | A validated transition forecast, an established intervention effect or a policy prescription |
| `midr` | MIDR v1.0 | Source-based industrial/economic exposure, support matrices, claim ledger and frozen topology | Transition probabilities, node-level causal elasticities, Exact GR or generalized PR |
| `brown_mackay` | Brown–MacKay v0.4 | Reproduced finite-grid mathematical case, independent computational checks and frozen claim | A theorem about the unmodified continuous market, external causal identification, or automatic transfer to v0.2.0 |
| `cross_conflict` | Cross-conflict v0.1 | Cross-case geometric descriptors, lag tests, passive-memory sensitivity and refined episodes | A common causal engine, transferable conflict dynamics, or an intervention policy |

Each row identifies a *source role*, not permission to treat an external ledger as a validated control kernel.

## F01.2. Russia–Ukraine: why a candidate state is not a certified regime

The source is *A Reproducible Stress Test of Permansson Regime Theory* (working paper v0.2.1, 13 August 2026; historical evidence cutoff 12 August 2026). It reports **328 strategic events**, **24 observability-only samples**, **76 primary direct-coercive events**, **67 deduplicated strategic episodes** under `known_at` timing, and **two explicitly sourced cross-player response links**. Those numbers belong to the source's historical audit. They are not sample sizes for identifying a physical transition kernel.

The paper's reconstructed candidate-state occupancy across **234 wartime weekly as-of evaluations** is 44.9% under its broad threshold, 32.1% central, and 17.9% strict. Those are **classifier occupancies of observed/reconstructed indices**. The paper reports that the initial 2022 full-scale invasion occurs while its bilateral candidate B classification is outside the defined region; the nominal first re-entry is 28 February but moves to 23 March under an ablation of a coded strategic-policy-response event. That is a useful methodological demonstration that **classification boundaries depend on declared code families and event admission**. It is not a counterfactual result identifying the outcome of a feasible intervention.

The paper's own formal status is explicit: **selected equilibrium NOT ESTABLISHED; structural transition kernel NOT IDENTIFIED; Exact EGR NOT ESTABLISHED; policy constitution NOT IDENTIFIED; Permansson regime NOT CERTIFIED**. A guide that recodes its weekly occupation percentage as $\Pr(E_{G\prec D,T})$ or a Bellman input without a separately declared model has changed the mathematical question.

**Reader task F01-A.** A colleague reports `central occupancy = 32.1%` and claims it is the probability that an intervention succeeds. Identify the missing bridge. **Answer:** the occupancy is a fraction of reconstructed weekly classifications, whereas a policy-value claim requires an explicit stochastic transition model, an initial law, an admissible intervention/policy class, an event or payoff and a checked evaluation. None of these is supplied by that percentage.

## F01.3. Hormuz: recurrence, observational gaps and attribution

The Hormuz empirical paper v1.1.1 documents **recurrent high-coupling configurations** with censoring and attribution ambiguities; the record cannot establish that every observational gap is a real system exit. Its formal-status table separately marks *selected equilibrium not established*, *structural transition kernel not identified*, *Exact EGR not established*, *policy constitution not identified*, and *Permansson regime not certified*. The distinction between a repeated observed state configuration and an invariant mathematical regime is precisely the distinction defined in Volume B.

**Reader task F01-B.** Can a series with repeated entries to a measured region establish the Exact-GR condition $K(B\mid y)=1$ for **every** $y\in B$? **Answer:** no. A finite, partially observed historical path does not establish an all-state invariance theorem, nor all-initial-law limiting occupation convergence.

## F01.4. MIDR: industrial/economic exposure is not the probability kernel

The MIDR v1.0 release (discovery cutoff 22 August 2026) distinguishes **causally supported broad economic mechanisms**—trade re-routing, partial recovery of access and incomplete substitution—from **structural candidates** such as a named dependency graph. The release's `ANALYSIS_STATUS.md` explicitly states that node-level causal pressure-transfer elasticities $\Gamma$, full-basin finite persistence, Exact-GR invariance/occupation and strategic constitution **are not established**. A graph edge, static share, support-score or dependency pressure estimate is not an entry $P(x'\mid s,x,a)$, and a dependency cycle is not automatically a recurrent class of a Markov chain.

A source-aware translation must state separately: the observed measurement, proposed state encoding, time step, candidate transition family, identification assumptions, and any intervention semantics. The static evidence may inform model hypotheses, but the model remains declared/assumption-conditional until another study justifies its mapping.

## F01.5. Iran: simulation output is conditional on its parameter family

The October 3, 2026 paper *Breaking the Persistence Loop* reports a replicated January counterfactual, a frozen Hormuz replay and a separately declared model with nine state variables. In the replicated January model, it reports **56,752 accepted parameterizations from 100,000 draws** and a **51.9929%** corridor frequency for one stated configuration. The paper also gives an inactive-channel identification counterargument and a projected-path **zero-effect witness** that defeats a proposed positive common constitutive margin. These are statements about explicitly bounded hypothetical and measured components, not a universal political-transition theorem.

The paper expressly differentiates finite simulated persistence, a named corridor, political survival, and actual causal identification. The guide should use the **negative result** as an important teaching example: a parameter family containing a zero-effect member cannot support a strictly positive *uniform* effect over the whole declared family. It can still contain positive-effect instances. This is an abstract quantifier lesson, not operational advice about real actors.

**Reader task F01-C.** A model family includes one member with $\Delta_{\psi,J}(y)=0$ on its declared comparison set. Can the common lower bound $\inf_{m,y}\Delta_{\psi,J}^{(m)}(y)$ be strictly positive? **Answer:** no, provided that member is included in the infimum. This does not rule out positive differences in other family members.

## F01.6. Brown–MacKay and cross-conflict geometry: two different limits

The Brown–MacKay companion's `README.md` labels `BM-FG-TURN-0.005-v0.4` **certified under PRT v1.2.2 for its frozen finite-grid turn-based instantiation**, with a separate computational checker, sensitivity tables and source hashes. That certification is *package-specific*. It neither establishes a theorem for the original continuous-action Brown–MacKay economy nor means that the successor application's own `ScientificReport.v2` has a Lean-checked empirical model.

The cross-conflict geometry workpack reports **665 aligned weekly dates**, **125 jointly evaluable dates**, **64 comparable four-week movement windows**, a **mean directional cosine of about 0.103** and a circular-shift placebo **p approximately 0.425** in its initial global comparison. Its refined test finds a few localized active-innovation episodes; much apparent raw similarity disappears when passive memory/decay is removed. The useful mathematical lesson is that **a high score in selected windows is not a global invariant or causal transport theorem**.

## F01.7. How to inspect the case archives safely

On a checked-out Linux installation, the evidence-intake route is a read-only command, for example:

```bash
python -m permansson_app.governance_cli domain-import \
  '/path/to/PRT_Russia_Ukraine_FOI_Companion_v0.4.1_FIXED.zip' \
  --case russia_ukraine --output /tmp/ru_source_inventory
```

The imported result must preserve the explicit **evidence-only** status. An observed source event date and the date when a source became usable (`known_at`) are distinct; timezone-free dates cannot silently be promoted to timestamp-aware as-of admissibility. For the Russia–Ukraine archive, an earlier successor-import audit found unresolved `known_at` values for its 328 date-form event rows under a generic timezone-aware filter. That is a semantic normalization gap, not an error in the original study's own timing reconstruction. Consult the domain importer's `clock.py`, `importer.py`, `registry.py`, `DOMAIN_IMPORTS.md`, and the separate case's frozen timing specification.

**Practice F01-D.** Create an evidence card with fields `source_uri`, `source_version`, `cutoff`, `artifact_hash`, `observation_type`, `known_at`, `semantic_role`, `claim_supported` and `claim_not_supported`. Fill it from the companion package only; never infer a `P` row from the presence of an event ledger. **Answer-key test:** every nonempty causal field must identify a separate fitted/assumed model and its provenance, not merely a descriptive CSV.

# F02. Reproducible neutral exercises and answer keys

## F02.1. Reproduce the existing application rather than build another one

The source authority is [data/capabilities.json](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/src/permansson_app/data/capabilities.json), [EXAMPLES_AND_LIMITS.md](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/EXAMPLES_AND_LIMITS.md), [scripts/end_to_end.py](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/scripts/end_to_end.py) and [REVIEWER_GUIDE.md](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/REVIEWER_GUIDE.md). A correctly installed Linux CPython 3.12/3.13 successor application has **26 finite numeric commands** plus **two native C10/C11 providers** under a distinct route. A successful example is *conditionally correct for its literal input* if its checker passes; it makes no historical or empirical assertion.

From a pinned checkout:

```bash
python -m pip install './apps/permansson/application-successor[full-schema]'
permansson-app about
permansson-app capabilities
permansson-app resources --full --output /tmp/permansson-classroom
permansson-app finite-kernel \
  /tmp/permansson-classroom/examples/finite_world.v1.model.json \
  --output /tmp/permansson-classroom-result
```

The `resources --full` command exports packaged examples and their schemas; `scripts/end_to_end.py` is the existing whole-suite executable guide and should **not** be duplicated by a new general runner. For true whole-suite reproducibility, follow its `--lean` mode from a pinned source checkout with the Research Lean toolchain installed. Without the `--lean` option, `lean-emit`/`lean-recheck` prove source-byte correspondence and tamper rejection, not compiler acceptance. Four packaged example inputs exceed their particular reflection bounds and are numeric-only at that size, as listed in `EXAMPLES_AND_LIMITS.md`.

## F02.2. Complete 26-profile practice index

Each row below comes from the **exact registered command**. The exercise asks the reader to run the named packaged fixture, identify its independent checker, report the mathematical object, and state at least one unsupported extrapolation. The last column is an answer-key theme, not a claim that all profiles have the same output shape.

| Profile command | Packaged fixture(s) | Learning checkpoint |
|---|---|---|
| `finite-safety` | `finite_safety.v1.json` | Almost-sure controlled invariant core; outside does not imply zero finite survival |
| `finite-kernel` | `finite_world.v1.model.json` | Induced exact rational K; no fitted primitive |
| `finite-cq1` | `cq1.v1.json` | Finite CQ-1 certificate; not Exact PR |
| `finite-exit` | `finite_world.v1.model.json + finite_region.v1.json` | Exit destination subprobability and never-exit mass |
| `frozen-menu` | `finite_menu.v1.json` | Maximum among a frozen declared menu only |
| `finite-bellman` | `control_hitting.v1.json` | Remaining-horizon state-feedback policy; fully observed |
| `finite-survival` | `finite_survival.v1.json` | Killed-kernel finite retention, not exact invariance |
| `finite-metric` | `metric.v1.json` | Finite W1 contraction bound requires strict contraction |
| `nonlinear-stationary` | `nonlinear.v1.json` | Score of recurrent-class laws before expectation |
| `one-step-risk` | `risk_occupancy.v1.json` | One-transition risk optimum, not multistage feedback |
| `finite-grammar` | `grammar.v1.json` | Included patch-block minimality relative to admitted grammar |
| `finite-perturbation` | `finite_perturbation.v1.json` | Finite TV error envelope, not long-run certificate |
| `finite-occupation` | `finite_world.v1.model.json` | Random limiting class occupancy vs expected occupancy |
| `finite-algebra` | `algebra.v1.json` | Declared rational algebra witness; not physically identified feature |
| `finite-robust-nature` | `robust_nature.v1.json` | Rectangular nature differs from committed nature |
| `finite-residence` | `residence.v1.json` | Reach-and-stay monitor, not first reach |
| `finite-multiagent` | `multiagent.v1.json` | Declared protocol and information timing |
| `finite-quotient` | `quotient.v1.json` | Typed quotient only under compatibility premises |
| `lp-check` | `Receipt object emitted by lp-propose` | Independent consumer; not standalone model-file producer |
| `lp-propose` | `lp.v1.model.json` | LP candidate and independent optimality checks; failed search ≠ infeasible |
| `one-step-belief` | `belief.v1.json` | Observe-then-act information structure |
| `finite-belief-tree` | `belief_tree.v1.json` | Finite observation-history tree law |
| `finite-private-stage` | `private_stage.v1.json` | Declared private-stage saddle, exact mixed witness |
| `finite-adaptive-grammar` | `adaptive.v1.json` | Adaptive row-local patches vs a frozen admissible block |
| `one-step-risk-infeasibility` | `risk_infeasibility.v1.json` | Exact lower risk bound can refute a proposed cap |
| `finite-cq1-transport` | `cq1_transport.v1.json` | Finite certificate transport under explicit error budget |


The case-specific source of expected statuses is **not this table**; it is the committed test and the per-profile numeric documentation. A reader must compare the exact path and output of the fixture actually run. `lp-check` is a crucial exception: it receives the `receipt` object derived from `lp-propose` output, as described next.

## F02.3. Exercise 1 — simple stochastic continuity (independent of app profiles)

Let a fictional municipal hotline have state `O` (operating) and `I` (interrupted), with declared transition matrix

$$
K=\begin{pmatrix}4/5&1/5\\1/4&3/4\end{pmatrix},
$$

ordered as `(O,I)`. Start in `O`. **Question A:** what is the probability of being in `O` after two steps? **Question B:** what is the probability of remaining in `O` at *every* step 0,1,2? **Question C:** can these quantities be substituted for one another in a residence monitor?

**Answer A.** `P(Y2=O)=(4/5)(4/5)+(1/5)(1/4)=16/25+1/20=69/100`.

**Answer B.** The all-in-`O` event is `P(Y1=O,Y2=O | Y0=O)=(4/5)^2=16/25`.

**Answer C.** No. Endpoint occupation is **69/100**; uninterrupted residence is **16/25**. A path may leave `O` and return before the endpoint. The example demonstrates event semantics, not an empirically estimated transition matrix.

## F02.4. Exercise 2 — a finite choice set is not a universal search

Two predeclared service-recovery menus contain fixed stationary alternatives A and B over the synthetic states `interrupted`, `restored`, `unavailable`. From `interrupted`, A restores with probability 1/4 and otherwise remains interrupted; B restores with probability 1/2 and otherwise enters unavailable. Goal and unavailable are terminal for this example. For two transitions and objective 'reach restored before unavailable':

$$
V_A = \frac14+\frac34\cdot\frac14=\frac7{16},
\qquad
V_B=\frac12.
$$

**Questions.** Which alternative wins the frozen two-item menu? What if state-dependent switching is allowed on the second transition? Does a zero result from some other menu prove impossible achievement?

**Answer.** B wins the **two-item fixed menu**. If the declared policy class permits a fresh decision at the second transition, choose A first and B after a return to interrupted; the two-step value is $1/4+(3/4)(1/2)=5/8$. That is a distinct D1 problem with different admissible policy rules. No finite list result can establish impossibility among unlisted alternatives. Volume C has the theorem and quantifier crosswalk.

## F02.5. Exercise 3 — exact risk feasibility in a noncombat model

The repository's packaged `risk_infeasibility.v1.json` constructs a finite one-step system whose independently checked least achievable next-step risk is **7/16**, while a proposed cap is **1/4**. Because $7/16-1/4=3/16>0$, the cap cannot be met **within that declared finite one-step policy class**. The exercise is to identify the primal/dual or Farkas-style witness and state the exact class of policies to which the certificate applies.

**Answer.** The exhibited minimum exceeds the cap by **3/16**. It does not imply a prohibition on a different multistage model, an expanded action menu, or an alternative observation structure. Read `NUMERIC_RISK_INFEASIBILITY.md` and the receipt checker rather than trusting a displayed status alone.

## F02.6. Exercise 4 — adaptive, private and bounded transport fixtures

The repository's packaged examples deliberately choose distinguishing rational witnesses:

- `adaptive.v1.json`: permitted row-local adaptation yields **9/16**, compared with the best fixed admitted block at **3/8**. The arithmetic difference is $9/16-3/8=3/16$. This does not admit an unlisted joint patch block.
- `private_stage.v1.json`: the declared private mixed-control game has value **1** with controller mixture `(1/2,1/2,0)` and a nature mixture `(3/5,2/5)`. These numbers are a witness for the exact declared payoff table; they have no physical interpretation.
- `cq1_transport.v1.json`: a declared CQ-1 margin of **8/25** is transported under its separate bounded perturbation assumptions to **301/1250**; the compared model's own margin **729/2500** respects that bound. The argument requires its actual declared error budget, not an arbitrary substitution of one total-variation estimate.

**Answer-key rule.** Never generalize beyond the explicit information timing, admissible patches, exact rational data and finite certificate type. Use the application's checker and bridge documentation for each fixture.

## F02.7. Exercise 5 — the LP producer/consumer handoff

`lp-propose` emits a proposal envelope. **`lp-check` does not accept the whole envelope as its certificate argument.** The latter expects the extracted `receipt` object, and a separate valid request. This is observable in the original `scripts/end_to_end.py`, which reconstructs `lp-check` input from `proposal.json` before invoking the consumer.

A portable illustrative shell sequence (from a checked-out installation) is:

```bash
permansson-app lp-propose \
  /tmp/permansson-classroom/examples/lp.v1.model.json \
  --output /tmp/permansson-lp-proposal

python - <<'PYCODE'
import json
from pathlib import Path
p = Path('/tmp/permansson-lp-proposal/proposal.json')
obj = json.loads(p.read_text(encoding='utf-8'))
Path('/tmp/permansson-certificate.json').write_text(
    json.dumps(obj['receipt'], indent=2) + '\n', encoding='utf-8')
PYCODE

permansson-app lp-check \
  /tmp/permansson-classroom/examples/lp.v1.model.json \
  /tmp/permansson-certificate.json \
  --output /tmp/permansson-lp-independent-check
```

**Exercise.** Mutate one rational certificate field or switch its certificate family. **Answer:** an independent checker must reject an invalid or mismatched certificate. Its error semantics matter; a producer that fails to find a feasible candidate does **not** prove global infeasibility.

## F02.8. Exercise 6 — scope and instance-evidence classification

Take three hypothetical records: (i) a finite numeric receipt with `independent_check.status = PASS`, (ii) a `lean-recheck` reply `ok=true`, (iii) a separately pinned Lean compiler log for a particular emitted theorem. Record what is known at each stage.

**Answer:** (i) the named receipt passed its independent numerical checker within that profile's declared scope; (ii) source candidate bytes were reconstructed consistently from the same input/receipt; (iii) the compiler checked that *literal instance theorem* under its actual assumptions, if the log/source identity is independently authenticated. None is an empirical identification or a blanket certification of the papers.

## F02.9. Reproduction worksheet (copy for every example)

| Field | Required record |
|---|---|
| Source checkout | exact Git commit + tree identity |
| Application | installed package version and artifact digest |
| Command | exact profile ID, CLI args and environment |
| Inputs | original JSON filename, SHA-256, schema version |
| Limits | horizon, dimensions, bit widths, reflection bound |
| Output | receipt hash, mathematical value, independent check |
| Candidate | emitted Lean family and byte recheck, if applicable |
| Compiler | external authenticated source and axiom audit, if separately run |
| Interpretation | one supported statement; at least two unsupported extrapolations |

A useful rule: if the result cannot be independently reconstructed from the pinned model and its receipt, **do not promote** it to a claimed verified exercise.

# F03. Scientific and engineering boundary matrix

## F03.1. Separate the objects before making claims

The formal theorem layer and the executable numerical layer do not share one universal success flag. The decisive claim chain is

$$
\begin{aligned}
&\text{typed model} \to \text{calculation} \to \text{independent check}\\
&\to \text{optional Lean instance}\\
&\to \text{separate scientific interpretation}.
\end{aligned}
$$

Each arrow needs its own evidence. Crucially, **empirical identification is a different research question**, not a prerequisite for computing a declared finite mathematical world. But it **is** a prerequisite for stronger claims that a fitted `P`, `alpha`, or `U` represents actual external causal dynamics. See [APPLICATION_BOUNDARY.md](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/APPLICATION_BOUNDARY.md), [ACCEPTANCE_STATUS.md](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md) and [FORMALIZATION_MAP.md](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/FORMALIZATION_MAP.md).

| Observation | Supported conclusion | Not licensed |
|---|---|---|
| JSON schema validates | The input satisfies declared structural constraints | All rows reflect reality or intended semantics |
| Typed finite model constructed | A well-defined conditional mathematical object exists | It is the unique representation of the external system |
| Exact producer emits rational value | A computed candidate for the declared model | Independent numeric verification |
| Independent checker passes | Source-separated numerical agreement for the named receipt | Authenticated Lean compilation |
| `lean-emit` succeeds | Candidate proof source can be emitted | Theorem acceptance by the Lean compiler |
| `lean-recheck` succeeds | Candidate source bytes match expected derivation | That the source is well typed or compiled |
| Pinned Lean compile plus axiom audit succeeds | Literal formal declaration is accepted with declared assumptions | Scientific correctness of unformalized prose or empirical causal identification |
| Original and Research Lean library CI succeeds | The specified libraries build at the exact commit | Every paper statement or external instance is proved |
| D0 menu maximum found | All indices in the declared frozen menu compared | The global optimum over every possible intervention |
| D1 Bellman optimum found | Value for declared finite full-observation class and deadline | Private-information or infinite-horizon optimum |
| D2 finite residence computed | Declared finite monitor objective checked | An Exact-GR limiting occupation law |
| Finite killed-kernel survival positive | A finite persistence event holds under the given matrix | Invariance for every state and all time |
| QSD certificate available | Named quasi-stationary hypothesis holds | Uniform finite retention without its own conditions |
| Finite CQ-1 margin positive | Finite-horizon certificate under frozen property/region/typed comparison | Full Exact PR status |
| Legacy semantic validator accepts envelope | Structural/semantic contract holds as specified | New app instance proof or external identification |
| Domain archive intake passes | Required source files and bounded archive integrity checked | Companion calculations independently reproduced or empirical causal model identified |
| Owner releases numeric package | Versioned artifact is qualified under the owner release policy | Independent mathematical or security certification |
| Historical research companion claims certification | Only its stated package-and-model scope can be considered | A theorem about all continuous models or the successor app |

## F03.2. Distinguish four kinds of mathematical persistence

1. **Endpoint event:** distribution at an indicated step; a state might have been left and later revisited.
2. **Finite survival:** region-membership event for a declared prefix, possibly represented using killed kernels.
3. **Finite residence:** a finite run-length condition requiring the specified number of consecutive goal visits.
4. **Exact Generated Regime:** an invariant region under **every** state in that region, the prescribed nontriviality gates, and limiting descriptor occupation semantics quantified over the declared initial-law class.

A valid finite residence/retention certificate is useful and entirely legitimate without becoming an Exact GR or generalized PR. The gap is one of **logical quantifiers**, not primarily a lack of computing power.

## F03.3. Name the optimization and evidence quantifiers

Whenever the word *optimal* is used, append its scope: `over 1..8 listed interventions`, `over deterministic remaining-horizon Markov schedules`, `over all admissible one-step randomized occupancies`, `over declared rectangular model rows`, etc. Similarly, whenever the word *certified* appears, identify the object: `numerically checked receipt`, `Lean-compiled bounded instance`, `independent case-specific frozen certificate`, or `independently accepted overarching claim`.

Do not let a Boolean field such as `scientific_claims_verified=false` be flipped by a user-provided file and interpreted as an external certification. The source's validation and policy tools check integrity and compatibility; they do not manufacture an independently trusted review identity.

## F03.4. Formal core is not identical to every paper or application result

The repository's `FORMALIZATION_MAP.md` says the numbered discrete mathematical-core obligations through **Proposition 8.1** have corresponding Lean closure. It separately labels specialized Appendix E results as outside that universal core and highlights explicit hypotheses such as standard Borel/nonempty ambient spaces. The Research Lean library adds independently scoped theorems; there is no license to retroactively claim that every historical empirical statement follows from the original core.

The earlier source and CI audit checked **784 Lean files** in the frozen tree: **776** through the two library roots, **seven** standalone witness compilations, and **one** checked import snapshot. That is evidence of coverage by repository workflows at the pinned commit. It is **not** the same as a manuscript-to-Lean equivalence proof for every sentence written in the guide.

## F03.5. A red-team exercise in claim language

Consider these statements and rewrite them so they become accurate.

| Overstatement | Required correction |
|---|---|
| "The solver proved the historical event ledger implies victory." | "A declared finite model yields a checked conditional value for the defined event and admissible class; the ledger-to-model causal step is a separate task." |
| "The bridge was generated, therefore Lean proved the result." | "The byte-corresponding candidate was emitted; compilation must be checked separately." |
| "A positive five-day survival proves a persistent generated regime." | "The finite survival event holds; all-state exact invariance and occupation limits have not been established." |
| "A 0% finite-menu result means no intervention can work." | "No declared listed menu member succeeds under this model, initial law, deadline and event." |
| "The source archive passed, so all its timestamps were known in real time." | "Source bytes passed integrity/role inspection; `known_at` admissibility is a separate case-specific chronological question." |
| "The native C10/C11 models are included in all 26 numeric profiles." | "The 26 budgeted exact profiles and the two closed native providers have separate registry and runner scopes." |
| "Research Lean CI passed; all 45+11 certification cases are independently signed off." | "Library CI passed at its source identity; the separate certification target remains unbound at the audited checkpoint." |

**Answer-key requirement:** in every correction, keep the actual supported positive result. Rigorous boundaries are not excuses to pretend that a successful calculation accomplished nothing.

# F04. Deferred engineering and research roadmap

## F04.1. Reuse first; build only the actual missing interfaces

Read [the successor roadmap](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/ROADMAP.md) against [acceptance status](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md), [implementation manifest](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/apps/permansson/application-successor/IMPLEMENTATION_MANIFEST.json) and [certification target intent](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/research/certification/target_intent.json). The separate `docs/FUTURE_THEORY_ROADMAP.md` is a **historical date-scoped research programme** (October 15 checkpoint). Its old *proposed* rows do not override later merged code. This is a source-precedence rule, not a stylistic choice.

**Already implemented; do not rebuild:**

- Original 64-file `PermanssonLean/` core, separate 711-file Research Lean tree, and root build/test workflows.
- D0 menus, D1 controlled finite-state objects and D2 finite residence mathematics, with multiple stronger research proof families in addition to the executable subset.
- **26** versioned exact finite numeric profiles, **27** bundled JSON schema files and **30** packaged JSON example files; two distinct native C10/C11 providers.
- Independent producer-separated checkers, 24 source-bound Lean bridge modules, source-byte rechecks and targeted compiler mutation tests.
- Existing full packaged example runner `scripts/end_to_end.py`, registry/resources introspection, release qualification and safe separate domain-source inventory.
- Legacy Application Standard v0.1.0 and archival/provenance contracts, kept distinct from the released successor.

**Additional work still genuinely deferred or conditional** is narrower. An extension should be named for a concrete missing *interface*, *semantic guarantee*, *platform qualification*, *source adapter*, or *acceptance step*; it should not be called a missing general reverse solver.

## F04.2. Engineering work packages after the guide

| ID | Current status at frozen source | Extension to build or evaluate | Dependency/acceptance test |
|---|---|---|---|
| EXT-01 | Versioned per-profile contracts exist; general cross-profile relationship incomplete | Typed cross-profile composition contract | Preserve exact event, horizon, initial law, intervention and receipt semantics; tests must reject unjustified composition |
| EXT-02 | Six case-aware **evidence-only** ZIP profiles exist | Case-specific chronological/semantic adapter reference, not automatic causal inference | Exact hash, row-role, timezone-aware `known_at`, lineage and ambiguity tests; no unsafe reclassification |
| EXT-03 | Read-only local federation and detached offline bundles exist | Authenticated external provider contract if explicitly approved later | Origin authentication, independent trust roots, scope separation and fail-closed negative tests |
| EXT-04 | `FIX-01` benchmark/X1 application route deferred | Separate finite benchmark numerical profile with its own registry/receipt/bridge scope | New authorization and exact-scope acceptance; do not imply research Lean modules are absent |
| EXT-05 | `ADV-01` nonfinite expert-evidence application route deferred | New specialized nonfinite contract only after mathematical and platform scoping | Termination/resource design, symbolic proof scope and independent acceptance; never advertise finite CLI as nonfinite |
| EXT-06 | Linux CPython 3.12/3.13 qualified for v0.2.0 | Platform-equivalent run-budget controller if portability desired | Windows/macOS process-group/limits safety, installed-wheel acceptance and reproducible qualification |
| EXT-07 | 26-workflow reviewed policy in force; 30-workflow T2 candidate separate | Review-gated T2 security-contract migration | Owner and independent scope-specific reviews, exact file diff, positive/negative workflow-control evidence |
| EXT-08 | Source/release checks and historical arithmetic tests exist | Separate independent **45 original + 11 later** certification acceptance | Reviewer source authentication; bind exact `certification_pr`; do not set unearned booleans |
| EXT-09 | Original v1.1 assembly, ledger and PDF QA completed at their recorded scope on 20 November 2026 | Refresh the source/evidence ledger and PDF QA for every subsequent edition; v1.1.1 has its own proofreading record | Preserve original artifacts; verify equations, links, table wrapping and each new manifest |

## F04.3. Independence of research and application development

There are three productive parallel projects, each with a different success condition.

1. **Pure theory:** prove new statements, counterexamples and hypotheses in the Research Lean library; subject those declarations to pinned compiler, axiom, import and negative-mutation checks.
2. **Finite application engineering:** register a new bounded exact numerical profile only when a distinct producer, schema, independent checker, documented scope, reproducible fixture and optional bridge exist.
3. **Empirical application science:** investigate whether observations can identify state semantics and transition kernels, with source-grade chronology, causal assumptions, held-out tests and publication claims. This need not block either conditional mathematical work or honest finite application documentation.

Conflating these projects creates either duplicate code or claims of certainty that no source supports.

## F04.4. Exit criteria for this manuscript

The guide manuscript's **first-draft completion** criterion was: all 46 chapters present, source-linked examples and explicit answers, exact source commit/registry pinned, existing scope/status labels preserved, and documented negative cases. A stronger **independent-publication acceptance** criterion still requires: full theorem-to-prose review, executable snippet replay from the released installed wheel, all PDF links and symbols checked, consistent paper size and typography, final citation/file identity audit, and approval of the manuscript as prose. It does **not** require all unrelated future theory, empirical identification, or independent CERT projects to be complete.

A release candidate should contain: `README`/front matter; all six volume manuscripts; one unified PDF; separate source and exercise ledgers; QA results; exact fixture/receipt manifests; and an honest known-limitations appendix. A draft that passes PDF rendering alone should not be stamped final.

**Dated edition clarification — 20 November 2026, Europe/Stockholm.** The installed-release replay and canonical v1.0 rendering were completed and are preserved in Appendix I. The first-draft criteria above describe that earlier production stage. The new v1.1 gate is set out in F04.6; it requires checking this edition's added sources, status statements and rendered pages rather than pretending the earlier wheel run has not occurred.

## F04.5. Reviewer checklist

1. Is the checked mathematical theorem the literal claim made in the prose, including every quantifier and hypothesis?
2. Does each code example run with an actual released or source-pinned binary under its platform limits?
3. Does the checker independently reproduce the numeric answer and reject deliberate mutation?
4. If a Lean candidate appears, is its status `NOT_EXECUTED`, byte-rechecked, or separately compiled and pinned?
5. Are off-by-one conventions, information timing, nonreach/never-exit mass, and the distinction between fixed menu, feedback and residence all correct?
6. Do historical examples retain their original source-cutoffs and nonclaims?
7. Are the 26 finite profiles, two native providers and 24 bridges distinguished?
8. Are deferred `FIX-01` and `ADV-01` correctly described as **unreleased application extensions**, not missing core theorems?
9. Are independent scientific review and causal identification clearly separate from arithmetic reproducibility?
10. Are page geometry, text, tables, links, bookmarks and the final PDF manifest publication-ready?

**Final exercise F04-A.** A reviewer notices that the October 15 roadmap says multiagent protocol research is proposed, but `PermanssonResearch/MultiAgent/` and a `finite-multiagent` profile are in the frozen November 1 `main` tree. Which status wins? **Answer:** actual current code and its exact-head successful CI, accompanied by the current acceptance document. Preserve the older roadmap as historical evidence; do not use its stale proposal language to erase implemented mathematics.

## F04.6. Completed source repairs and remaining work

The current work should be divided by the assertion still needing evidence, rather than by a stale “missing proof” label. The complete case-by-case plan is in Appendix J and its machine-readable crosswalk.

| Workstream | Recorded result | What remains |
|:--|:--|:--|
| D-05, B-02 and Q-03 bounded source interfaces | Actual event-to-game bridge, genuinely nonisomorphic admitted-order fixture and original measure/event-TV adapter. The actual source/compiler receipt state is recorded in E02.6; no unreported clean replay is inferred. Internal clause mapping is complete | Authentic independent criterion and scope adjudication; no unbounded generalization |
| Q-04 defective-row example | Baseline/treated visits, row TV 1, output gap 1 and original margin 1 versus reported margin 0 are derived in B06.2. The actual source/compiler receipt state is recorded in E02.6; no unreported clean replay is inferred. The full original comparison set and treatment error charge are mapped | Authentic independent decision on the stated literal criterion |
| M-02 existing-source receipt and scope correction | Actual marked-history and separate reactive-countermodel declarations retain their own autonomy premises. The actual source/compiler receipt state is recorded in E02.6; no unreported clean replay is inferred. Both witnesses are mapped separately | Authentic independent decision retaining the distinct premises; no stronger unified construction is inferred |
| Per-case evidence coverage | The all-56 selected-source receipt state is recorded separately in E06.6. The dated internal reconciliation completes 105 clauses across all 56 entries. Authentic current method joins and their overlap are recorded in Appendix J | Six precisely conditional stronger-scope/control items remain in the companion reconciliation; independent adequacy is undecided |
| Supplemental local controls | E-04 has an 18-name positive probe and two mathematical negatives; C11-02 has an accepted complete baseline and rejected genuine nonbottom-class report. Both detached readbacks pass | Retain separate local Lean and Python provenance; these are not additions to PR126 CI or its primary 17 controls |
| Independent acceptance | Frozen records and unsigned case-review forms are preserved | Obtain real identified independent decisions; internal review and CI cannot supply them |
| Conditional guide publication | Complete prose/source crosswalk and source/command audits; actual publication status is recorded separately | Final PDF review, CI/integration observation and artifact/Drive readback must have their own receipts; all 56 independent decisions remain separate |
| Future application extensions | A separate contract, input limits, producer/checker, fixture and release policy are required for any extension | No automatic expansion of the released v0.2.0 scope |

The documented new source results replace obsolete absence claims only at their stated interfaces. Already existing results should receive direct source and receipt coverage rather than being reimplemented. Source reading alone should not mark a negative control as executed, and an original `PARTIAL_SCOPE` record must keep its qualifier until an actual decision changes it.

The 154-method route inventory is source discovery: [final_closure_case_method_routes.py](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/final_closure_case_method_routes.py). Its current PR126 join now establishes explicit, unique OK outcomes for all 149 distinct selectors and 154 owned routes. The separately mapped 31 supplemental selectors and four D-02 timing/deadline methods also have authentic current observations; after the three selector overlaps are accounted for, the union is 181 distinct selectors and 193 distinct case/selector associations. The completed internal review maps their literal relevance and retains exact qualifications. Independent adequacy remains a separate decision, and the all-56 named-source probe itself executes zero semantic controls.

### Exact gate for the v1.1 conditional reference

The complete Markdown edition must retain all 46 chapters and all 24 formal-core interpretations, with every inserted example attached to its literal source, assumptions and comparison domain. The builder must verify the preserved v1.0 hash, distinguish its historical source from the final added-source commit, resolve every inserted source path, and reject unknown commands or fixture names. All asserted compiler results must identify actual source-bound receipts; any pending item must remain plainly pending.

The Q-04 source paragraph and source-bound receipts are now integrated. A completed technical-reference designation also requires the actual integration/publication observations and a full render with visual checks. The PDF review must inspect equations, long theorem names and paths, table wrapping, page geometry, headings/bookmarks, text extraction and links. The final PDF, Markdown, builder inputs, source crosswalk and QA record receive a fresh byte manifest. v1.0 and the historical addenda retain their original bytes.

The installed-release evidence remains the historical CPython 3.13 run: 28 end-to-end rows passed; 21 candidates were byte-checked but not compiled; matching already-installed dependencies were copied into the isolated environment; the optional `rfc8785` test was not rerun. This new research-source edition does not relabel that earlier experiment.

A conditional guide can meet this gate while the separate independent case-acceptance register remains unresolved. Its title, front matter and status ledger must say what has actually been completed, without claiming programme-wide scientific validation.

# Appendix F-A. Casebook source inventory

The external sources are versioned supplied artifacts, not files under `PermanssonLean` Git. For exact filenames and SHA-256 digests use the accompanying `Volume_F_External_Source_Manifest.csv` in the QA package, rather than inventing GitHub paths for them.

| Case | External versioned source | Repository intake source |
|---|---|---|
| Russia–Ukraine | Paper v0.2.1; companion v0.4.1 | `russia_ukraine` |
| Hormuz | Paper v1.1.1 | `hormuz` |
| MIDR | Report + companion v1.0 | `midr` |
| Iran | October report v0.2 + companion | `iran` |
| Brown–MacKay | Certification companion v0.4 | `brown_mackay` |
| Cross-conflict | Geometry workpack v0.1 | `cross_conflict` |

# Appendix F-B. Claim/evidence submission card

A reviewer should be able to inspect this short record for **every material result**:

```text
claim_id:
question_and_quantifiers:
state_space_and_observation_structure:
model_semantics_and_horizon:
source_commit_and_artifact_hashes:
input_schema_and_exact_request:
producer_command_and_status:
independent_checker_and_status:
lean_theorem_and_instance_status:
formalization_map_anchor:
external_evidence_origin_and_known_at:
empirical_identification_status:
independent_review_status:
release_scope_and_policy:
interpretation_and_nonclaims:
```

No extra status should be silently filled in merely because the field is present.

# Appendix F-C. Immutable source identity

```text
repository: HMarcusWH/PermanssonLean
main_commit: 89ac97cb8bcaad0c47c421209dd2e103db6d60ee
git_tree: cf3d19b5eaa3756fe5c2e392367b9066330e1a4b
application_release_commit: 63a66c82a9ece4361f646ee13b6711192f831406
```

# Appendix F-D. Historical first-draft completion and later editions

**Completeness:** All 46 planned chapters are present. This is an editorial count, not external certification; independent installed-release reproduction remains separately scoped.



\newpage

**Edition clarification.** The following statement is the preserved v1.0 source/interpretation record. The additional source identity and its actual evidence status appear in A03.1, E02.6 and E06.6. Its historical frozen-code wording does not erase the explicitly identified v1.1 additions.

# Historical v1.0 publication and verification statement

This reference edition is indexed to the immutable repository commit `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`.

The source Git tree is `cf3d19b5eaa3756fe5c2e392367b9066330e1a4b`. The release `permansson-app-v0.2.0` is a separate numeric artifact from commit `63a66c82a9ece4361f646ee13b6711192f831406`. The exact code implementation remains at its frozen versions throughout this guide.

The original paper's source-to-Lean map is [`docs/FORMALIZATION_MAP.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/FORMALIZATION_MAP.md). That map claims Lean closure of the numbered *v0.1.8 discrete formal core through Proposition 8.1*, not every specialized mathematical extension or all claims in every manuscript. The references in this edition were checked against the 2,302-file source snapshot. The corresponding formalization ledger lists 24 paper theorem/definition obligations, and all named Lean declarations were located in the source. The additional 24-entry editorial scope table below inspects source declaration interfaces and restricts the prose accordingly. This does **not** replace external independent expert review of every mathematical proof or specialized research claim.

The numerical examples are conditional on the given input, resource ceilings, and command profile. A passing exact-arithmetic receipt does not itself imply a successful Lean instance compilation. An emitted Lean source file or a successful byte recheck likewise does not establish a verified compiler run. The repository's pinned GitHub CI provides compilation evidence for its imported libraries and separately exercised witnesses; this edition does not assert fresh local compilation on every sample.

The repository's 45 original cases and 11 newer mathematical claims have separately documented independent acceptance status. A reader should verify the relevant acceptance evidence before describing any such claim as independently certified. The historical case-study imports have evidence/provenance semantics; they do not independently identify the underlying causal strategic generator, world transition, or update kernels.

**Use and interpretation.** The mathematics can be reproduced with the software's declared finite models and fictional service examples. This guide does not supply tactical targeting, strike sequencing, attack allocation, or operational military decision optimization.


\newpage

# Appendix G — Formal-core claim-to-declaration scope review (24 entries)

This appendix reports a **source-scope editorial reading** of all 24 entries in the repository's [`docs/FORMALIZATION_MAP.md`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/docs/FORMALIZATION_MAP.md) paper-to-Lean ledger. Its statements are **conditional on the exact Lean declaration interfaces**, including typeclass assumptions and predeclared objects. The source compilation record is supplied by the pinned GitHub CI, not by this PDF. The appendix does not independently verify Lean's kernel or certify empirical applications.

Two reading cautions are worth making prominent. First, `IsFinitePersistent` quantifies over **all of `spec.region`**, not just its basin (see Corollary 4.2b); the earlier edition misstated this in a schematic display. Second, the concrete Lean declaration `enlarged_state_reduction` is a proof that the already-constructed induced kernel is Markov, **not** by itself an executable general history-to-Markov compiler.

| Paper object | Source-bound reading | Essential qualification |
|:---|:---|:---|
| Thm. 3.1 | Probability initial law; Markov induced kernel; existence and uniqueness of specified full path law | Does not identify alpha, P, U from observations. |
| Prop. 3.2 | The named declaration proves IsMarkovKernel of the induced joint kernel | It does not, by itself, construct an arbitrary finite-history reduction; discuss augmentation as separate modeling work. |
| Prop. 4.1a | Polish/Borel descriptor-space certificate with metric and weak-convergence structure | Not a declaration about arbitrary non-Polish spaces. |
| Prop. 4.2 | Exact one-step invariance for every y in region B is equivalent to a.s. indefinite survival from every y in B | Do not replace the region quantifier with basin B0. |
| Thm. 4.2a | Path survival and killed-kernel mass coincide from y in B; surviving endpoints and Green/tail expectation have separate equalities | The identities are not estimates of external-world survival. |
| Cor. 4.2b | Finite persistence iff killed-mass finite persistence at given horizon and eta <= 1, quantified over all y in B | Not merely over the declared initial basin B0. |
| Cor. 4.2c | A nonnegative uniform one-step retention floor q over every z in B implies q^n killed survival lower bound, starting y in B | Cannot infer a one-step floor from selected sample trajectories. |
| Def. 4.3 | Exact GR = canonical well-posedness and Assumption 4.1 and exact invariance and convergence for all admissible initial laws | One finite simulation or a positive occupation estimate is insufficient. |
| Def. 4.4a | QSD-certified quasi-regime requires both a finite-persistence gate and a QSD eigenmeasure certificate | QSD existence alone is not the finite-persistence gate. |
| Prop. 4.4b | Given a supported QSD with theta>0 and theta<=1, obtains scaled survival and conditional-stationarity certificate | Conditional stationarity is not unconditional invariance. |
| Def. 5.1 | Generalized PR relative to a specified admissible strategic intervention or existentially over a frozen family, additionally requires Exact GR | Numeric property difference without the baseline regime and legal comparison set is not PR. |
| Prop. 5.2 | Two-sided property effect/margin perturbation inequality requires explicit output bounds on baseline and intervened values | An observed effect size is not a causal identification certificate. |
| Cor. 5.3 | Uniform constitution is retained under declared margins and perturbation budgets; PR certificate keeps baseline regime requirements | Must not promote perturbation robustness into empirical validity. |
| Prop. 5.4 | Uniform one-step event-TV bound epsilon on two Markov kernels gives a finite-prefix TV envelope and <=Tepsilon under declared measurability assumptions | Only finite horizon; no unrestricted infinite-horizon closeness. |
| Thm. 6.1 | Paper-I selected-model EGR iff embedded Exact GR for the specified lifted model and regime | Not a map from every arbitrary equilibrium game without the selected-model encoding. |
| Thm. 6.2 | Paper-I PR iff compatible embedded relative PR under matched policy intervention and transported property/comparison set | Requires transported intervention and property conventions; not equality from the baseline K alone. |
| Prop. 7.1 | The same induced baseline K entails equivalent Exact GR status for a common frozen specification | This implication does not transfer arbitrary constitutive intervention status. |
| Thm. 7.2 | Exhibits two concrete Boolean/Unit strategic-world factorizations with identical induced K but distinct G and P | An existence counterexample, not identification of a unique true factorization. |
| Thm. 7.3 | Constructed concrete pair demonstrates constitution can differ despite equal baseline K | Does not say all representations are constitutively inequivalent. |
| Prop. 7.4 | Constitutive equivalence requires common baseline K and matched intervened kernels with compatible comparisons | Baseline kernel equality alone is insufficient. |
| Prop. 7.4a | Frozen-family PR equivalence under explicitly matched intervention signatures | No invariance under arbitrary replacement or relabeling of intervention families. |
| Thm. 7.4b | Type-respecting compression with kernel intertwining and matched regimes/interventions transports family PR status | Not an automatic license for arbitrary dimension reduction. |
| Prop. 7.5 | Under matching grounded path-law projections, nuisance padding cannot create a new grounded effect | Depends on the declared relevance map and the matching hypotheses. |
| Prop. 8.1 | A particular periodic constructed model satisfies the paper-level Exact GR predicate | One existence witness; not a theorem that every periodic process is Exact GR. |

**Inspection trace.** The accompanying `Core_24_Theorem_Scope_Review.csv` and `.json` include the exact source path, Lean declaration names and declaration-header extracts for each row. A reader should consult those bytes before making a stronger theorem claim. The separate `Core_24_Complete_Declaration_Header_Addendum_2026-11-20` supplies complete headers for all 30 declarations, including the two historical extracts truncated inside named arguments; it preserves the original companion and source pins. This table does not convert a `def` into a separately proved existence theorem.

**Independent-review boundary.** The repository separately records unresolved or distinct independent acceptance questions for 45 original cases and 11 later mathematical claims. Neither compilation success nor the 24-entry table automatically discharges them. A technical reader may reproduce the stated finite mathematics from the existing source and fixtures without claiming external scientific approval.


**Historical core-review scope.** Appendix H retains the original 24 interpretations and their review context, with the nonnegative parameter types in obligations 06 and 07 made explicit in v1.1.1. Its statements about relying on existing source CI and not performing a new local compilation apply to that earlier core interpretation review. The new source-probe receipts described in E02.6 are a separate v1.1 activity.

# Appendix H — Independently interpreted theorem scope (24 obligations)

**Source-based mathematical review; not an outside peer-review certificate.**

## Mathematical verdict

**Interpretation accepted for technical reference use with two substantive scope corrections and one explicit witness distinction.** The core is coherent as a conditional stochastic-process/regime-classification framework. The two scope corrections concern the actual range of Proposition 3.2 and the weakness of the point-initialized comparison-set diversity condition. The witness distinction concerns Theorem 7.3, whose Lean proof verifies an alternative example rather than the paper’s literal Bernoulli long-run example.

**What the framework is:** a factorized Markov-process generator with regime predicates and typed-intervention-relative constitution, plus separately scoped reverse-solver families. It does **not** define a novel Nash-equilibrium concept or establish that its factorizations, intervention semantics, or stochastic parameters are learned from observed data.

**Logical relationship:**
1. Supplying `alpha`, `P`, and `U` defines `K`, its path law, and conditional state/property probabilities.
2. A specified `(B, B0, h, nu, convergence mode)` may qualify as an Exact GR only when the full conjunction holds.
3. A PR requires a qualifying GR baseline **and** nonzero property change under an intervention from the frozen grammar.
4. The same baseline `K` can underlie different intervention responses; structural attribution is not a function of baseline `K` alone.
5. D0/D1/D2 optimizers are conditional on their declared admissible classes and information structures; they do not prove a global strategy over every possible model.

# Paper-to-Lean interpretations — all 24 formal-core obligations

## 01. Thm. 3.1 — Joint-process well-posedness

**Interpretation:** Given a declared Markov strategic-world model and an initial probability law, the induced joint-state kernel is a valid Markov kernel and determines a unique law on infinite trajectories. This is well-posedness of a specified stochastic process, not existence of a strategic equilibrium or uniqueness of any economic/game-theoretic solution.

**Formal prerequisites and quantifiers:** The model already supplies measurable action-selection, world and update kernels; the initial law is a probability measure. Uniqueness applies to the full path law satisfying the named transition law, not to the factorization of the transition law.

**Game-theoretic/statistical reading:** This is the Ionescu–Tulcea / Markov-path-law layer of the framework. It establishes a coherent object to classify; it does not determine the input components from data.

**Verdict:** `ALIGNED`. **Lean source:** [`WellPosedness.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/StrategicWorld/WellPosedness.lean#L173).

## 02. Prop. 3.2 — Enlarged-state reduction

**Interpretation:** The named proposition proves the induced joint-state kernel of an already specified StrategicWorldModel is Markov. The human-language idea that sufficient memory can be put in the state is valid as a modeling strategy, but the specifically named Lean declaration does not implement an arbitrary history-augmentation construction.

**Formal prerequisites and quantifiers:** A suitable augmented state and its measurable transition kernels must first be constructed; simply calling a process Markov does not make its originally observed coordinate Markov.

**Game-theoretic/statistical reading:** Use this proposition only for the joint kernel. Send general finite-history and information-state encodings to the separately scoped Research Lean constructions.

**Verdict:** `SCOPE_TIGHTENED`. **Lean source:** [`WellPosedness.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/StrategicWorld/WellPosedness.lean#L185).

## 03. Prop. 4.1a — Polish descriptor-space generality

**Interpretation:** For a Polish descriptor space with its Borel structure, a bounded metric/weak-convergence certificate supports the paper’s measure-valued descriptor formulation. The result broadens beyond a compact descriptor range but does not remove the topological and measurability assumptions.

**Formal prerequisites and quantifiers:** The theorem explicitly assumes TopologicalSpace, PolishSpace, MeasurableSpace and BorelSpace on H. It does not state a generic convergence theorem for every descriptor trajectory.

**Game-theoretic/statistical reading:** Separates the choice of a suitable descriptor-space metric from the much harder question whether an occupation process converges in that metric.

**Verdict:** `ALIGNED`. **Lean source:** [`PolishDescriptor.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/PolishDescriptor.lean#L303).

## 04. Prop. 4.2 — Exact invariance equivalent forms

**Interpretation:** For a single declared Markov model and measurable region B, one-step invariance at every y in B is equivalent to almost-sure survival in B for all future times from every y in B. This is a robust statewise equivalence, not a statistical inference from observed long runs.

**Formal prerequisites and quantifiers:** Both sides quantify over the entire regime region B, not only its basin B0. The survival event is indefinite, whereas finite-persistence events have explicit horizons.

**Game-theoretic/statistical reading:** Do not use a high-but-imperfect finite-horizon survival value to infer exact invariance; 0.999 is different from 1.

**Verdict:** `ALIGNED`. **Lean source:** [`Persistence.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/Persistence.lean#L261).

## 05. Thm. 4.2a — Exact killed-kernel persistence calculus

**Interpretation:** The killed-kernel identities express finite-horizon survival as retained substochastic mass, surviving endpoints as killed-kernel powers, and expected first exit time as a sum of survival tails. These are exact identities for the given stochastic kernel.

**Formal prerequisites and quantifiers:** The survival and endpoint equalities start from y in B. The expected-exit-time sum is an extended nonnegative quantity; nothing in the equality guarantees its finiteness.

**Game-theoretic/statistical reading:** This permits independent calculations of survival and exit quantities from one declared kernel, not statements about unmodeled external events.

**Verdict:** `ALIGNED`. **Lean source:** [`ExitTimeExpectation.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/ExitTimeExpectation.lean#L123), [`SurvivalBridge.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/SurvivalBridge.lean#L204).

## 06. Cor. 4.2b — Exact finite-persistence characterization

**Interpretation:** A finite-persistence requirement stated as survival probability at least 1−eta for horizon L is logically equivalent to the corresponding killed-kernel mass inequality.

**Formal prerequisites and quantifiers:** The parameter eta is nonnegative (typed ℝ≥0∞ in Lean), the predicate explicitly includes eta ≤ 1, and the inequality is required for EVERY starting state y in B; the paper’s infimum convention is represented by this pointwise universal inequality.

**Game-theoretic/statistical reading:** Do not replace the region B by the initial basin B0, and do not infer infinite-horizon invariance from any finite L.

**Verdict:** `ALIGNED`. **Lean source:** [`Persistence.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/Persistence.lean#L142).

## 07. Cor. 4.2c — One-step `q^L` lower bound

**Interpretation:** A state-uniform lower bound q on one-step retention probability within B implies the n-step lower bound q^n for killed survival from every y in B. It is a conservative propagation rule, not an equality in general.

**Formal prerequisites and quantifiers:** The parameter q is nonnegative (typed ℝ≥0∞ in Lean), with q ≤ K(z,B) for every z in B, and the starting state y belongs to B. A floor established only on a simulation path or sampled subset does not satisfy the premise.

**Game-theoretic/statistical reading:** The lower bound typically decreases with horizon when q<1; it does not prove exact persistence.

**Verdict:** `ALIGNED`. **Lean source:** [`Persistence.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/Persistence.lean#L84).

## 08. Def. 4.3 — Exact Generated Regime

**Interpretation:** Exact GR is a CONJUNCTION: canonical path-law well-posedness, Assumption 4.1, exact invariance of B, and occupation-law convergence in the declared mode for every initial probability law concentrated on B0. This is a property of a frozen model plus frozen specification, not an intrinsic label of K alone.

**Formal prerequisites and quantifiers:** Assumption 4.1 includes basin nonemptiness, region topological/measure nontriviality, at least two descriptor values in B, and two distinct point-initialized basin path laws. Lean carries the specification as an input but cannot verify the historical timing of its predeclaration.

**Game-theoretic/statistical reading:** The separately named confirmatory GR additionally requires reachable descriptor nondegeneracy; the broader Exact GR does not automatically assert it.

**Verdict:** `SCOPE_TIGHTENED`. **Lean source:** [`GeneratedRegime.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/GeneratedRegime.lean#L40).

## 09. Def. 4.4a — QSD-certified quasi-regime

**Interpretation:** A QSD-certified quasi-regime requires BOTH the finite-persistence gate and a valid quasi-stationary distribution with its killed-kernel eigenmeasure identity. It is neither simply a QSD nor automatically an Exact GR.

**Formal prerequisites and quantifiers:** The QSD law has mass one in B, 0<theta≤1, and its killed one-step image equals theta times the original measure.

**Game-theoretic/statistical reading:** The QSD concerns a particular distribution over surviving states; the finite-persistence gate is uniform across states in B, so the first does not substitute for the second.

**Verdict:** `ALIGNED`. **Lean source:** [`QuasiStationary.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/QuasiStationary.lean#L49).

## 10. Prop. 4.4b — QSD survival and conditional stationarity

**Interpretation:** Starting in an actual QSD, the probability of survival for n transitions is theta^n and the endpoint distribution conditional on survival equals the starting QSD. The unconditioned surviving endpoint measure has total mass theta^n.

**Formal prerequisites and quantifiers:** Conditional stationarity is defined only because theta>0, and is NOT equality of the unconditional state distribution to μ on the full process.

**Game-theoretic/statistical reading:** This is the standard quasi-stationary versus stationary distinction; it does not assert persistence from arbitrary initial states.

**Verdict:** `ALIGNED`. **Lean source:** [`QuasiStationary.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/QuasiStationary.lean#L193).

## 11. Def. 5.1 — Generalized Permansson Regime

**Interpretation:** A generalized PR is an Exact GR plus at least one admissible, predeclared strategic-generator intervention whose specified path-law property differs at every comparison state. The relative form names one intervention; the family form existentially selects within the frozen family.

**Formal prerequisites and quantifiers:** The comparison set lies within B0 and contains two distinct point-initialized path laws; the intervened model need not remain an Exact GR. Distinct point-initialized FULL path laws are a weak structural diversity gate because their time-zero coordinates already distinguish different initial states.

**Game-theoretic/statistical reading:** PR is a relational, grammar-dependent classification. To claim substantive path dependence, inspect shifted/future-law differences or grounded path properties separately; the nontriviality witness alone does not prove those.

**Verdict:** `SCOPE_TIGHTENED`. **Lean source:** [`Permansson.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/Permansson.lean#L21).

## 12. Prop. 5.2 — Two-sided constitutive-margin perturbation bound

**Interpretation:** If a baseline and an intervened property value are each approximated with certified errors ε0 and εJ, the absolute error in their distance, and in the infimal constitutive margin, is bounded by ε0+εJ. This is a metric triangle-inequality bound.

**Formal prerequisites and quantifiers:** The stated errors must really control the property outputs on the comparison set; this theorem does not itself create the bounds or certify a data-fitting procedure.

**Game-theoretic/statistical reading:** The conclusion is numerical/model robustness of a declared comparison, not robust external causation.

**Verdict:** `ALIGNED`. **Lean source:** [`Perturbation.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/Perturbation.lean#L164).

## 13. Cor. 5.3 — Robust PR certificate

**Interpretation:** If the ORIGINAL uniform constitutive margin is strictly greater than the total declared property-output error budget, the perturbed margin remains positive. The PR certificate version retains the Exact GR premise of the original baseline.

**Formal prerequisites and quantifiers:** One must know the unperturbed margin, the error budget and the existence of a valid comparison set, and verify a STRICT inequality.

**Game-theoretic/statistical reading:** The theorem protects the sign of a quantified mathematical effect under supplied bounds; it does not prove empirical stability of the world.

**Verdict:** `ALIGNED`. **Lean source:** [`Perturbation.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/Perturbation.lean#L252), [`UniformPermansson.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/UniformPermansson.lean#L119).

## 14. Prop. 5.4 — Finite-horizon kernel-to-path envelope

**Interpretation:** For two Markov kernels starting from the same state and a UNIFORM one-step event-total-variation bound ε, a finite prefix through T transitions differs in total variation by at most 1−(1−ε)^T, which is no larger than Tε.

**Formal prerequisites and quantifiers:** The theorem assumes the requisite measurable-space hypotheses and 0≤ε≤1. The envelope applies to finite prefixes, not to arbitrarily long paths with one constant small error budget.

**Game-theoretic/statistical reading:** A one-step discrepancy accumulates along a trajectory; this is a perturbation envelope, not an infinite-time invariance theorem.

**Verdict:** `ALIGNED`. **Lean source:** [`FinitePrefixTV.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Probability/FinitePrefixTV.lean#L388).

## 15. Thm. 6.1 — EGR embedding

**Interpretation:** The selected equilibrium-generated Paper-I model, when lifted into the specified state-recording representation, is an EGR if and only if its embedding is an Exact GR. The result establishes conservative inclusion of the earlier framework within the generalized one.

**Formal prerequisites and quantifiers:** It is parameterized by a PaperISelectedModel and a matched embedded specification. It does not prove a Nash or subgame-perfect equilibrium exists and does not embed arbitrary undefined games.

**Game-theoretic/statistical reading:** Equilibrium is a *possible source* of the generator, not a required primitive of the regime-classification layer.

**Verdict:** `ALIGNED`. **Lean source:** [`RegimeEmbedding.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/EGR/RegimeEmbedding.lean#L205).

## 16. Thm. 6.2 — Conservative Permansson extension

**Interpretation:** Paper-I constitutive PR status is preserved under a specifically transported intervention and property/comparison-set convention. The equivalence depends on preserving the relevant world or recorded-action path-law semantics under embedding.

**Formal prerequisites and quantifiers:** The paper’s conservative hierarchy is restricted to TRANSPORTED Paper-I protocols. It does not identify unrestricted generalized PR with the original PR class, and equality of baseline kernels alone is insufficient.

**Game-theoretic/statistical reading:** This is a compatibility theorem for a declared modeling translation, not a general strategic equivalence between unaligned games.

**Verdict:** `ALIGNED`. **Lean source:** [`PermanssonTransport.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/EGR/PermanssonTransport.lean#L356).

## 17. Prop. 7.1 — Baseline representation invariance

**Interpretation:** If two strategic-world factorizations induce exactly the same baseline joint-state Markov kernel and use the same frozen regime specification/reference measure, they have the same Exact GR classification.

**Formal prerequisites and quantifiers:** It says nothing about whether their constituent action-selection and world-response kernels are equal, nor about the effects of changing those constituents.

**Game-theoretic/statistical reading:** This formalizes the separation between dynamical observational equivalence and structural decomposition.

**Verdict:** `ALIGNED`. **Lean source:** [`RepresentationEquivalence.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/RepresentationEquivalence.lean#L102).

## 18. Thm. 7.2 — Factorization non-identification

**Interpretation:** An explicit finite counterexample shows two different strategic/world decompositions with identical induced baseline K. Hence observing K alone cannot generally identify the strategic generator or world-transition kernel.

**Formal prerequisites and quantifiers:** The result is existential non-identification, not a theorem that every factorization is indistinguishable or that no additional interventions/measurements could identify one.

**Game-theoretic/statistical reading:** In game-theoretic language this is observational equivalence with different mechanisms, a familiar reason to distinguish structural and reduced-form models.

**Verdict:** `ALIGNED`. **Lean source:** [`FactorizationCounterexample.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Examples/FactorizationCounterexample.lean#L121).

## 19. Thm. 7.3 — Constitutive non-invariance under baseline equivalence

**Interpretation:** An explicit constructed pair proves that identical baseline induced kernels and simultaneous Exact GR status do not force the same answer to a strategic constitutive-intervention test. In one model the declared replacement changes no tested property; in the other it produces a positive uniform effect.

**Formal prerequisites and quantifiers:** CRITICAL WITNESS DISTINCTION: the v0.1.8 manuscript uses a Bernoulli(1/2) long-run occupation example (gap 1/2); the Lean proof uses an alternative deterministic identity-dynamics construction, a ONE-STEP survival property, margin 1, and a custom convergence mode that always returns True. It proves the existential non-invariance proposition, NOT the manuscript’s literal Bernoulli/SLLN witness.

**Game-theoretic/statistical reading:** This is mathematically legitimate as a separate counterexample to the broad existential claim, but it does not machine-check the particular convergence analysis asserted for the manuscript’s illustrated construction. Keep the two witnesses explicitly separate.

**Verdict:** `WITNESS_SCOPE_GAP`. **Lean source:** [`ConstitutiveNoninvariance.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Examples/ConstitutiveNoninvariance.lean#L470).

## 20. Prop. 7.4 — Intervention-compatible invariance

**Interpretation:** When two models share both the baseline induced kernel and the matched POST-INTERVENTION kernel, a fixed path-property comparison has the same constitutive truth value. The comparison set is transported using the proven baseline-kernel equality.

**Formal prerequisites and quantifiers:** Both equalities are hypotheses. Sharing baseline K alone is exactly what Theorem 7.3 showed insufficient.

**Game-theoretic/statistical reading:** This provides the appropriate invariance test for a specified intervention, not invariance of every unlisted counterfactual.

**Verdict:** `ALIGNED`. **Lean source:** [`InterventionEquivalence.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/InterventionEquivalence.lean#L39).

## 21. Prop. 7.4a — Intervention-family invariance

**Interpretation:** For frozen INDEXED intervention families, a signature-preserving equivalence transports family-level PR status. The condition fixes more than a single chosen intervention: it accounts for the comparison signatures of all admitted members.

**Formal prerequisites and quantifiers:** The theorem assumes an InterventionCompatibleFamilyEquivalence object. A mere bijection of names or parameters does not imply that their intervened kernels or relevant properties match.

**Game-theoretic/statistical reading:** This permits re-encoding a finite intervention grammar without changing the question when the requisite signature evidence exists.

**Verdict:** `ALIGNED`. **Lean source:** [`FamilyEquivalence.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/FamilyEquivalence.lean#L161).

## 22. Thm. 7.4b — Intervention-compatible quotient preservation

**Interpretation:** A type-respecting state compression preserves the specified family PR classification when it admits all required kernel intertwining, initial-law, regime, property and intervention compatibility witnesses.

**Formal prerequisites and quantifiers:** The statement quantifies over an InterventionCompatibleStateQuotient certificate. It is a sufficient, heavily conditional preservation theorem, not a blanket assertion that any state aggregation or dimensionality reduction is harmless.

**Game-theoretic/statistical reading:** This is the closest connection to probabilistic bisimulation/lumpability; for interpretability one should state which projected observables are preserved.

**Verdict:** `ALIGNED`. **Lean source:** [`Preservation.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Quotient/Preservation.lean#L165).

## 23. Prop. 7.5 — Nuisance-padding exclusion

**Interpretation:** Adding nuisance coordinates cannot create a new effect measured through a grounded relevance map if the baseline and intervened grounded path laws match the original model. The metric gap is equal under padding; if the original grounded property did not change, neither can the padded version.

**Formal prerequisites and quantifiers:** The relevant path-law projection equalities are an explicit premise; this is not a test that identifies which features are genuinely relevant.

**Game-theoretic/statistical reading:** The result prevents a declared grounded comparison from acquiring an artificial effect solely through bookkeeping dimensions, provided the matching assumptions hold.

**Verdict:** `ALIGNED`. **Lean source:** [`NuisancePadding.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Regime/NuisancePadding.lean#L112).

## 24. Prop. 8.1 — Periodic Exact GR

**Interpretation:** A constructed deterministic two-cycle is an Exact GR under almost-sure WEAK convergence of empirical occupation laws to the half-half measure on the cycle. The instantaneous state distribution can oscillate even while the time-averaged descriptor law converges.

**Formal prerequisites and quantifiers:** This is a SPECIFIC periodic example whose invariance, nontriviality and occupation convergence are proved. The source uses ConvergenceMode.almostSureWeak, not a trivially true custom convergence mode.

**Game-theoretic/statistical reading:** It demonstrates why stationarity of the one-step state law and long-run occupation convergence must not be conflated. It is not a universal theorem for every periodic Markov system.

**Verdict:** `ALIGNED`. **Lean source:** [`PeriodicExactGR.lean`](https://github.com/HMarcusWH/PermanssonLean/blob/89ac97cb8bcaad0c47c421209dd2e103db6d60ee/PermanssonLean/Examples/PeriodicExactGR.lean#L585).

# Important paper-to-Lean witness distinction
The **Theorem 7.3** Lean source explicitly says its proof uses an "equivalent deterministic finite witness" instead of the Bernoulli(1/2) / long-run expectation example in the paper. This is not a flaw in the logical existential result: one valid counterexample establishes that baseline equivalence does **not** imply constitutive equivalence. But the phrase “the paper’s specific Example 7.3 is formalized line-for-line” would be false.

The Lean witness is set up with `ConvergenceMode.custom ... (fun _ _ _ => True)`, identity baseline dynamics on a two-bit joint state, two strategic-state initial conditions sharing one world-state bit, and a one-step survival property. Its positive constitutive margin is 1. The **manuscript** uses an i.i.d. Bernoulli world process, a long-run occupation property and a margin of 1/2. In both constructions the **existential non-invariance claim** follows, but their asymptotic details are distinct. The guide should describe this as *alternative-witness closure*, not an exact transcription of the manuscript example.

# Operational meaning of the reverse-solver mathematics (noncombat examples)
## D0 — frozen menus
D0 fixes a finite, nonempty set of admissible stationary interventions. For each member, a model-defined probability of hitting a target before a forbidden state within T steps is evaluated. The proof of menu optimality concerns **all members of the declared menu**, not strategies outside it. A zero maximum says nothing about omitted alternatives or empirical possibility. The equivalence from rational tables to a typed `alpha/P/U` model is established only in a constructed family, not for arbitrary real-world factorizations.

## D1 — observed feedback and histories
A state-feedback row choice may outperform any globally fixed D0 member, because the same fixed action need not suit all model states. Further D1 results address nonstationary or history-dependent policies in **their declared finite fully observed classes**. Keep information availability and time dependence explicit; do not infer these results for partial observation, different risk rules, or arbitrary external factorizations without a new theorem.

## D2 — residence objectives
Entering a set by time T is different from remaining in it for m subsequent transitions. The D2 residence event is `exists e <= T, forall j <= m, Y(e+j) in G`, observed through T+m. The semantics allow retrying after failed entry and count starting in G as e=0. The completed-by-D version has a different deadline. A proof for one event definition is not a proof for the other.

# Interpretation controls for the guide
**Strongly stated and supported:** (i) given model primitives and measurability, the Markov path law is well-posed; (ii) exact persistence and killed-kernel calculus are rigorous within the model; (iii) constitutive PR status is relative to typed counterfactuals; (iv) equal baseline K is insufficient for constitutive attribution; (v) matched intervention signatures and sufficiently compatible quotients preserve the relevant formal status.

**State with explicit qualifiers:** Exact GR requires its complete multi-clause gate and prescribed convergence; the point-initialized path-law nontriviality is not substantive future diversity; robust margins require error bounds; conditional QSD stationarity is not unconditional stationarity; a custom convergence mode is a weak witness when compared with almost-sure weak convergence.

**Must not claim:** a new equilibrium existence or strategic-solution theorem; a general history-state conversion from the named Proposition 3.2 declaration; empirical recovery of `alpha/P/U`; an unrestricted reverse-solver optimum; universal dimension-reduction invariance; real-world conflict efficacy; independent acceptance of all research-only extensions.

# Historical mathematical-review recommendations (incorporated before v1.0)
- **B03:** Keep `ex ante` as a frozen modeling convention; explicitly state that Lean cannot authenticate the historical declaration date.
- **B05:** Replace “strong baseline path-law nontriviality” with “formal point-initialized path-law nontriviality.” Add that differences in full path laws follow from different time-zero states and need not imply different future transition responses.
- **B06:** Keep the baseline/intervention equivalence distinction; add Theorem 7.3 alternative-witness note to the theorem appendix.
- **Appendix G:** Retain the 24-row source index, supplemented with these interpretations and with the deliberate distinction between paper evidence and alternative Lean witnesses.
- **Version label:** `v0.9.2 — mathematically interpreted technical reference`. This is an internal source-scope review status; external certification remains a distinct administrative/scientific act, not something to demand before the user can read an accurate guide.

# Sources and reproducibility
- Frozen source: [Pinned repository tree](https://github.com/HMarcusWH/PermanssonLean/tree/89ac97cb8bcaad0c47c421209dd2e103db6d60ee).
- Original paper: *Permansson Regimes: A General Framework for Strategic Dynamics Beyond Equilibrium*, working paper v0.1.8 (23 September 2026).
- Core formalization map: `docs/FORMALIZATION_MAP.md`.
- Secondary D0/D1/D2 scope sources: `docs/D0_FROZEN_MENU.md`, `docs/D1_CONTROLLED_KERNEL.md`, and `docs/D2_RESIDENCE_OBJECTIVE.md`. Historical status headers may predate current merges; current source/CI status is separately pinned.
- Interpretations are constructed from exact Lean statements and immediate prerequisites; the pinned CI is the existing Lean compilation record. No new local Lean compilation is claimed in this review.


\newpage

# Appendix I — Preserved installed-release reproduction and v1.0 scope

## I.1 What was independently reproduced here

The full 64-character SHA-256 values are recorded in the machine-readable release-verification manifest; prefixes in the printed table are abbreviated for legibility.

The release subject was the GitHub-published **Permansson application 0.2.0**, *not* a wheel built from an unpinned development checkout. The build artifacts were recovered from [the 1 November 2026 GitHub Actions release run](https://github.com/HMarcusWH/PermanssonLean/actions/runs/41313849870), specifically the `release-build` and `release-gated` artifacts. Two independently built wheel/sdist pairs match each other byte-for-byte and match the published release asset digests.

| Release subject | Verified SHA-256 |
|:--|:--|
| `permansson_application_successor_recovery-0.2.0-py3-none-any.whl` | `c119d66a1459535d17e2…` |
| `permansson_application_successor_recovery-0.2.0.tar.gz` | `873af692897d6bf4de2c…` |
| `release-manifest.json` | `d556cee5c1ea5e6f4f2c…` |

The application-release source commit is `63a66c82a9ece4361f646ee13b6711192f831406`; the reviewed guide's frozen source reference is the later `89ac97cb8bcaad0c47c421209dd2e103db6d60ee`. The release's owner-engineering authority is **not** an independent mathematical or security certificate.

## I.2 Installed application results

A separate Python 3.13 virtual environment was used. The installed `permansson-app about` command resolved `permansson_app` to that virtual environment, rather than the source checkout. The reference package's own `end_to_end.py --app` test was run *without* `--skip-install-check`, using the frozen repository tree solely for native provider bytes and the example/check harness.

| Check | Result | Boundary |
|:--|:--|:--|
| Application package identity | 0.2.0, imported from isolated venv | Package installed from authenticated-release-build-matching wheel |
| Finite profiles registered | 26 | Numeric scope `successor-finite-numeric.v1` |
| Primary packaged examples | 25 passed | Profile-specific exact numerical results and independent checker |
| Native C10/C11 requests | Three passed | Native source-checked provider paths, separately scoped |
| Total end-to-end rows | 28 passed, zero failures | Installed-wheel re-run; no fresh Lean compile |
| Source-bound Lean candidates | 21 emitted, byte-rechecked, tamper-rejected | `lean_status = NOT_EXECUTED` for application reports |
| Numeric-only reflection-bound cases | Four | Deliberate reflection bounds, not failed computations |
| LP certificate consumer | Passed | The receipt must be extracted from `lp-propose`'s `proposal.json` |
| Resource export | 57 files | Package resource packaging and reading |
| Missing-input negative control | Exit 2, no output folder | Fail-closed CLI handling |

All 25 primary results passed their **profile-specific independent numerical checks**. The emitted Lean candidates were not compiled in this local pass, and the source's previous pinned GitHub Lean CI is not an installed-instance proof transcript. That distinction remains mandatory in every example.

## I.3 Offline environment qualification

The local environment had no direct Internet package-index access. Therefore the virtual environment installed the published wheel with `--no-index --no-deps` and copied the already-installed matching Python dependency package files and distribution metadata into its own `site-packages`: `jsonschema 4.26.0`, `referencing 0.37.0`, `attrs 26.1.0`, `rpds-py 2026.5.1` and `jsonschema-specifications 2025.9.1`. `pip check` then reported no broken requirements. This provides application import isolation and reproducibility **but is not a separate authenticated download of all transitive dependencies**.

The release itself has original CI qualification records for Linux CPython 3.12 and 3.13; this local installed-wheel reproduction used CPython 3.13 only. Other platforms are not qualified by this experiment.

## I.4 Claim-status separation and follow-up evidence

**Verified here:** exact published distribution digests, installed package import identity, bounded numeric fixtures, independent receipt checks, source-byte candidate integrity, negative mutations, and the native exact-rational replay responses.

**Not verified here:** fresh local Lean compilation of emitted instance candidates, empirical identification of `alpha/P/U` in a real system, unrestricted strategic-control optimality, the research programme's 45 historical plus 11 later independent acceptance decisions, or a new security certification. The optional `rfc8785` canonical-digest dependency test was not rerun locally; its absence is not evidence of failure, nor a PASS.

The numerical release's claims `scientific_claims_verified = false` and `empirical_identification = NOT_IDENTIFIED` remain authoritative. The broader research certification register remains separate and unapproved; the technical reference guide v1.0 is an accurate **conditional reference**, not a declaration of programme-wide scientific validation.

**Reproduction evidence included with this edition:** `Installed_Release_Reproducibility_v1.json`, the 28-row `installed_wheel_e2e_report.json`, `installed_wheel_e2e.log`, `local_dependency_provenance.json`, release metadata/checksum copies, a local exact-test inventory and the v1.0 PDF QA record. All are distributed as a supporting reproducibility bundle.


## I.5 Relation to the v1.1 research-source additions

The reproduction described in I.1–I.4 is the preserved v1.0 installed-application experiment. New research-source compiler receipts are identified in E02.6 and do not change its 21 candidate files to compiled instances. The release's Linux CPython 3.12/3.13 qualification, the local CPython 3.13 environment, copied matching dependencies and unrerun optional rfc8785 test retain their original scope. No new independent case acceptance or empirical identification follows from the edition assembly.


## I.6 Original support bundles and historical render identity

The [canonical v1.0 support archive](https://drive.google.com/file/d/1Y-X07wH2Z08MwpaEDPxs8iKYn2xYKJD6/view) preserves the original Markdown, canonical PDF, installed-release report, walkthrough JSON/log, dependency provenance, release assets and source-anchor records. Its archive SHA-256 is `ff7e22ac1568e5e42d63e3da016dac40640b6ee6fd74db1fbb045e58ed418433`. The recovered manifest is byte-identical to the preserved canonical manifest, and all 19 listed members match their recorded hashes and sizes.

The separately named [v1.0 Complete Evidence archive](https://drive.google.com/file/d/1JlcA0SyDwvOgL9KzW5tSc4jxzG8ob6Iz/view), SHA-256 `12c153cb8db61f92f3b61fae8f6c23406f58b44b36eb0a6902abf0b113229d05`, is internally consistent but contains a different archived PDF render and corresponding manifest. Of the 20 archive members, 18 are identical across the archives, including the Markdown and installed-release evidence. The authoritative canonical PDF is the one with SHA-256 `717223f7216958ded79eb890f741ba55537971b63ce55259d26bc98fb8a7b89a`; the other archived PDF has SHA-256 `7665dcd9c1c8d6854a9beab82b8e047eaf1dce16fa41cf9a6882ee81cf742be6`. The archives are preserved under their original names and are not silently substituted for one another.

The accompanying `Original_Companion_Artifact_Inventory.json` distinguishes members of these recovered archives from the older Core_24, external-source and 26-profile QA companions referenced by the inherited chapters. A separately named historical artifact is not recreated by renaming a related newer table. The integrity verification concerns original bytes and does not imply a new execution of the installed-wheel examples.

The separately named original companions have also been recovered and hashed: [Core_24 source-scope JSON](https://drive.google.com/file/d/1A5CDoSy2Yi-ZRW-YBvKwEqgPx655-axU/view), [Core_24 CSV](https://drive.google.com/file/d/1D4cV5H0FnNz5RIbar70YQY2jodJKKwe6/view), [Volume F external-source manifest](https://drive.google.com/file/d/1iZU0Z3PzVOrqTS0PuWRk7C99vwjpHXjR/view), and [26-profile source/engine/checker integration CSV](https://drive.google.com/file/d/1ZrreAqVT64ZW04v3o3Q68UMAUB7zf0UJ/view). Their actual file identities and full digests appear in the companion inventory; their original filenames are retained.

\newpage

# Appendix J — All 56 cases: criteria, source routes and remaining scope

This crosswalk preserves the original 45-case register and separate 11 later claims. The records remain 15 `PENDING`, 30 `PARTIAL_SCOPE` and 11 `SOURCE_PRESENT_REVIEW_PENDING`. They describe acceptance dispositions, not a count of absent Lean proofs. Direct compiler receipts and broader literal-criterion decisions are distinct evidence.

The original source routes below are pinned to the frozen Tranche 9 head `5cee78c124c46a551e70bea92056efdcf5e6f292`; additive source probes carry their own source identity in the catalog. The complete JSON companion preserves every frozen record, all selected qualified names, source hashes and edition receipt metadata. Case identifiers containing a hyphen, such as Q-03 and D-09, are not the same register entries as later Q3 and D9.

Each entry names the literal criterion or later-claim interpretation, the source catalog IDs and the retained scope boundary. The existing replay routes and the edition evidence ledger determine what was actually executed. A source-present declaration is not automatically an independently accepted case.

## J.0. Internal clause reconciliation — 20 November 2026

The dated internal reconciliation now maps all 56 entries through 105 explicit clauses to actual theorem statements, controls and stored receipts. It replaces a generic mapping backlog with concrete evidence and stated residual scope. The companion `Internal_56_Clause_Reconciliation_Addendum_2026-11-20.md` and its JSON retain the full mapping, the original frozen rows, source hashes and execution provenance. This is an internal technical review; no independent case decision is created.

The authentic PR126 Research log separately records explicit, unique OK outcomes for all 149 original selectors/154 case-owned routes, 31 supplemental selectors/35 associations, and four additional D-02 timing/deadline methods. Three supplemental selectors overlap the original registry; the union is 181 distinct selectors and 193 distinct case/selector associations. The joins bind candidate 23e6a57b381363cf20751a18337ca927cd393a6c to run 44639175231 and job 135965431558, with exact source and log hashes in the companion JSON. Prior actual-main observations retain their producing commit. A method PASS establishes execution of its body; it does not decide that the body covers every literal clause.

| Case | Dated evidence or scope correction |
|:--|:--|
| A-01 | Finite dual-supremum equality and an attained primal coupling are proved. A general named dual-attaining potential and complementary-equality witness were not located; that stronger purpose is not inferred from supremum equality. |
| A-04 | The actual four-process interfaces require all four factorization data. The stored missing-fourth-argument rejection and the scalar three-output impossibility are distinct from a concrete canonical four-process model with exactly one failed factorization; that stronger model was not located. |
| E-01 / E-05 | The shared specialized-boundary audit imports only the E-02/E-03 `BoundaryWitnesses` provider. Relevant rank/Gram evidence instead comes from the actual selected compiler signatures and the dedicated E-01 semantic and E-05 full-Gram methods. |
| E-04 | The registered inverse mutant belongs to E-03. A separate local E-04 addendum now checks 18 names (14 local theorems and four original providers) and mathematically rejects both zero-coefficient cancellation and positivity without a preimage. Its detached source/transcript readback passes. These two local controls are separate from PR126 CI and its primary 17 controls. |
| C11-02 | A separate local complete-report check now accepts the original three-state baseline and rejects a genuine nonbottom SCC {0}. Positive outgoing edges to states 1 and 2 establish nonbottomness; this is Python checker evidence, separate from Lean controls and PR126 CI. The older reordered-class mutation retains its original meaning. |
| Later Q1 | The canonical discounted wrapper requires its initial witness ξ to be a probability measure, dominated by the initial probability μ with its pushforward dominated by ν. It therefore does not construct an arbitrary initial-mismatch subprobability witness. The separate nonstationary projected-evolution theorem uses a finite common submeasure. |
| D-07 | The older robust-mixing arithmetic method receives no leakage/infinite-safety clause credit. The actual leakage path-law and stationary-optimum providers supply the relevant evidence. |


## J.1. Original 45 cases

### X-01 — PENDING

**Criterion.** Each of 8 literal matrices equals actual typed atoms at all 324 pairs.

**Source routes.** S123, S145, S090, S087, S155.

**Named anchors.** `protocol_atom_eq`; `matrix_atom_eq`.

**Scope and remaining review.** The strengthened control separately checks a normalized nonnegative candidate row and rejects the wrong actual atom value 1/2 in place of 3/4. Source-formula equality and emitted literal-table equality remain separate obligations.

### X-02 — PARTIAL_SCOPE

**Criterion.** All 576 literal terminal entries satisfy initialization and successor equations.

**Source routes.** S144, S154, S088, S155.

**Named anchors.** `table_zero`; `table_step`; `original_property_eq_table`.

**Scope and remaining review.** Finite literal table coverage is distinct from the universal recurrence theorem.

### X-03 — PARTIAL_SCOPE

**Criterion.** All 54 effect entries and six minima with complete start domain.

**Source routes.** S144, S154, S086, S155.

**Named anchors.** `effects_eq_candidates`; `exactEffect_lower`; `exactEffect_attained`; `component_original_margin`.

**Scope and remaining review.** Do not replace the original comparison set with selected attaining starts.

### X-04 — PENDING

**Criterion.** Corrupt emitted Lean denominator or omit minimizing start.

**Source routes.** S124, S107, S086, S092, S155.

**Named anchors.** `attainingStart_mem`.

**Scope and remaining review.** The historical unique-attainer-only objection is stale: the tied-equilibrium omitted-domain source exists.

### X-05 — PARTIAL_SCOPE

**Criterion.** Reset before action, use new rather than old world, swap action/update labels.

**Source routes.** S144, S107, S090, S155.

**Named anchors.** `protocol_atom_eq`.

**Scope and remaining review.** A type/interface rejection and numerical kernel-equality rejection should be labeled separately.

### X-06 — PARTIAL_SCOPE

**Criterion.** Promote positive margins to old Exact GR.

**Source routes.** S154, S099, S107, S106, S085, S155.

**Named anchors.** `replete_not_exactGR`.

**Scope and remaining review.** This is deliberately a boundary theorem, not a missing general invariance proof.

### S-01 — PARTIAL_SCOPE

**Criterion.** Both-player exact advantage table and dynamic policy telescoping.

**Source routes.** S142, S148, S006, S089, S091, S155.

**Named anchors.** `finite_performance_difference`; `strategy_exact_advantage`; `nonstationary_terminal_identity`.

**Scope and remaining review.** Current opponent draw remains independent and unobserved within the admitted policy class.

### S-02 — PARTIAL_SCOPE

**Criterion.** Current opponent action or future draw is available to deviation.

**Source routes.** S135, S097, S149, S083, S084, S155.

**Named anchors.** `BehavioralPolicy`; `actual_step_fair_matching`; `peeked_fair_matching`; `no_unobserved_draw_copy`; `observed_history_cannot_copy_next_state`.

**Scope and remaining review.** Exclusion from an interface alone is not an executed semantic countermodel.

### M-01 — PARTIAL_SCOPE

**Criterion.** Stochastic strict anchors differing off reachable key support.

**Source routes.** S132, S101, S148, S031, S011, S155.

**Named anchors.** `strict_anchors_pathLaw_eq`; `ae_anchors_pathLaw_eq`.

**Scope and remaining review.** Off-support differences may be allowed; omitted on-support update agreement is not.

### M-02 — PENDING

**Criterion.** Endogenous common coordinate or missing update agreement.

**Source routes.** S121, S117, S116, S010, S019, S020, S012, S013, S031, S011, S014, S158, S155.

**Named anchors.** `point_start_violates_premise`; `strictAnchor`; `strictAnchor_isStrict`; `sourceProfile`; `markedLaw`; `markedLaw_actual_source_atom`; `actual_unmarked_next_key_fair`; `actual_unmarked_next_key_laws_equal`; `actual_marked_diagonal_separation`; `update_mechanisms_differ`; `same_physical_P_for_both_actual_protocols`; `actual_opponent_private_update`; `same_allowed_anchor_update_key`; `unequal_actual_update_rows`; `original_strict_anchor_premise_rejected`; `actual_opponent_action_fair`; `source_aligned_atom`; `source_crossed_atom`; `unmarked_key_laws_identical`; `marked_diagonal_separates`; `unmarked_not_strict_certificate`; `opponentMark`; `autonomous_marked_atom`; `BaselineAgreement`; `supported_full_kernel_eq`; `strict_anchors_pathLaw_eq`; `BaselineAEAgreement`; `ae_anchors_pathLaw_eq`; `row_iff_all_histories`; `exists_row_iff_all_histories`.

**Scope and remaining review.** Two separately strict anchors have equal unmarked marginals and different actual marked laws. A separate reactive-opponent witness refutes strictness; the two constructions must not be combined into an unproved unified history theorem.

**Edition evidence.** `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 29 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_M-02_Receipt.json` (SHA-256 prefix `ca5969c76844`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`).

### F-01 — PENDING

**Criterion.** Asymmetric player swap and finite three-player reduction.

**Source routes.** S119, S103, S028, S018, S164, S155.

**Named anchors.** `actual_pathLaw`.

**Scope and remaining review.** No new proof gap identified in this read-only audit; finite and measurable conditional-product scopes remain separate.

**Edition evidence.** Merged Tranche 8 source packet: 37 named declarations and three semantic compiler controls.

### F-02 — PARTIAL_SCOPE

**Criterion.** Clock never updated or driven by treated action.

**Source routes.** S137, S101, S108, S030, S027, S023, S022, S021, S155.

**Named anchors.** `actual_projection`; `natural_projection`; `natural_scheduled_row`; `inherited_strictness`; `advancing_update`; `stalled_clock_rejected`.

**Scope and remaining review.** Clock is part of the augmented baseline and must really advance.

### F-03 — PARTIAL_SCOPE

**Criterion.** Two own-key-equal states with disjoint legal actions.

**Source routes.** S133, S101, S107, S100, S016, S155.

**Named anchors.** `exists_feasible_strictAnchor_iff`.

**Scope and remaining review.** Finite menu/nonempty rows do not ensure a common strict probability anchor.

### F-04 — PARTIAL_SCOPE

**Criterion.** Fair diagonal two-player joint law.

**Source routes.** S101, S108, S015, S155.

**Named anchors.** `mediator_mixture_eq`.

**Scope and remaining review.** Conditional independent draws given a mediator do not imply an unconditional product law.

### F-05 — PENDING

**Criterion.** Identical observed SCMs Y=M versus Y=T with M=T.

**Source routes.** S122, S133, S108, S017, S029, S155.

**Named anchors.** `two_SCMs_same_observational_law`; `two_SCMs_different_joint_do`; `two_SCMs_positivity_failure`.

**Scope and remaining review.** Historical dedicated-positive-Lean absence is stale: explicit positive-support SCM and original identification instantiation exist.

### Q-01 — PARTIAL_SCOPE

**Criterion.** Non-Markov fine projection with fine common-mass lift.

**Source routes.** S099, S149, S053, S155.

**Named anchors.** `approxQuotient_prefix_tv_le_geometric`.

**Scope and remaining review.** No projected-process Markov claim is available from matching one start.

### Q-02 — PENDING

**Criterion.** eta zero/one, T zero and mismatched initial laws.

**Source routes.** S127, S108, S053, S041, S054, S155.

**Named anchors.** `approxQuotient_prefix_tv_le_geometric`; `discounted_geometric_budget_initial`; `zero_row_defect_retains_initial_budget`.

**Scope and remaining review.** Historical homogeneous/matched-start-only objection is stale for the generic expanded adapter; canonical property/full-path bindings remain explicit and separate.

### Q-03 — PENDING

**Criterion.** Sequential correlated stage errors.

**Source routes.** S120, S093, S105, S036, S044, S040, S039, S159, S155.

**Named anchors.** `primitiveCommon_mass_ge_product`; `inducedKernel_tv_le_primitive_product`; `path_tv_le_product`; `initialStep`; `nextRow`; `dependentAtom`; `perfectAtom`; `dependentLaw`; `perfectLaw`; `true_history_mass`; `finiteHalfL1`; `dependent_three_stage_halfL1_exact`; `actual_retained_product`; `evolution`; `evolution_probability`; `evolution_mono`; `retained`; `common_mass_ge`; `prefix_tv_le_product`; `zero_defect_product`; `unit_defect_product`; `recurring_leak_retained_tendsto_zero`; `recurring_leak_budget_tendsto_one`.

**Scope and remaining review.** B07.1 adds the actual measure/event-TV equality 23/50 and an explicit unconditional dependence witness to the existing conditional common-mass bounds. Compiler and control status is reported in E02.6.

**Edition evidence.** `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 51 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_Q-03_Receipt.json` (SHA-256 prefix `0f60c35c1e85`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`).

### Q-04 — PENDING

**Criterion.** Counterfactual reaches a baseline-unvisited high-defect row.

**Source routes.** S115, S125, S105, S048, S052, S045, S047, S001, S002, S160, S155.

**Named anchors.** `historyEvolution_tv_le_sum`; `geometricQuotient_margin_abs_le`; `eventTV_compProd_averaged`; `historyEvolution`; `goodHistoryMajorant`; `goodHistory_lintegral_le`; `historyEvolution_tv_le_goodVisits`; `finitePrefixLaw_tv_le_averaged`; `finitePrefixLaw_tv_le_goodVisits`; `mixedFinitePrefixLaw`; `mixedFinitePrefixLaw_tv_le_initial`; `finitePrefixLaw_tv_le_goodVisits_initial`; `finitePathExpectation_abs_le_goodVisits_initial`; `LocalizedProtocolErrors`; `baselineBudget`; `interventionBudget`; `toConstitutiveOutputErrors`; `reportedMargin_abs_le`; `trueMargin_pos_of_reported`; `reportedMargin_pos_of_true`; `matchedPair`; `exactLocalizedErrors`; `reportedEffect_four_fifths`; `reportedMargin_four_fifths`; `localizedBudget_total_one_fifth`; `originalMargin_ge_three_fifths`; `originalMargin_positive`; `cannot_omit_baseline_report_error`; `cannot_omit_treatment_report_error`; `initialMismatch_gap_one`.

**Scope and remaining review.** B06.2 distinguishes the existing reporting-error example from the new defective-row/treated-visit fixture. Its final source and receipt status remain explicit; baseline visit bounds cannot replace treated visit bounds.

**Edition evidence.** `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 65 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_Q-04_Receipt.json` (SHA-256 prefix `fd2cc0cf72c7`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`).

### Q-05 — PENDING

**Criterion.** Fixed tiny leakage and infinite survival.

**Source routes.** S102, S126, S127, S152, S151, S153, S150, S063, S161, S162, S155.

**Named anchors.** `high_actual_finite_survival_zero_infinite`.

**Scope and remaining review.** B06.1 identifies the actual original whole-path margins 19/90 and 1/5 and their gap 1/90. The earlier 2/41 bound remains valid; Exact GR and external identification are separate.

**Edition evidence.** Merged source and focused original-margin/whole-path replay recorded in the Tranche 7/8 packet.

### A-01 — PARTIAL_SCOPE

**Criterion.** Finite transport potentials, coupling and complementary equality.

**Source routes.** S138, S094, S149, S042, S043, S155.

**Named anchors.** `finite_couplingW1_eq_dual_supremum`; `scaled_two_point_exact`; `scaled_two_point_bound_two_rejected`.

**Scope and remaining review.** Finite dual-supremum equality and primal coupling attainment are proved. A general named dual-attaining potential or complementary-equality witness was not located in the inspected providers. Larger-space quantization and first-moment assumptions remain separate.

### A-02 — PARTIAL_SCOPE

**Criterion.** Identity kernel or perturbation removing irreducibility.

**Source routes.** S136, S094, S148, S035, S155.

**Named anchors.** `exists_unique_invariant`.

**Scope and remaining review.** Do not infer unique invariant law from nonexpansion or missing irreducibility.

### A-03 — PARTIAL_SCOPE

**Criterion.** Unbounded metric with small TV but large mean-distance shift.

**Source routes.** S094, S146, S046, S155.

**Named anchors.** `tv_does_not_control_w1_on_real`.

**Scope and remaining review.** Bounded diameter is a premise, not a hidden normalization.

### A-04 — PARTIAL_SCOPE

**Criterion.** One of four kernels lacks stated occupation factorization.

**Source routes.** S094, S142, S147, S038, S037, S155.

**Named anchors.** `four_actual_factorizations`.

**Scope and remaining review.** All four factorization data are required by the actual theorem interfaces. A historical missing-DJt application rejection and a scalar three-output countermodel are present; a canonical four-process model with exactly one false factorization was not located.

### A-05 — PARTIAL_SCOPE

**Criterion.** Time-zero/survival property inserted as occupation functional.

**Source routes.** S094, S107, S147, S034, S155.

**Named anchors.** `contraction_does_not_transfer_survival`.

**Scope and remaining review.** Contraction does not identify an arbitrary path property with an occupation functional.

### D-01 — PARTIAL_SCOPE

**Criterion.** All finite histories compared with monitor summary and behavioral mixtures.

**Source routes.** S097, S148, S065, S066, S155.

**Named anchors.** `behavioralResidence_optimal_and_attained`; `monitor_history_probability_optimal_and_attained`.

**Scope and remaining review.** Known finite fully observed model and finite horizon remain explicit.

### D-02 — PARTIAL_SCOPE

**Criterion.** time zero, m=0, retry versus first entry, entry/completion deadline.

**Source routes.** S097, S118, S111, S061, S155.

**Named anchors.** `first_entry_retry_counterexample`; `firstEntry_event_eq`.

**Scope and remaining review.** Event classification conventions cannot be swapped while reusing a value.

### D-03 — PARTIAL_SCOPE

**Criterion.** Danger at time zero, at success, and after success.

**Source routes.** S118, S143, S111, S057, S073, S078, S077, S155.

**Named anchors.** `danger_precedes_simultaneous_success`; `danger_after_success_does_not_undo`; `behavioralAvoidResidence_optimal_and_attained`; `initial_risk_iff_time`; `actual_risk_probability_eq_occupancy`; `actual_success_integral_eq_original`; `danger_at_zero_counts`; `danger_after_completed_success_counts`; `simultaneous_target_danger_counts`; `failure_and_danger_are_not_complements`.

**Scope and remaining review.** Failure, danger and lack of success are not interchangeable events.

### D-04 — PARTIAL_SCOPE

**Criterion.** 4/5+p/10 success and p/10 risk <=1/20.

**Source routes.** S097, S140, S112, S062, S155.

**Named anchors.** `actual_half_attains`; `all_actual_feasible_success_le`; `full_risky_choice_is_infeasible`.

**Scope and remaining review.** Finite occupancy LP/reconstruction scope is different from unrestricted optimization.

### D-05 — PENDING

**Criterion.** Static model pairs(.1,.9),(.9,.1).

**Source routes.** S128, S111, S074, S157, S155.

**Named anchors.** `whole_model_commitment_strictly_exceeds_rectangular`.

**Scope and remaining review.** C07.1 adds the actual two-state game bridge: committed 9/100, full admitted behavioral rectangular minimum 1/100, and switching attainment. It preserves the selected event expectation rather than differently typed raw path laws.

**Edition evidence.** `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 47 named declarations with allowed-axiom output and 3 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_D-05_Receipt.json` (SHA-256 prefix `d89bd1432c5a`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`).

### D-06 — PENDING

**Criterion.** Same physical belief but different hidden completed flags.

**Source routes.** S131, S112, S058, S165, S155.

**Named anchors.** `monitored_history_attained`.

**Scope and remaining review.** Current-readout insufficiency does not establish posterior uniqueness/minimality.

**Edition evidence.** Merged Tranche 9 source packet: 39 named declarations and three semantic compiler controls.

### D-07 — PARTIAL_SCOPE

**Criterion.** Finite survival tends to zero under positive leakage.

**Source routes.** S134, S097, S146, S063, S064, S155.

**Named anchors.** `high_actual_finite_survival_zero_infinite`; `deterministic_stationary_infinite_optimum`.

**Scope and remaining review.** The actual leakage fixture has positive finite survival and zero infinite safety, while the stationary-optimum theorem retains finite controlled-state hypotheses. The old robust-mixing scalar check does not address this literal clause.

### D-08 — PENDING

**Criterion.** Illegal/conflicting grammar block selected by controller.

**Source routes.** S109, S129, S056, S166, S155.

**Named anchors.** `adaptive_block_optimal_and_attained`.

**Scope and remaining review.** Raw normalized conflicting folds may exist and depend on order; no certified choice differs from no raw kernel.

**Edition evidence.** Merged Tranche 9 source packet: 30 named declarations and three semantic compiler controls.

### D-09 — PENDING

**Criterion.** Different physical classes share descriptor target.

**Source routes.** S110, S104, S059, S076, S075, S163, S155.

**Named anchors.** `physical_classes_remain_distinct`; `equal_descriptor_laws_equal_values`; `stationary_menu_actual_optimal_and_attained`.

**Scope and remaining review.** The two-absorber expected score 1/2 versus barycenter 5/6 and the native phase-blind maximum 5/6 versus phase-aware 1 are different model/property/policy statements.

**Edition evidence.** Merged Tranche 8 source packet: 19 named declarations and three semantic compiler controls.

### C11-01 — PARTIAL_SCOPE

**Criterion.** Singleton, periodic, multi-class, nonpositive dimension.

**Source routes.** S114, S148, S059, S060, S155.

**Named anchors.** `periodic_family_accepted`; `zero_dimension_reference_rejected`; `referenceStationaryFamily_check`.

**Scope and remaining review.** The bottom-class construction applies to declared nonempty finite stochastic matrices; the zero-state input is rejected.

### C11-02 — PARTIAL_SCOPE

**Criterion.** Missing/duplicate/nonbottom class or wrong all-state stationary vector.

**Source routes.** S114, S107, S148, S059, S155.

**Named anchors.** `corrupted_stationary_receipt_rejected`.

**Scope and remaining review.** The actual checker accepts the complete original three-state transient-split report with bottom classes {1},{2}. A separately executed local adversary preserves the input digest, schema, class count and full vector but names SCC {0}, whose outgoing probabilities 1/3 and 2/3 prove it is not bottom. The unchanged class-comparison check rejects it. Detached byte/transcript readback passes. This Python checker control is separate from Lean, PR126 CI and independent acceptance; the historical reordered-class test is not relabeled.

### C-01 — PARTIAL_SCOPE

**Criterion.** Growing-block countable chain and escaping mass.

**Source routes.** S139, S146, S033, S032, S155.

**Named anchors.** `canonical_clock_no_weak_limit`; `canonical_growing_block_occupations_fail`.

**Scope and remaining review.** No unrestricted countable/nonfinite occupation convergence theorem is claimed.

### B-01 — PENDING

**Criterion.** Two overlapping patches prescribe opposite Dirac laws.

**Source routes.** S130, S113, S107, S008, S007, S155.

**Named anchors.** `applyCompatiblePatches_perm`.

**Scope and remaining review.** Historical concrete-overlap absence is stale; differing fold orders remain normalized.

### B-02 — PENDING

**Criterion.** Positive incomparable singletons and XOR.

**Source routes.** S113, S095, S096, S009, S156, S155.

**Named anchors.** `exists_least_positive_of_finite_meet_closed`.

**Scope and remaining review.** C08.2 retains the original AND/XOR margins and adds positive local minimality transport between genuinely nonisomorphic admitted orders. Component-map noninjectivity alone would not establish that conclusion.

**Edition evidence.** `CI_AND_CLEAN_REPLAY_PASS`: Clean committed replay and authenticated PR126 Research CI each checked 65 named declarations with allowed-axiom output and 5 intended mathematical rejections. Source inputs and worktrees remained unchanged. Independent acceptance remains separate. Receipt: `PR126_Tranche10_B-02_Receipt.json` (SHA-256 prefix `5b1dd829d437`); `PR126_New_Compiler_Receipt_Verification.json` (SHA-256 prefix `5f7c4e501810`); `Tranche10_Five_Case_Clean_Receipts.json` (SHA-256 prefix `5d953233ff8a`).

### XPLUS-01 — PARTIAL_SCOPE

**Criterion.** New model all original GR and grounded comparison fields.

**Source routes.** S142, S154, S148, S004, S003, S005, S155.

**Named anchors.** `original_exactGR`; `original_confirmatoryGR`; `original_grounded_confirmatory_uniformPR`; `baseline_leak_not_original_exactGR`.

**Scope and remaining review.** New constructed model is distinct from the historical X1 witness.

### E-01 — PARTIAL_SCOPE

**Criterion.** Rank-two seam example with nonconstant diagonal.

**Source routes.** S133, S141, S146, S081, S155.

**Named anchors.** `seam_rank_le_two`; `seam_constant_diagonal`.

**Scope and remaining review.** The actual seam theorem gives rank at most two; the rank-two exact matrix and dedicated source-preserving negative reject unconditional rank one. Constant diagonal is an additional premise. The shared BoundaryWitnesses audit is not itself a seam receipt.

### E-02 — PARTIAL_SCOPE

**Criterion.** Approximation violates legal constraints or embedding changes form.

**Source routes.** S133, S107, S106, S079, S155.

**Named anchors.** `changed_embedding_loses_negativity`; `exact_but_illegal_approximant`.

**Scope and remaining review.** Numerical closeness does not discharge carrier legality or identity of quadratic forms.

### E-03 — PARTIAL_SCOPE

**Criterion.** Shell dimension2 or zero shift singular block.

**Source routes.** S133, S107, S106, S079, S155.

**Named anchors.** `dimension_two_retains_second_equation`; `zero_shift_does_not_supply_inverse`.

**Scope and remaining review.** One scalar shell equation or unjustified inverse loses necessary constraints.

### E-04 — PARTIAL_SCOPE

**Criterion.** b not in rangeH, or Gamma0=0.

**Source routes.** S133, S107, S106, S082, S155.

**Named anchors.** `incompatible_kernel_negative`; `source_vanishes_of_nonexceptional`.

**Scope and remaining review.** The original incompatibility theorem and nonzero-coefficient premise are now supplemented by a passing local 18-name probe and two genuine mathematical negatives: Γ=0 cancellation with source value 1, and positivity of an actual singular block without a preimage. Source/transcript readback is recorded separately. The old inverse mutant is not credited here; the new local controls are not PR126 CI or additions to the primary 17-control count.

### E-05 — PARTIAL_SCOPE

**Criterion.** Gram gap zero or positive summand masks negative block.

**Source routes.** S133, S141, S098, S080, S155.

**Named anchors.** `signedGram_witness_negative`; `gram_additional_component_negative`.

**Scope and remaining review.** The actual Gram theorem retains its strict gap and additional-component threshold. The dedicated full-Gram provider/control proves a positive summand can mask the signed negative block; the shared E-02/E-03 audit is not a Gram receipt.

## J.2. Later 11 claims

### Q1 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Actual-source discounted output discrepancy is bounded under explicit retention and source-domination assumptions.

**Source routes.** S050, S155.

**Named anchors.** `canonical_discounted_output_error`.

**Scope and remaining review.** The canonical discounted source wrapper requires probability mass one for ξ. Its domination assumptions do not supply a genuinely subprobability initial-mismatch witness. The separate NonstationaryProjected finite-common-submeasure theorem has a different interface.

### Q2 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Transfers an original constitutive comparison margin over the declared full B1 family when the required point witnesses hold.

**Source routes.** S049, S155.

**Named anchors.** `actual_canonical_discounted_original_margin`; `point_witness_output`.

**Scope and remaining review.** PointWitness/source and full B1 premises are not automatically satisfied by arbitrary compression.

### Q3 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Constructed exact-intertwining witness and exact rational positive/negative discounted-budget examples.

**Source routes.** S051, S155.

**Named anchors.** `exactKernelPointWitness`; `correct_frozen_discounted_budget`; `wrong_frozen_discounted_budget`.

**Scope and remaining review.** A fixture is an existence/control example, not a universal quotient theorem.

### M1 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Matches open- and closed-loop two-agent kernels for the stated measurable product-structure interventions.

**Source routes.** S025, S155.

**Named anchors.** `matched_closed_kernel_two`; `matched_open_kernel_two`.

**Scope and remaining review.** Conditional-product subclass only: do not infer unrestricted correlated strategic generators.

### M2 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Preserves matched initial path laws and original B1 constitutive margins under declared product-to-binary transport.

**Source routes.** S026, S155.

**Named anchors.** `matched_closed_loop_original_margin`; `matched_open_loop_original_margin`; `matched_closed_loop_all_initial_paths`; `matched_open_loop_all_initial_paths`.

**Scope and remaining review.** Requires matching intervention and comparison-set premises; not free representation invariance.

### M3 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Provides source-bound asymmetric and mixed-start counterexample/positive controls for the two-agent transport.

**Source routes.** S024, S155.

**Named anchors.** `matched_closed_worlds_both_frozen`; `wrong_asymmetric_input_change_is_detectable`; `matched_open_worlds_both_frozen`.

**Scope and remaining review.** Do not equate the examples with all heterogeneous information or multiagent protocols.

### N1 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Constructs the actual three-phase native cycle and exact six-state invariant-weight characterization.

**Source routes.** S071, S069, S155.

**Named anchors.** `phase_aware_invariant_weights`; `native_phase_aware_actual_true_mass`.

**Scope and remaining review.** The unique-cycle result is model-specific; not a generic stationary-law theorem.

### N2 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Connects actual infinite-path nonlinear scores with phase-aware policy and phase-blind comparisons.

**Source routes.** S070, S072, S155.

**Named anchors.** `native_phase_aware_actual_score_one`; `native_phase_blind_actual_le_five_sixths`; `native_phase_blind_actual_attained`; `native_actual_phase_aware_strictly_beats_phase_blind`; `actual_restricted_gap_of_identified_classes`.

**Scope and remaining review.** General phase-blind bound/gap uses explicit class-identification hypotheses; not global randomized/history policy optimality.

### N3 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Builds a Boolean nonlinear class evaluator with exact rational evaluation on certified C11 class laws.

**Source routes.** S067, S155.

**Named anchors.** `booleanClassFunctional`; `boolean_rational_objective_eq_actual`; `certified_boolean_score_exact`; `boolean_score_bounded`.

**Scope and remaining review.** Applies to the typed rational finite class family; must not score the stationary barycenter instead of classes.

### D8 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Shows a restricted certified intervention menu admits two named components and excludes their joint block in a concrete fixture.

**Source routes.** S055, S155.

**Named anchors.** `actual_restricted_menu_admits_both_components`; `actual_restricted_menu_rejects_joint`; `actual_restricted_menu_row_normalized`.

**Scope and remaining review.** Grammar relative; never infer global absence of a joint intervention.

### D9 — SOURCE_PRESENT_REVIEW_PENDING

**Criterion.** Demonstrates the actual mixed-initial nonlinear score differs from evaluating the barycenter in a two-absorbing-class model.

**Source routes.** S068, S155.

**Named anchors.** `actual_two_absorbing_full_path_mixture`; `actual_multichain_classwise_differs_from_barycenter`; `actual_mixed_nonlinear_half_not_barycenter`; `physically_distinct_classes_with_shared_descriptor`; `actual_mixed_initial_nonlinear_expectation`; `exact_two_absorbing_rational_scores`.

**Scope and remaining review.** The half-versus-five-sixths example does not itself discharge the distinct historical five-sixths-versus-one criterion.

## J.3. Complete source catalog

The displayed commit labels identify the exact source object. Full SHA-256 values, full qualified declaration names and frozen acceptance records are in `Guide_56_Case_Source_Crosswalk_v1.1.json`. A draft source has a local digest but no fabricated committed link.

| Source | Repository path | Commit role |
|:--|:--|:--|
| S001 | [PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixError.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixError.lean) | `5cee78c124c4` |
| S002 | [PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ConstitutiveQuasi/LocalizedPrefixExamples.lean) | `5cee78c124c4` |
| S003 | [PermanssonResearch/EconomicWitness/Constitution.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/EconomicWitness/Constitution.lean) | `5cee78c124c4` |
| S004 | [PermanssonResearch/EconomicWitness/ExactRegime.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/EconomicWitness/ExactRegime.lean) | `5cee78c124c4` |
| S005 | [PermanssonResearch/EconomicWitness/Regression.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/EconomicWitness/Regression.lean) | `5cee78c124c4` |
| S006 | [PermanssonResearch/Games/DiscountedVerification.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Games/DiscountedVerification.lean) | `5cee78c124c4` |
| S007 | [PermanssonResearch/GrammarRobust/BooleanOverlapFixture.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/GrammarRobust/BooleanOverlapFixture.lean) | `5cee78c124c4` |
| S008 | [PermanssonResearch/GrammarRobust/CompatibleOverlap.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/GrammarRobust/CompatibleOverlap.lean) | `5cee78c124c4` |
| S009 | [PermanssonResearch/GrammarRobust/LowerSetTransport.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/GrammarRobust/LowerSetTransport.lean) | `5cee78c124c4` |
| S010 | [PermanssonResearch/MultiAgent/AutonomousAEContinuumFixture.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/AutonomousAEContinuumFixture.lean) | `5cee78c124c4` |
| S011 | [PermanssonResearch/MultiAgent/AutonomousAEMechanisms.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/AutonomousAEMechanisms.lean) | `5cee78c124c4` |
| S012 | [PermanssonResearch/MultiAgent/AutonomousMarkedKernel.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/AutonomousMarkedKernel.lean) | `5cee78c124c4` |
| S013 | [PermanssonResearch/MultiAgent/AutonomousSupportClosure.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/AutonomousSupportClosure.lean) | `5cee78c124c4` |
| S014 | [PermanssonResearch/MultiAgent/BehavioralAutonomy.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/BehavioralAutonomy.lean) | `5cee78c124c4` |
| S015 | [PermanssonResearch/MultiAgent/CorrelatedMediator.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/CorrelatedMediator.lean) | `5cee78c124c4` |
| S016 | [PermanssonResearch/MultiAgent/FeasibleAnchors.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/FeasibleAnchors.lean) | `5cee78c124c4` |
| S017 | [PermanssonResearch/MultiAgent/FiniteMediation.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/FiniteMediation.lean) | `5cee78c124c4` |
| S018 | [PermanssonResearch/MultiAgent/FiniteProductTwo.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/FiniteProductTwo.lean) | `5cee78c124c4` |
| S019 | [PermanssonResearch/MultiAgent/M02ActualMarkedHistoryFixture.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/M02ActualMarkedHistoryFixture.lean) | `5cee78c124c4` |
| S020 | [PermanssonResearch/MultiAgent/MarkedStrategicPathCountermodel.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/MarkedStrategicPathCountermodel.lean) | `5cee78c124c4` |
| S021 | [PermanssonResearch/MultiAgent/MeasurableNatClockFixture.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/MeasurableNatClockFixture.lean) | `5cee78c124c4` |
| S022 | [PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/MeasurableNatClockTransport.lean) | `5cee78c124c4` |
| S023 | [PermanssonResearch/MultiAgent/MeasurableNatPrivateClock.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/MeasurableNatPrivateClock.lean) | `5cee78c124c4` |
| S024 | [PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedExamples.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedExamples.lean) | `5cee78c124c4` |
| S025 | [PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedProtocols.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedProtocols.lean) | `5cee78c124c4` |
| S026 | [PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/MeasurableProductTwoOriginalMarginClosure.lean) | `5cee78c124c4` |
| S027 | [PermanssonResearch/MultiAgent/NatPrivateClockTransport.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/NatPrivateClockTransport.lean) | `5cee78c124c4` |
| S028 | [PermanssonResearch/MultiAgent/PlayerSwapTransport.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/PlayerSwapTransport.lean) | `5cee78c124c4` |
| S029 | [PermanssonResearch/MultiAgent/PositiveMediationWitness.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/PositiveMediationWitness.lean) | `5cee78c124c4` |
| S030 | [PermanssonResearch/MultiAgent/PrivateClockTransport.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/PrivateClockTransport.lean) | `5cee78c124c4` |
| S031 | [PermanssonResearch/MultiAgent/StrictMA2Obstruction.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultiAgent/StrictMA2Obstruction.lean) | `5cee78c124c4` |
| S032 | [PermanssonResearch/MultipleLimit/GrowingBlockCounterexample.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultipleLimit/GrowingBlockCounterexample.lean) | `5cee78c124c4` |
| S033 | [PermanssonResearch/MultipleLimit/NonfiniteClock.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/MultipleLimit/NonfiniteClock.lean) | `5cee78c124c4` |
| S034 | [PermanssonResearch/Perturbation/ContractiveAdversaries.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Perturbation/ContractiveAdversaries.lean) | `5cee78c124c4` |
| S035 | [PermanssonResearch/Perturbation/FirstMomentInvariant.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Perturbation/FirstMomentInvariant.lean) | `5cee78c124c4` |
| S036 | [PermanssonResearch/Perturbation/PrimitiveProductTV.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Perturbation/PrimitiveProductTV.lean) | `5cee78c124c4` |
| S037 | [PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Perturbation/RegenerativeFirstMomentFactorization.lean) | `5cee78c124c4` |
| S038 | [PermanssonResearch/Perturbation/RegenerativeOccupationFactorization.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Perturbation/RegenerativeOccupationFactorization.lean) | `5cee78c124c4` |
| S039 | [PermanssonResearch/Probability/DependentHistoryCommonMass.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/DependentHistoryCommonMass.lean) | `5cee78c124c4` |
| S040 | [PermanssonResearch/Probability/DependentThreeStageSaturation.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/DependentThreeStageSaturation.lean) | `5cee78c124c4` |
| S041 | [PermanssonResearch/Probability/DiscountedInitialBudget.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/DiscountedInitialBudget.lean) | `5cee78c124c4` |
| S042 | [PermanssonResearch/Probability/FiniteKantorovichDuality.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/FiniteKantorovichDuality.lean) | `5cee78c124c4` |
| S043 | [PermanssonResearch/Probability/FiniteTransportRegression.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/FiniteTransportRegression.lean) | `5cee78c124c4` |
| S044 | [PermanssonResearch/Probability/FullPathProductTV.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/FullPathProductTV.lean) | `5cee78c124c4` |
| S045 | [PermanssonResearch/Probability/GoodHistoryVisit.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/GoodHistoryVisit.lean) | `5cee78c124c4` |
| S046 | [PermanssonResearch/Probability/KantorovichTV.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/KantorovichTV.lean) | `5cee78c124c4` |
| S047 | [PermanssonResearch/Probability/LocalizedFinitePrefix.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/LocalizedFinitePrefix.lean) | `5cee78c124c4` |
| S048 | [PermanssonResearch/Probability/LocalizedHistoryTV.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Probability/LocalizedHistoryTV.lean) | `5cee78c124c4` |
| S049 | [PermanssonResearch/Quotient/DiscountedCanonicalMarginClosure.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Quotient/DiscountedCanonicalMarginClosure.lean) | `5cee78c124c4` |
| S050 | [PermanssonResearch/Quotient/DiscountedCanonicalSourceWitness.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Quotient/DiscountedCanonicalSourceWitness.lean) | `5cee78c124c4` |
| S051 | [PermanssonResearch/Quotient/DiscountedCanonicalWitnessExamples.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Quotient/DiscountedCanonicalWitnessExamples.lean) | `5cee78c124c4` |
| S052 | [PermanssonResearch/Quotient/GeometricMargin.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Quotient/GeometricMargin.lean) | `5cee78c124c4` |
| S053 | [PermanssonResearch/Quotient/GeometricQuotient.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Quotient/GeometricQuotient.lean) | `5cee78c124c4` |
| S054 | [PermanssonResearch/Quotient/NonstationaryProjectedTransport.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Quotient/NonstationaryProjectedTransport.lean) | `5cee78c124c4` |
| S055 | [PermanssonResearch/ReverseSolver/AdaptiveGrammarAdmissionFixture.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/AdaptiveGrammarAdmissionFixture.lean) | `5cee78c124c4` |
| S056 | [PermanssonResearch/ReverseSolver/AdaptiveGrammarControl.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/AdaptiveGrammarControl.lean) | `5cee78c124c4` |
| S057 | [PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/AvoidResidenceMonitor.lean) | `5cee78c124c4` |
| S058 | [PermanssonResearch/ReverseSolver/BeliefMonitor.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/BeliefMonitor.lean) | `5cee78c124c4` |
| S059 | [PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/C11ReferenceExamples.lean) | `5cee78c124c4` |
| S060 | [PermanssonResearch/ReverseSolver/C11ReferenceStationaryFamily.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/C11ReferenceStationaryFamily.lean) | `5cee78c124c4` |
| S061 | [PermanssonResearch/ReverseSolver/FirstEntryMonitor.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/FirstEntryMonitor.lean) | `5cee78c124c4` |
| S062 | [PermanssonResearch/ReverseSolver/FlowRiskWitness.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/FlowRiskWitness.lean) | `5cee78c124c4` |
| S063 | [PermanssonResearch/ReverseSolver/InfiniteSafetyLeakage.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/InfiniteSafetyLeakage.lean) | `5cee78c124c4` |
| S064 | [PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/InfiniteSafetyOptimality.lean) | `5cee78c124c4` |
| S065 | [PermanssonResearch/ReverseSolver/MonitorEventOptimality.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/MonitorEventOptimality.lean) | `5cee78c124c4` |
| S066 | [PermanssonResearch/ReverseSolver/MonitorHistoryBridge.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/MonitorHistoryBridge.lean) | `5cee78c124c4` |
| S067 | [PermanssonResearch/ReverseSolver/NonlinearBooleanClassEvaluator.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/NonlinearBooleanClassEvaluator.lean) | `5cee78c124c4` |
| S068 | [PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/NonlinearMultichainAggregationFixture.lean) | `5cee78c124c4` |
| S069 | [PermanssonResearch/ReverseSolver/NonlinearPeriodThreeClassGeometry.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/NonlinearPeriodThreeClassGeometry.lean) | `5cee78c124c4` |
| S070 | [PermanssonResearch/ReverseSolver/NonlinearPeriodThreeExpectedScore.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/NonlinearPeriodThreeExpectedScore.lean) | `5cee78c124c4` |
| S071 | [PermanssonResearch/ReverseSolver/NonlinearPeriodThreeStationary.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/NonlinearPeriodThreeStationary.lean) | `5cee78c124c4` |
| S072 | [PermanssonResearch/ReverseSolver/NonlinearPhaseBlindClassGeometry.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/NonlinearPhaseBlindClassGeometry.lean) | `5cee78c124c4` |
| S073 | [PermanssonResearch/ReverseSolver/ResidenceSpecializationOptimality.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/ResidenceSpecializationOptimality.lean) | `5cee78c124c4` |
| S074 | [PermanssonResearch/ReverseSolver/SolverBoundaryWitnesses.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/SolverBoundaryWitnesses.lean) | `5cee78c124c4` |
| S075 | [PermanssonResearch/ReverseSolver/StationaryMenuOptimization.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/StationaryMenuOptimization.lean) | `5cee78c124c4` |
| S076 | [PermanssonResearch/ReverseSolver/StationaryOccupationObjective.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/StationaryOccupationObjective.lean) | `5cee78c124c4` |
| S077 | [PermanssonResearch/ReverseSolver/ThroughHorizonRiskFixture.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/ThroughHorizonRiskFixture.lean) | `5cee78c124c4` |
| S078 | [PermanssonResearch/ReverseSolver/ThroughHorizonRiskMonitor.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/ReverseSolver/ThroughHorizonRiskMonitor.lean) | `5cee78c124c4` |
| S079 | [PermanssonResearch/Specialized/BoundaryWitnesses.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Specialized/BoundaryWitnesses.lean) | `5cee78c124c4` |
| S080 | [PermanssonResearch/Specialized/GramSeparation.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Specialized/GramSeparation.lean) | `5cee78c124c4` |
| S081 | [PermanssonResearch/Specialized/SeamReduction.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Specialized/SeamReduction.lean) | `5cee78c124c4` |
| S082 | [PermanssonResearch/Specialized/SingularCompatibility.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/Specialized/SingularCompatibility.lean) | `5cee78c124c4` |
| S083 | [PermanssonResearch/StrategicWorld/ActionTrace.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/StrategicWorld/ActionTrace.lean) | `5cee78c124c4` |
| S084 | [PermanssonResearch/StrategicWorld/InformationBoundary.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/StrategicWorld/InformationBoundary.lean) | `5cee78c124c4` |
| S085 | [PermanssonResearch/X1/Comparison.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/X1/Comparison.lean) | `5cee78c124c4` |
| S086 | [PermanssonResearch/X1/ExactMargins.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/X1/ExactMargins.lean) | `5cee78c124c4` |
| S087 | [PermanssonResearch/X1/ExactMatrixTables.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/X1/ExactMatrixTables.lean) | `5cee78c124c4` |
| S088 | [PermanssonResearch/X1/ExactTerminalTables.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/X1/ExactTerminalTables.lean) | `5cee78c124c4` |
| S089 | [PermanssonResearch/X1/FullStrategyCertificate.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/X1/FullStrategyCertificate.lean) | `5cee78c124c4` |
| S090 | [PermanssonResearch/X1/InterventionNumericalBridge.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/X1/InterventionNumericalBridge.lean) | `5cee78c124c4` |
| S091 | [PermanssonResearch/X1/StrategyRegression.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/X1/StrategyRegression.lean) | `5cee78c124c4` |
| S092 | [PermanssonResearch/X1/TiedStartDomainFixture.lean](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/PermanssonResearch/X1/TiedStartDomainFixture.lean) | `5cee78c124c4` |
| S093 | [verification/research/test_a2_primitive_tv.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_a2_primitive_tv.py) | `5cee78c124c4` |
| S094 | [verification/research/test_a3_contractive.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_a3_contractive.py) | `5cee78c124c4` |
| S095 | [verification/research/test_b02_actual_original_margin_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_b02_actual_original_margin_lean.py) | `5cee78c124c4` |
| S096 | [verification/research/test_b02_local_nonisomorphic_margin_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_b02_local_nonisomorphic_margin_lean.py) | `5cee78c124c4` |
| S097 | [verification/research/test_d2_residence.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_d2_residence.py) | `5cee78c124c4` |
| S098 | [verification/research/test_e05_full_gram_masking_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_e05_full_gram_masking_lean.py) | `5cee78c124c4` |
| S099 | [verification/research/test_e1_approx_quotient.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_e1_approx_quotient.py) | `5cee78c124c4` |
| S100 | [verification/research/test_f03_actual_infeasible_strict_anchor_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_f03_actual_infeasible_strict_anchor_lean.py) | `5cee78c124c4` |
| S101 | [verification/research/test_f1_multiagent_protocols.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_f1_multiagent_protocols.py) | `5cee78c124c4` |
| S102 | [verification/research/test_final04_source_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final04_source_lean.py) | `5cee78c124c4` |
| S103 | [verification/research/test_final05_measurable_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final05_measurable_lean.py) | `5cee78c124c4` |
| S104 | [verification/research/test_final06_phaseblind_original.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final06_phaseblind_original.py) | `5cee78c124c4` |
| S105 | [verification/research/test_final_actual_product_reporting_false_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final_actual_product_reporting_false_lean.py) | `5cee78c124c4` |
| S106 | [verification/research/test_final_closure_existing_false_semantics_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final_closure_existing_false_semantics_lean.py) | `5cee78c124c4` |
| S107 | [verification/research/test_final_closure_missing_original_positives.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final_closure_missing_original_positives.py) | `5cee78c124c4` |
| S108 | [verification/research/test_final_closure_more_false_semantics_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final_closure_more_false_semantics_lean.py) | `5cee78c124c4` |
| S109 | [verification/research/test_final_d08_admission.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final_d08_admission.py) | `5cee78c124c4` |
| S110 | [verification/research/test_final_d09_multichain.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final_d09_multichain.py) | `5cee78c124c4` |
| S111 | [verification/research/test_final_original_chronological_false_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final_original_chronological_false_lean.py) | `5cee78c124c4` |
| S112 | [verification/research/test_final_original_risk_belief_false_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_final_original_risk_belief_false_lean.py) | `5cee78c124c4` |
| S113 | [verification/research/test_lane_b2_sequential_effects.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_lane_b2_sequential_effects.py) | `5cee78c124c4` |
| S114 | [verification/research/test_lane_c11_stationary.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_lane_c11_stationary.py) | `5cee78c124c4` |
| S115 | [verification/research/test_localized_prefix_compiler.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_localized_prefix_compiler.py) | `5cee78c124c4` |
| S116 | [verification/research/test_m02_actual_history_kernel_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_m02_actual_history_kernel_lean.py) | `5cee78c124c4` |
| S117 | [verification/research/test_m02_marked_actual_source_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_m02_marked_actual_source_lean.py) | `5cee78c124c4` |
| S118 | [verification/research/test_monitor_stationary_closures.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_monitor_stationary_closures.py) | `5cee78c124c4` |
| S119 | [verification/research/test_next03_asymmetric_common_swap_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next03_asymmetric_common_swap_lean.py) | `5cee78c124c4` |
| S120 | [verification/research/test_next03_dependent_three_stage.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next03_dependent_three_stage.py) | `5cee78c124c4` |
| S121 | [verification/research/test_next03_m02_marked_coupling.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next03_m02_marked_coupling.py) | `5cee78c124c4` |
| S122 | [verification/research/test_next03_positive_mediation.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next03_positive_mediation.py) | `5cee78c124c4` |
| S123 | [verification/research/test_next03_stochastic_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next03_stochastic_lean.py) | `5cee78c124c4` |
| S124 | [verification/research/test_next03_tied_start_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next03_tied_start_lean.py) | `5cee78c124c4` |
| S125 | [verification/research/test_next04_original_margin.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next04_original_margin.py) | `5cee78c124c4` |
| S126 | [verification/research/test_next04_original_margin_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next04_original_margin_lean.py) | `5cee78c124c4` |
| S127 | [verification/research/test_next04_projection_arithmetic.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next04_projection_arithmetic.py) | `5cee78c124c4` |
| S128 | [verification/research/test_next06_committed_path_law.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next06_committed_path_law.py) | `5cee78c124c4` |
| S129 | [verification/research/test_next06_d08_joint_only_compiler.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next06_d08_joint_only_compiler.py) | `5cee78c124c4` |
| S130 | [verification/research/test_next06_overlap_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next06_overlap_lean.py) | `5cee78c124c4` |
| S131 | [verification/research/test_next06_reachable_completion_belief.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_next06_reachable_completion_belief.py) | `5cee78c124c4` |
| S132 | [verification/research/test_paper_autonomy_ae_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_autonomy_ae_lean.py) | `5cee78c124c4` |
| S133 | [verification/research/test_paper_closure_boundaries.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_closure_boundaries.py) | `5cee78c124c4` |
| S134 | [verification/research/test_paper_infinite_safety_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_infinite_safety_lean.py) | `5cee78c124c4` |
| S135 | [verification/research/test_paper_information_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_information_lean.py) | `5cee78c124c4` |
| S136 | [verification/research/test_paper_invariant_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_invariant_lean.py) | `5cee78c124c4` |
| S137 | [verification/research/test_paper_measurable_clock_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_measurable_clock_lean.py) | `5cee78c124c4` |
| S138 | [verification/research/test_paper_metric_coupling_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_metric_coupling_lean.py) | `5cee78c124c4` |
| S139 | [verification/research/test_paper_nonfinite_counterexample_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_nonfinite_counterexample_lean.py) | `5cee78c124c4` |
| S140 | [verification/research/test_paper_risk_lp_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_risk_lp_lean.py) | `5cee78c124c4` |
| S141 | [verification/research/test_paper_specialized_boundary_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_specialized_boundary_lean.py) | `5cee78c124c4` |
| S142 | [verification/research/test_paper_strategy_economic_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_strategy_economic_lean.py) | `5cee78c124c4` |
| S143 | [verification/research/test_paper_through_risk_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_through_risk_lean.py) | `5cee78c124c4` |
| S144 | [verification/research/test_paper_x1_lean_closure.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_x1_lean_closure.py) | `5cee78c124c4` |
| S145 | [verification/research/test_paper_x1_matrix_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_paper_x1_matrix_lean.py) | `5cee78c124c4` |
| S146 | [verification/research/test_pr113_semantic_boundary_candidates.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_pr113_semantic_boundary_candidates.py) | `5cee78c124c4` |
| S147 | [verification/research/test_pr113_semantic_factorization_candidates.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_pr113_semantic_factorization_candidates.py) | `5cee78c124c4` |
| S148 | [verification/research/test_pr113_semantic_second_candidates.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_pr113_semantic_second_candidates.py) | `5cee78c124c4` |
| S149 | [verification/research/test_pr113_semantic_structural_candidates.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_pr113_semantic_structural_candidates.py) | `5cee78c124c4` |
| S150 | [verification/research/test_q05_actual_atom_closure_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_q05_actual_atom_closure_lean.py) | `5cee78c124c4` |
| S151 | [verification/research/test_q05_actual_source_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_q05_actual_source_lean.py) | `5cee78c124c4` |
| S152 | [verification/research/test_q05_nonidentity_source_fixture.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_q05_nonidentity_source_fixture.py) | `5cee78c124c4` |
| S153 | [verification/research/test_q05_original_margin_adapter_lean.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_q05_original_margin_adapter_lean.py) | `5cee78c124c4` |
| S154 | [verification/research/test_x1_commons.py](https://github.com/HMarcusWH/PermanssonLean/blob/5cee78c124c46a551e70bea92056efdcf5e6f292/verification/research/test_x1_commons.py) | `5cee78c124c4` |
| S155 | [verification/research/tranche10_all56_named_source_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_all56_named_source_receipt_addendum.lean) | `23e6a57b3813` |
| S156 | [verification/research/tranche10_b02_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_b02_scope_receipt_addendum.lean) | `23e6a57b3813` |
| S157 | [verification/research/tranche10_d05_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_d05_scope_receipt_addendum.lean) | `23e6a57b3813` |
| S158 | [verification/research/tranche10_m02_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_m02_scope_receipt_addendum.lean) | `23e6a57b3813` |
| S159 | [verification/research/tranche10_q03_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_q03_scope_receipt_addendum.lean) | `23e6a57b3813` |
| S160 | [verification/research/tranche10_q04_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche10_q04_scope_receipt_addendum.lean) | `23e6a57b3813` |
| S161 | [verification/research/tranche6_q05_whole_path_identification.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche6_q05_whole_path_identification.lean) | `23e6a57b3813` |
| S162 | [verification/research/tranche7_q05_original_margin_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche7_q05_original_margin_addendum.lean) | `23e6a57b3813` |
| S163 | [verification/research/tranche8_d09_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche8_d09_scope_receipt_addendum.lean) | `23e6a57b3813` |
| S164 | [verification/research/tranche8_f01_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche8_f01_scope_receipt_addendum.lean) | `23e6a57b3813` |
| S165 | [verification/research/tranche9_d06_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche9_d06_scope_receipt_addendum.lean) | `23e6a57b3813` |
| S166 | [verification/research/tranche9_d08_scope_receipt_addendum.lean](https://github.com/HMarcusWH/PermanssonLean/blob/23e6a57b381363cf20751a18337ca927cd393a6c/verification/research/tranche9_d08_scope_receipt_addendum.lean) | `23e6a57b3813` |


\newpage

# Appendix K — Additive edition change record

**Historical v1.1 edition record — 20 November 2026, Europe/Stockholm.** Canonical v1.0 bytes remain unchanged. The following table records the original v1.1 changes, with the ED-04 explanation clarified in v1.1.1. The new proofreading edition is recorded separately in K.1.

| Change | Scope | Reason |
|:--|:--|:--|
| ED-01 | Edition text | A new edition is assembled; canonical v1.0 is unchanged. |
| ED-02 | Edition text | Correct local edition date after midnight in Stockholm; historical experiment dates retained. |
| ED-03 | Edition text | Separate current edition/source evidence from preserved historical release and independent decisions. |
| ED-04 | Edition text | Replace the historical unreleased label “finite-cq1-certificate” with the released command `finite-cq1`, as exposed by the pinned registry and CLI. |
| ED-05 | Edition text | Avoid presenting an earlier execution as a fresh v1.1 run. |
| ED-06 | Edition text | Preserve the receipt while identifying its actual experiment. |
| ED-07 | Edition text | The six listed workflow runs and file totals concern 89ac97cb, not latest source. |
| ED-08 | Edition text | The historical unfinished-unified-guide description is stale after canonical v1.0 completion. |
| ED-09 | Edition text | Identify historical gate language and separate the current v1.1 gate. |
| ED-10 | Edition text | Preserve the original 89ac source/publication statement without representing it as the latest source ledger. |
| ED-11 | Edition text | The retained v0.9.2 recommendation is historical editorial provenance, not this edition's label. |
| ED-12 | Edition text | Keep the exact installed-wheel experiment and its limitations distinct from new research proof receipts. |
| ED-15 | Edition text | Qualify the earlier no-local-compiler statement to the installed-application experiment; v1.1 has separate new research receipts. |
| ED-16 | Edition text | A04 must not imply that the new research-source probes were never compiled. |
| ED-17 | Edition text | Keep the earlier no-source-change statement in its historical editorial scope; v1.1 integrates new proof sources. |
| ED-23 | Edition text | The v0.1.8 artifact is a versioned submission/editorial source; the guide must not imply an external publication decision. |
| ED-24 | Edition text | Separate the Volumes A–B scope paragraph from its source blockquote so the PDF does not print literal greater-than markers. |
| ED-18 | F04 | Distinguish completed bounded repairs and clean committed replay from remaining literal-criterion/control mapping, independent decisions and publication receipts. Preserve the separate zero-control scope of the all56 probe and the 154 existing method routes. |
| ED-19 | C07 | State the D-05 alive initial state at time zero before any transitions, without calling the initial state/history pair empty. |
| ED-20 | C08 | Distinguish the identity component map from its identity lift on component subsets. |
| ED-21 | C14 | Name IsExogenousCommon and both strict-anchor/support-agreement premises explicitly. |
| ED-22 | Edition text | Avoid duplicate terminal punctuation after injected receipt status paragraphs. |
| ED-25 | Appendix J | Integrate the 20 November 2026 internal 56-case clause map; distinguish A-01 dual supremum and primal attainment from an unlocated dual witness, A-04 interfaces from an unlocated one-failed-factorization model, correct E-01/E-04/E-05 and D-07 evidence routing, and retain later Q1's probability-mass premise on the initial common witness. No source or independent-acceptance promotion. |
| ED-26 | Appendix J | Record the separately evidenced E-04 local source-bound repair for zero-coefficient cancellation and missing-preimage positivity. Its 18-name/two-control receipt is separate from PR126 CI, the primary 17 controls and independent case acceptance. |
| ED-27 | Appendix J | Record the complete-baseline PASS and genuine nonbottom-class rejection by the unchanged C11 Python checker, with detached source/transcript readback. Preserve its local Python trust boundary and the original Lean/CI/count/acceptance claims. |
| ED-28 | F04; Appendix J | Bind the current PR126 method joins, preserve prior-main chronology and report the 105-clause internal map as completed. The original 149 selectors/154 owned routes, supplemental overlaps and D-02 additions retain separate identities; independent adequacy remains unapproved. |
| IN-B06 | B06 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-B07 | B07 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-C01 | C01 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-C06 | C06 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-C07 | C07 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-C08 | C08 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-C09 | C09 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-C14 | C14 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-E02 | E02 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-E03 | E03 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-E06 | E06 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| IN-F04 | F04 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| REF-B08 | B08 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| REF-C10 | C10 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| REF-D05.1 | D05.1 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| REF-D05.2 | D05.2 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| REF-D05.3 | D05.3 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| REF-D06.1 | D06.1 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| REF-D06.2 | D06.2 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| REF-E07 | E07 | Integrate the dated source-qualified example or cross-reference in its chapter. |
| ED-13 | E02.6 | State the receiptless finite-world candidate exception and distinguish command names from candidate families. |
| ED-14 | Appendix J | Supply the full 56-case source crosswalk while preserving all frozen decision records. |

The associated build manifest records the canonical input, insert hashes, added-source identity, output hashes and structural checks. PDF rendering and visual inspection are a separate publication step; this builder records no invented page count or PDF QA result.


## K.1 Proofread edition v1.1.1 — 20 November 2026

This edition follows an end-to-end text, source and visual audit of all 125 pages of the delivered v1.1 PDF. The attached proofreading notes were treated as hypotheses to verify. The reported hash substitutions, missing operators and duplicated CLI argument were not reproduced in the exact source/PDF. Pages 118–125 were present and were inspected directly. The audit records both confirmed changes and rejected suggestions.

The verified corrections concern mandatory schema dependencies; Boolean/action naming; fixed-model perturbation numbering; the reduced chain used for recurrent-class absorption; first-step versus second-step risk objectives; checker algorithm separation and shared dependencies; numeric command versus candidate-family names; fresh output paths; hash versus signature terminology; explicit source-path bases; profile-specific verification language; nonnegative persistence premises; source attribution and weekly cadence; completed versus future publication work; and consistent appendix labels. Short code atoms are kept together in the PDF where possible. No worked numerical result, published hash, frozen case disposition or CLI invocation was changed.

The accompanying `Permansson_Proofreading_Addendum_v1.1.1_2026-11-20.md` and `Proofread_Changes_v1.1.1.json` give the audit result and exact replacements. The full delivery also includes the original page-range reviews, supplied-claim dispositions, source checks, command checks, renderer inputs and a new PDF QA record. The separate Core 24 complete-header addendum repairs two truncated historical theorem-header extracts without changing the source theorems or original companion bytes.

**Fresh executable check.** A new Linux CPython 3.12 source installation at commit `c5a36cd6189e2a249d5f4bc11f31698917dc8b10` passed the official 28-example numerical walkthrough. Twenty-one candidates were emitted, byte-rechecked and rejected after tampering; four primary examples remained numerical-only because of reflection bounds. This was a new source-installation check, not a new reproduction of the published wheel bytes. No Lean compiler run or independent case acceptance is claimed by this proofreading pass. Historical release and research compiler receipts above retain their original scope.
