# PermanssonLean

Formal verification and executable-validation companion for **Permansson Regimes: A General Framework for Strategic Dynamics Beyond Equilibrium v0.1.8**.

The repository machine-checks the paper's discrete-time GR/PR mathematical core in Lean 4. It is a theorem-level companion to the paper, not a substitute for its empirical, identification, provenance, or literature-priority disciplines.

## Toolchain

- Lean 4.34.0
- mathlib 4.34.0

Both are pinned.

## Formalization strategy

The build follows mathematical dependency rather than paper page order:

1. typed strategic-world kernels `α`, `P`, and `U`;
2. induced joint kernel `K_{𝔊,P}`;
3. canonical path law, well-posedness, and enlarged-state reduction;
4. Generated Regime semantics, Polish descriptor support, exact persistence, and killed-kernel calculus;
5. finite-persistence and QSD-certified quasi-regime machinery;
6. typed intervention grammar;
7. generalized Permansson constitution;
8. constitutive margins, perturbation robustness, and the finite-horizon TV envelope;
9. intervention-family and representation equivalence;
10. type-respecting intervention-compatible quotient preservation;
11. Paper-I EGR embedding and conservative PR recovery;
12. grounded confirmatory semantics;
13. recorded-action decoding and action-sensitive Paper-I recovery;
14. Section-7 non-identification, constitutive non-invariance, and nuisance-padding witnesses;
15. Proposition 8.1's explicit period-two Exact GR under almost-sure weak occupation convergence.

See [docs/FORMALIZATION_MAP.md](docs/FORMALIZATION_MAP.md) for the source-to-Lean theorem ledger and claim firewall.

## Status discipline

- **PROVED** — accepted by Lean on the pinned toolchain.
- **DEFINED** — a paper object is represented as data/structure and has no separate theorem obligation merely for existing.
- **SCAFFOLDED** — a partial interface exists but a stated theorem obligation remains incomplete.
- **OPEN** — a formal-core claim has not yet been represented in Lean.
- **NON-CORE / OUTSIDE FORMALIZED CORE** — explicitly outside the universal GR/PR theorem set, such as the specialized finite-certificate/rigidity material collected in Appendix E.
- **EMPIRICAL / OUT OF SCOPE** — depends on data, scientific identification, provenance, statistics, or literature priority rather than pure formal derivation.

A green build certifies the Lean declarations that are actually present. It does not validate empirical inputs, causal identification, novelty, or material outside the formalized theorem scope.

## Current coverage

The numbered theorem/proposition/corollary/definition obligations in the **v0.1.8 discrete formal core through Proposition 8.1** have corresponding Lean closure. The checked surface includes:

- joint-process construction and uniqueness plus Proposition 3.2 enlarged-state reduction;
- Proposition 4.1a Polish descriptor-space / bounded-Lipschitz weak-convergence support;
- exact invariance, killed-kernel survival, finite persistence, exit-time/Green identities, and the `q^L` lower bound;
- Definition 4.3 Exact GR and Definition 4.4a / Proposition 4.4b QSD certification;
- generalized PR constitution, uniform margins, Proposition 5.2 / Corollary 5.3 robustness, and Proposition 5.4's finite-horizon TV envelope;
- Theorems 6.1–6.2 conservative Paper-I recovery for world-only, recorded-action, uniform-margin, and grounded-confirmatory protocols;
- Proposition 7.1, Theorems 7.2–7.3, Propositions 7.4/7.4a, Theorem 7.4b, and Proposition 7.5;
- Proposition 8.1's literal two-state periodic Exact GR under `ConvergenceMode.almostSureWeak`.

The specialized scalar-defect / finite-detection / first-bad / singular-compatibility material in Appendix E remains deliberately **NON-CORE / OUTSIDE FORMALIZED CORE** unless and until a natural Permansson interface and direct theorem are supplied. Continuous-time, set-valued, nonautonomous, and application-specific extensions remain outside the discrete core completion claim.

## Build

```bash
lake update
lake build
```

CI additionally audits the root import graph and rejects `sorry`, `admit`, and source-level custom `axiom` declarations.

## Executable verification

The repository now carries the inspectable Python verification source in addition to Lean:

- `verification/destructive/suite/` — destructive/regression Runs 17–30;
- `verification/v0.1.8_release_gate/` — release gates 31–34, with Runs 31–33 retained as historical gates and Run 34 as the editorial-final package gate;
- `verification/lean/` — exact paper-to-Lean crosswalk and CI provenance;
- `verification/repository_gate.py` — repository-level source/provenance synchronization check.

GitHub Actions runs the Lean build independently from the executable Python verification workflow. This preserves the epistemic distinction between theorem checking and destructive/regression testing.

See [verification/README.md](verification/README.md) for rerun instructions.

## Paper release provenance

The final editorial-clean v0.1.8 manuscript is tied to immutable formal-code snapshot `c018f79ea4ce46f4f679ad5bca254509778fc53c` and green CI run `35808810682`.

Final artifact identifiers:

- PDF SHA-256: `24f7dd43c8996b6fc8bedf708704969ba2124e159783bbd2ded45db61525df54`
- TeX SHA-256: `8235f6140bca33e7e3f0e96b4fd3aa2431c476fbdaf7c5d86d6d0b703ea54ed9`
- frozen destructive archive SHA-256: `7ab578c928a2918e09846b9f1c425f5a6c07b5b5dd0a0c8728662eebcb69a15a`
- Windows-safe destructive suite SHA-256: `864e2fec88b345194b0a9dc4ce9431e6a9a754eb88adea75fb8835b6244f41c3`
- final Windows-safe release ZIP SHA-256: `66a13d3d4ea6854d38a6a32fe8b7946cbc290c62484b654dc02e0317039faf25`
- final release gate: Run 34, **58/58 PASS**

Exact release metadata and claim boundaries are recorded in [docs/PAPER_VERIFICATION_MANIFEST.md](docs/PAPER_VERIFICATION_MANIFEST.md) and [docs/releases/v0.1.8.json](docs/releases/v0.1.8.json).
