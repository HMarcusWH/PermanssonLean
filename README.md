# PermanssonLean

Formal verification project for **Permansson Regimes: Strategic Dynamics Beyond Equilibrium v0.1.7**.

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
- **OPEN** — a promoted formal claim has not yet been represented in Lean.
- **NON-CORE / NOT PROMOTED** — explicitly outside the v0.1.7 universal GR/PR core, such as the Section 11.5 rigidity programme.
- **EMPIRICAL / OUT OF SCOPE** — depends on data, scientific identification, provenance, statistics, or literature priority rather than pure formal derivation.

A green build certifies the Lean declarations that are actually present. It does not validate empirical inputs, causal identification, novelty, or any non-promoted research programme.

## Current coverage

The numbered theorem/proposition/corollary/definition obligations in the intended **v0.1.7 discrete formal core through Proposition 8.1** now have corresponding Lean closure. The checked surface includes:

- joint-process construction and uniqueness plus Proposition 3.2 enlarged-state reduction;
- Proposition 4.1a Polish descriptor-space / bounded-Lipschitz weak-convergence support;
- exact invariance, killed-kernel survival, finite persistence, exit-time/Green identities, and the `q^L` lower bound;
- Definition 4.3 Exact GR and Definition 4.4a / Proposition 4.4b QSD certification;
- generalized PR constitution, uniform margins, Proposition 5.2 / Corollary 5.3 robustness, and Proposition 5.4's finite-horizon TV envelope;
- Theorems 6.1–6.2 conservative Paper-I recovery for world-only, recorded-action, uniform-margin, and grounded-confirmatory protocols;
- Proposition 7.1, Theorems 7.2–7.3, Propositions 7.4/7.4a, Theorem 7.4b, and Proposition 7.5;
- Proposition 8.1's literal two-state periodic Exact GR under `ConvergenceMode.almostSureWeak`.

The Section 11.5 scalar-defect / finite-detection / first-bad / singular-compatibility programme remains deliberately **NON-CORE / NOT PROMOTED** until a natural Permansson interface and paper theorem are supplied. Continuous-time, set-valued, nonautonomous, and application-specific extensions remain outside the discrete core completion claim.

## Build

```bash
lake update
lake build
```

CI additionally audits the root import graph and rejects `sorry`, `admit`, and source-level custom `axiom` declarations.

## Paper release provenance

The v0.1.8 manuscript is tied to the immutable formal-code snapshot `c018f79ea4ce46f4f679ad5bca254509778fc53c` and green CI run `35808810682`. Exact PDF/TeX/test-archive hashes and the release claim boundary are recorded in [docs/PAPER_VERIFICATION_MANIFEST.md](docs/PAPER_VERIFICATION_MANIFEST.md); machine-readable release metadata is in [docs/releases/v0.1.8.json](docs/releases/v0.1.8.json). The distribution metadata also records the Windows-safe release repack; it changes archive layout only and does not change the manuscript, Lean snapshot, frozen destructive archive, or theorem claims.
