# PermanssonLean

Formal verification project for **Permansson Regimes: Strategic Dynamics Beyond Equilibrium**.

The target paper is Permansson Regimes v0.1.7. The repository is intended to machine-check the semantic kernel of the framework in Lean 4 rather than merely replay finite tests.

## Toolchain

- Lean 4.34.0
- mathlib 4.34.0

Both are pinned.

## Formalization strategy

We build by dependency, not by paper page order:

1. typed strategic-world kernels `α`, `P`, `U`;
2. induced joint kernel `K_{𝔊,P}`;
3. path law and well-posedness;
4. Generated Regime definitions and exact persistence;
5. killed-kernel finite persistence;
6. typed intervention grammar;
7. Permansson constitution;
8. constitutive margins and robustness;
9. intervention-family equivalence;
10. quotient preservation;
11. EGR embedding;
12. optional QSD and original-math research lanes.

See [docs/FORMALIZATION_MAP.md](docs/FORMALIZATION_MAP.md) for the theorem ledger and status firewall.

## Status discipline

- **PROVED** means checked by Lean on the pinned toolchain.
- **SCAFFOLDED** means the type/definition exists but the theorem is not yet formalized.
- **OPEN** means no Lean formalization yet.
- **EMPIRICAL / OUT OF SCOPE** covers scientific identification, input-data validity, and literature-priority claims.

A green build is not a proof of anything marked OPEN.

## Build

```bash
lake update
lake build
```

The current proved spine reaches through exact persistence, killed-kernel survival calculus, typed interventions, generalized Permansson constitution, quantitative constitutive robustness, frozen intervention-family equivalence, type-respecting intervention-compatible quotient preservation, and the canonical Paper-I EGR → Exact-GR embedding with conservative pointwise/uniform world-path PR recovery. The next unresolved semantic boundary is the grounded confirmatory layer; recorded-action decode transport, Proposition 5.4's finite-horizon kernel-to-path TV envelope, BL metrization, and the optional QSD layer remain explicit open lanes.
