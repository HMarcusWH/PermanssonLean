# Permansson v0.1.7 — Post-proofread full rerun

**Overall:** PASS

## Frozen v0.1.6 controls

- Historical stress/control executions: **85/85 PASS**
- Baseline/backward-compatibility validation: **16/16 PASS**

## Strengthened v0.1.7 Runs 17–30

- Total checks: **3240/3240 PASS**
- Previous suite: 3183 checks
- Added after theorem-contract proofreading: **57 checks**

| Run | Checks | Result | Target |
|---:|---:|:---:|---|
| 17 | 29 | PASS | Killed-kernel exact persistence |
| 18 | 21 | PASS | QSD existence/uniqueness/pathology guards + finite-persistence gate |
| 19 | 15 | PASS | Polish descriptor-space weakening; individual tightness vs uniform tightness |
| 20 | 263 | PASS | Finite-horizon kernel perturbation accumulation + TV convention boundaries |
| 21 | 13 | PASS | Infinite-horizon robustness failure modes |
| 22 | 2004 | PASS | Constitutive margin-preservation theorem |
| 23 | 9 | PASS | Indexed typed intervention-family signature equivalence and omissions |
| 24 | 77 | PASS | Intervention-compatible typed quotient/lumpability theorem attacks |
| 25 | 221 | PASS | Scalar-defect architecture and necessity attacks |
| 26 | 11 | PASS | Persistent finite-detection architecture |
| 27 | 153 | PASS | First-bad quotient and Schur reduction |
| 28 | 59 | PASS | Singular kernel/range compatibility |
| 29 | 313 | PASS | Specialized novel-math theorem architectures |
| 30 | 52 | PASS | Integrated post-proofread v1.7 mutation/source gate and fresh v1.6 controls |

## Newly strengthened contracts

- QSD existence no longer substitutes for the uniform finite-persistence gate.
- Polish descriptor spaces distinguish individual tightness from uniform tightness of families/sequences.
- Total variation uses the explicit `sup_A` / half-L1 convention, including factor-of-two and epsilon boundary attacks.
- Intervention signatures are indexed families; duplicate labels remain distinct and matching must preserve target/type grammar.
- Quotients must be type-respecting product maps; every frozen intervention kernel and `B, B0, h, g, psi` must descend as required; `B1` admissibility and common property metric are independently checked.
- Historical Run 30 audited these contracts directly against the exact final v0.1.7 LaTeX source. Repository CI freezes the same source contract in a compact fixture while the full historical artifact remains in the frozen release package.

## Conclusion

All numbered Runs 01–30 were green under the strengthened post-proofread contract. Runs 17–30 remain directly executable from this repository.
