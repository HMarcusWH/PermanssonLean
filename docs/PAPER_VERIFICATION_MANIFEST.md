# Paper verification manifest - Permansson v0.1.8

## Release identity

- Paper: **Permansson Regimes: A General Framework for Strategic Dynamics Beyond Equilibrium**
- Version: **v0.1.8**
- Date: **23 September 2026**
- PDF SHA-256: `0fc957f19ac95bd1e3cced5558dc696930cf898714c5cd6dbbc9b928c69663f5`
- TeX SHA-256: `a181b5aa1236376134f562a76abbbe090f378d521aa8f33df69f746e5adba71c`
- Frozen v0.1.7 post-proofread test archive SHA-256: `7ab578c928a2918e09846b9f1c425f5a6c07b5b5dd0a0c8728662eebcb69a15a`

## Formalization snapshot

- Immutable mathematical snapshot: `c018f79ea4ce46f4f679ad5bca254509778fc53c`
- Lean: `4.34.0`
- mathlib: `v4.34.0`
- Green CI run: `35808810682`
- CI job: `107015473604`
- CI checks: axiom audit, `lake build`, and rejection of `sorry`, `admit`, and source-level custom `axiom` declarations.

The cited commit is the formal-code snapshot used by the paper. This provenance file may live in a later metadata-only commit without changing that mathematical snapshot.

## Verification layers

The frozen executable archive records 85/85 historical executions, 16/16 baseline compatibility checks, and 3240/3240 checks in Runs 17-30. Runs 17-30 were rerun again during the v0.1.8 boarding audit and all 14 numbered runs returned zero.

The original v0.1.8 release gate (Run 31) passed 42/42 checks. After final illustration review, Figure 1 was corrected to match the actual typed dependency graph and Figure 3 was tightened to state the exact finite-persistence gate and QSD certification relation. A follow-up figure-correction gate (Run 32) passed 45/45 checks, including the new artifact hashes, exact figure-source semantics, cold TeX compilation, PDF text identity, equation-number continuity, and preservation of the Section 11.5 non-promotion boundary.

## Claim boundary

The machine-checked completion claim is the promoted discrete GR/PR mathematical core through Proposition 8.1. It does not extend to empirical validity, causal identification, provenance quality, statistical adequacy, literature priority, continuous-time/set-valued/nonautonomous extensions, or the non-core Section 11.5 finite-certificate/rigidity programme.
