# Paper verification manifest - Permansson v0.1.8

## Release identity

- Paper: **Permansson Regimes: A General Framework for Strategic Dynamics Beyond Equilibrium**
- Version: **v0.1.8**
- Date: **23 September 2026**
- PDF SHA-256: `e71f0c46499fc9e72fdd5f048e2293e29986b573ecc4cf8e0b297afd455f690c`
- TeX SHA-256: `a0f6e7e3809f246ff1357e94947f343d08a91ebe5c90e7c7fee5db4eb7b306e0`
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

The original v0.1.8 release gate (Run 31) passed 42/42 checks. Figure 1 was then corrected to match the actual typed dependency graph and Figure 3 was tightened to state the exact finite-persistence gate and QSD certification relation; Run 32 passed 45/45 checks. A final Figure 3 layout freeze removed the duplicated internal title, raised and spread the boxes, moved the implication labels clear of the arrows, and changed the left label to "for every finite L" without changing theorem content. Run 33 passed 50/50 checks, including artifact hashes, exact figure-source semantics, cold TeX compilation, PDF text identity, equation-number continuity, and preservation of the Section 11.5 non-promotion boundary.

## Distribution packaging

The first portability-fixed outer release ZIP was structurally valid under standard ZIP tools, but it duplicated the expanded destructive suite inside the release tree. That created archive member paths up to 306 characters, which can cause Windows Explorer's built-in Compressed Folders handler to reject the ZIP as invalid under legacy path handling.

A Windows-safe distribution derivative was therefore produced without changing scientific or formal content:

- outer archive: `Permansson_v0.1.8_WINDOWS_SAFE.zip`
- outer archive SHA-256: `ae109fa7718b65023566f0dddf584e0d81d00ca494cc545d3f51268ef2d05cfb`
- archive root: `Permansson_v0.1.8/`
- maximum outer member path: 119 characters
- ZIP entry origin/metadata: DOS-compatible
- expanded destructive-suite duplicate: omitted from the outer ZIP
- runnable destructive derivative: `Permansson_TestSuite_v0.1.7_WINDOWS_SAFE.zip`
- runnable destructive derivative SHA-256: `864e2fec88b345194b0a9dc4ce9431e6a9a754eb88adea75fb8835b6244f41c3`
- runnable derivative maximum member path: 175 characters
- fresh portable rerun: Runs 17-30 = **14/14 PASS**
- v0.1.8 Run 33 after repack: **50/50 PASS**

The byte-identical frozen evidentiary archive remains unchanged at SHA-256 `7ab578c928a2918e09846b9f1c425f5a6c07b5b5dd0a0c8728662eebcb69a15a`. This is a packaging repair only; no Lean source, theorem statement, paper PDF/TeX, test threshold, mutation case, or claim boundary changed.

## Claim boundary

The machine-checked completion claim is the promoted discrete GR/PR mathematical core through Proposition 8.1. It does not extend to empirical validity, causal identification, provenance quality, statistical adequacy, literature priority, continuous-time/set-valued/nonautonomous extensions, or the non-core Section 11.5 finite-certificate/rigidity programme.
