# PR113 full v3.1 execution entrypoints — source implementation note

This note describes candidate code only. It is not a security review, mathematical acceptance, merger approval, or scholarly release. Everything remains on PR #113.

## Full-source and release calling convention

The read-only verification and release entrypoints now take three **required together** source-bound v3.1 inputs when claiming full 45-case/11-claim coverage:

- `--additional-contract`: the original v3.1 producer registry bound to the exact reviewed H, not a local completion flag.
- `--additional-zips`: detached directory of *original* downloaded GitHub producer artifact ZIPs indexed by authenticated numeric artifact IDs, containing exactly the registered members.
- `--workflow-blob-candidates`: exact versioned workflow source Git object mapping. Mapping OIDs alone **never** establish independent security approval.

Applies to `verification/research/final_closure_gate.py --phase premerge-full`, to `--phase postmerge-preseal-strict` and `--phase full-release-strict`, to `verification/research/final_closure_verify.py` corresponding modes, and to `release/mathematical-closure-1/seal_approved.py --full` / `verify_release.py --approved-seal` for the complete release.

The gate reauthenticates 21 original producing ZIPs, all 76 v3.1 role-owned source controls, associated GH run/job/check/attempt/source-workflow/ZIP identities, and the actual positive/negative source/log bytes. This is distinct from approving mathematical relevance; 11 claim pairs produce 22 directional checks. Synthetic positive tests exercise predicates only.

## Explicitly incomplete dependencies

- The genuine historical T→T2 archive restoration and original A2 successor migrations remain fail-closed until real independently authorized verification. Do **not** modify historical T/C manifests, switch original expected hashes, skip legacy tests or weaken the preserved 25-workflow security policy.
- The original 3 staged historical workflow blobs remain unchanged. `docs/operations/pr113_unapproved_workflows/pr113-source-controls-v3_1.yml` is an **additional non-executing** reviewed-source candidate for all 45+20+11 original control families. Its missing reviewed selection files are a deliberate stop, not a reason to invent favorable false statements.
- The previous 259/259 Lean type and axiom candidate receipts originated from the earlier real source head and must not be relabeled as execution of a future H. Source identity alone does not grant GH producer/authenticated case acceptance.
- Independently submitted source/security and scholarly approval, genuine owner-authorized merge M with exact-M checks, original ZIP archive source and postseal replay, and explicit publication authority have not occurred.

Any activation of a staged workflow or acceptance-map edit changes H and requires fresh exact-head CI, producer receipts, mathematical reviews and artifact verification.
