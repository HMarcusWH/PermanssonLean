# Post-PR102 acceptance — candidate audit only

**Source baseline**: `3931e4dccafb47b3cdf70177c0cf337102c90731`, original integrated tree `0ffd313dcd5efd1cf90a85ee458024b1b28cd3f8`.
**Status**: preliminary source-integrity gate; full45 and scoped-paper decisions
are **NOT ACCEPTED**. This directory does not revise historical
`research/paper_closures/post_merge_79/`.

This candidate includes all 45 original acceptance case IDs, their exact
historical original requirements and their original proof declaration
bindings. It checks raw current source SHA-256 digests for all 124 distinct
historical mathematical providers and checks the Git blob identities of the
three preserved post-PR79 historical JSON records.

At this **pre-review** snapshot all 45 decisions remain PENDING or
PARTIAL_SCOPE; 15 historical strengthened cases are specifically PENDING.
Neither matching source bytes nor old green CI becomes new independent
acceptance. The 17-check / 679-reference claim remains UNVERIFIED, and the
older ConstitutionCore owner-receipt mismatch remains RETIRED/UNRECONCILED.

Run:

```bash
python3 verification/research/post_merge_102_verify.py --mode audit
python3 -m unittest verification.research.test_post_merge_102_acceptance -v
```

The two strict gates MUST fail until their separate, independently
authenticated prerequisites are supplied:

```bash
python3 verification/research/post_merge_102_verify.py --mode full45-strict
python3 verification/research/post_merge_102_verify.py --mode scoped-release-strict \
  --manifest release/mathematical-closure-1/manifest.json
```

The final source identities must record actual B, H, genuine GitHub S,
post-merge M, required exact-head test/axiom receipts, individual semantic
negative fixtures, review provenance and case-by-case acceptance. The branch
has not been merged, and this candidate does not assert final release.
