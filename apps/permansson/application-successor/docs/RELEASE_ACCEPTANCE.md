# Remaining gates for a numeric-only selected release

1. Pin the exact tested source commit, root tree, package and schema versions.
2. Independently authenticate all test, wheel/sdist, ABI/platform, source and
   execution-profile receipts; show the selected-method matrix without skips.
   `scripts/build_distributions.py` gives the wheel and sdist digests for a
   clean commit. It accepts only the hash-locked build tools, fixes all
   timestamps to the commit time and normalizes the sdist, so an independent
   builder can reproduce the same bytes. Its record is self-produced and
   stays `LOCAL_SELF_PRODUCED_NOT_AUTHENTICATED`.
3. For Lean-verified modes, replay the literal caller-supplied instance in
   the pinned compiler, audit transitive axioms and semantic negative mutations.
4. Preserve historical T archive bytes and complete T/T2/current-C separation;
   independent security review and owner authorization must approve any
   workflow profile transition. No archive check is relaxed by this module.
5. Independent reviewer authority and owner signoff must be established outside
   a self-issued build or JSON file. Then, and only then, consider activation.

The code in PR #115 deliberately stops at **review readiness**, not
`RELEASE_ACCEPTED`. Numerical, Lean, mathematical CERT, empirical and
publication states remain independent.
