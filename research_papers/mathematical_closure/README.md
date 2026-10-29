# Mathematical closure — final single-PR manuscript candidate

**DRAFT / NOT ACCEPTED / NOT PUBLISHED.** Canonical source consists of these original thirteen TeX/bibliography/document files. This is the integrated continuation after PR #112, implemented in draft PR #113. Historical accepted v0.1.8 and v0.2.0 sources remain unchanged.

Verified starting main: \`17c315f7df7abf457eb94d393bd526d46da6f6f4\`.
The merged earlier source already included actual full canonical paths and conditional original-margin adapters for P-04/P-05 plus the native P-06 finite phase-orbit/Dirac original-path identity. The new single-PR code constructs source-specific projected error/CL/OL adapters and attempts the remaining canonical nonlinear occupation and D-08/D-09 acceptance.

All theorem statements in this manuscript MUST match accepted final Lean signatures and never be advertised as verified merely because compiled source is present. The complete acceptance status is computed separately, case-by-case, from preserved 45 original criteria; a scoped mathematical paper is not a blanket 45-case certificate. No independent academic or operational review or real-world GR/PR certification is asserted.

Draft PDF build (no release or tag):
\`\`\`bash
python3 release/mathematical-closure-1/build.py --mode draft --render --out /tmp/permansson-closure
python3 release/mathematical-closure-1/verify_release.py --manifest /tmp/permansson-closure/manifest.lock.json
\`\`\`

An approved paper requires full claim-crosswalk/negative-test review, actual final source H/B/S/M CI, an authentic independent review, page-level PDF inspection and a separate publication decision.
