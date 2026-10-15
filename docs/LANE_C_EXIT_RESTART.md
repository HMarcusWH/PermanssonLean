# C-Exit C — Canonical stopped-path restart (PR #68)

**Status:** active draft; incrementally compile the kernel and path-law
proofs before claiming the arbitrary measurable-event restart theorem.

**Base:** merged \`main@6e1fecf4fc3731b5c6ebee937edf3201b8186fcf\`
(PR #67; four post-merge workflows passed).

**Specification:** \`docs/PERMANSSON_V020_MATHEMATICAL_INTEGRATION_SPEC.md\`
§2.3 (Proposition 4.2f), mathematically separate from the already-proved
arrival and constitutive-margin certificates.

## Planned primary identity

For \`N\` a fixed canonical strategic-world model, source \`B\`, actual
first exit \`E(n,D)\`, \`y∈B\`, and a measurable \`A⊆(ℕ→Y)\`:

\`\`\`text
P_y(E(n,D) ∩ shift_(n+1)^-1(A))
  = ∫ z in D, P_z(A) ∂firstExitStepMeasure(N,B,n,y).
\`\`\`

Equivalently the corresponding restricted/shifted measures on infinite
paths are equal. First-exit never occurs at time zero from y∈B.

## Do not fake the missing step

1. \`CanonicalTailKernel.lean\`: actual measurable infinite-future kernel,
   equal to the canonical Dirac-point path law.
2. \`RestartSanity.lean\`: check the shifted future's zeroth observation
   equals the genuine first-exit endpoint measure. **Not full restart.**
3. \`StationaryTailLaw.lean\`: prove deterministic-time continuation for
   full future path from the last observed state (not just one-step law).
4. \`SwitchRestartLaw.lean\`: prove finite first-exit restricted-shifted
   probability-measure equality using the actual post-intervention model.
5. \`SwitchRestartSum.lean\`: disjoint countable first-exit-time mixture,
   preserving missing never-exit mass and zero-probability cases.
6. \`SwitchRestartAdversaries.lean\`: typed true-kernel witnesses
   for nontrivial future events.

Do NOT apply \`pathLaw\` to unnormalized exit submeasures. Use a Markov
kernel composed with the submeasure. Use the original \`D\B\` mask,
the original stationary \`α→P→U\` process, and do not assume \`StrongMarkov\`
as a premise. Standard-Borel or finite-state restrictions are not
automatically valid for the general theorem. Prove arbitrary measurable
future-event identity, not merely first-coordinate agreement.

## CI acceptance

Focused source-head smoke + original Lean, executable verification,
application contracts, Research Lean synthetic merge, 3-axiom
transitive audit, direct research-root imports, 668+ regressions,
source firewall, D0-F golden/C10 evidence.

A green focused smoke for a *subset* of modules is NOT the primary
Proposition 4.2f completion. The full implementation remains draft
until all mathematical and CI obligations are discharged.
