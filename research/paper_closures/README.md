# Mathematical paper closures

This additive implementation follows the supplied 2026-10-18 build package at
audited main `39279799834ae536bda715dedecdc11a32bf6c82`. The unchanged package is
under `spec/`; its historical `NOT_LEAN_VERIFIED` labels are retained verbatim.
Current implementation evidence is issued separately.

**The selected paper contracts are implemented in their declared scopes.**
Local compilation and axiom audits certify the exported Lean statements.
The 42-target crosswalk and independent scope reviews retain the broader atlas
residuals. They do not substitute for final PR-head and genuine synthetic-merge
CI or user-controlled merge.

The implementation adds actual typed X1 intervention atoms and rational
recursions, the six original margins, full observed action-history strategy
verification, finite autonomous-anchor obstruction, real behavioral finite
monitors, a rational stationary constructor, measurable quotient shared mass,
geometric prefix error, localized history budgets, summable path properties,
compatible overlapping grammar patches, finite legal anchor criteria, and
conditional specialized algebra. A separate `EconomicWitness` model supplies
its own original regime and strategic constitution gates.

The whole-path product bound constructs dependent-history common mass,
retains the initial mismatch and time-varying defects, and extends finite
prefix bounds to all product-measurable events. Summability gives a genuine
infinite product. A constant recurring leak has only the limiting budget one.
The normalized discounted score budget also retains initial error `epsilon`:
`1-(1-epsilon)*(1-beta)/(1-beta*(1-eta))`. Zero row error leaves exactly the
initial budget, including the time-zero score.

The strict-autonomy theorem proves an impossibility result for the
declared autonomous subclass. Its standard-Borel extension compares complete
infinite laws for every stationary treated mechanism under all-time primitive
almost-everywhere agreement. A nonatomic continuum fixture and a point-start
counterexample retain the null-set boundary. Finite-index product kernels now
allow arbitrary measurable component spaces, with literal three-player
real-coordinate and binary original-law reductions. The
natural private-clock construction now also allows arbitrary measurable
original coordinates. Its actual successor update, whole ordered alpha/P/U
row identity and original full infinite path-law projection retain the
declared schedule at `t+n`; strictness, common exogeneity and declared action
feasibility are preserved. A nonperiodic real-coordinate fixture checks the
general construction. The
finite coupling construction now proves both directions of the original
Kantorovich–Rubinstein duality and existence of an optimal finite coupling.
For separable Borel pseudometric spaces, explicit measurable finite quantizers,
bounded Lipschitz extensions and normalized restricted-cell product couplings
prove equality of the original coupling infimum and original dual supremum for
all first-moment probability laws. Actual conditional-kernel gluing and
summable-step limits now prove completeness on complete separable Borel metric
spaces. A Banach constructor gives the unique first-moment invariant law and
geometric convergence for a moment-preserving contractive kernel. Both laws in
the original perturbation bundle can be constructed independently.
The robust dynamic game lets nature observe the realized control. A separate
exact private-control stage LP proves the different maximin value before that
draw is revealed. Optional specialized algebra
keeps the actual model-to-feature identification as an explicit premise.

The exact rational hard-risk solver enumerates active subsets, proves real
vertex completeness, reconstructs actual legal control policies from flows,
and optimizes against every real behavioral history policy. The finite belief
layer proves normalized hidden-state filtering, alpha-vector attainment and
optimality over observation-admissible histories, with full monitor memory
hidden inside the belief state. The actual risk fixture has optimum `17/20`.
A separate danger flag continues after completed success and records the
literal through-horizon event, including time zero. Its probability under the
actual full-history law equals the terminal linear risk score of the occupancy
formulation; success and later danger can both have value one.

For compact metric Borel state spaces, the actual all-initial Markov law has
almost-sure invariant empirical cluster points; distance to the invariant
family tends to zero, and uniqueness gives weak empirical convergence. The
bounded pointwise ergodic theorem is derived from a Hopf maximal inequality,
including actual conditional-expectation identification without invertibility
or ergodicity. The stationary profile constructs the actual conditional random
invariant probability, proves compact and noncompact stationary weak empirical
limits, and transfers them with the exact initial-law Radon–Nikodym path
density. Homogeneous countable escaping-mass and oscillating-block chains
give explicit limits to general-state convergence claims.

Geometric regeneration constructs its invariant law, solves the bounded
Poisson equation and proves all-initial bounded-observable averages and weak
empirical convergence. A fixed numeric occupation-limit property and a literal
compact-descriptor probability-limit property each supply all four original
factorizations and the full margin adapter. For unbounded descriptors, a finite
expected absolute regenerative reward series now gives first moments,
all-initial integrable averages, literal empirical Wasserstein convergence,
and uniform tail control. A globally measurable first-moment limit selector
with a fixed fallback supplies the four original path-law factorizations.
The descriptor, fallback and bounded continuous functional are fixed before
comparison; the original global dual-Lipschitz predicate remains an explicit
requirement of the margin adapter. A real reset-and-increment chain checks
this profile with genuinely unbounded invariant support.

Actual finite couplings now follow the action/world/update order, with exact
marginals and propagated weighted metric sensitivities. Dobrushin/Doeblin
certificates retain their diameter/minimum-distance factor. Four independent
strict contraction gates construct the four invariant laws used by the
original comparison; the weighted metric and original product-max metric
retain the necessary conversion factor.

Infinite safety is proved for the actual canonical infinite law and every real
full-history behavioral controller. One deterministic stationary controller
attains the optimum at every state. The finite support-pruning construction
computes the greatest controlled invariant set, exactly the states with optimum
one. A fixed-leakage example has positive finite safety and zero infinite safety.
Adaptive grammar control is linked to the original admissible typed rows through
explicit rational atom certificates and a measurable finite-state coding.

Reproducible checks use the repository's existing Lean toolchain and pinned
dependency manifest; no dependency update is required:

```text
lake build PermanssonLean PermanssonResearch
python -m unittest discover -s verification/research -p 'test_*.py' -v
python verification/research/paper_closure_source_audit.py --output .lake/closure-build/source-audit.json
python verification/research/paper_closure_imports.py
python verification/research/test_x1_paper_closure.py
python verification/research/paper_closure_strategy_audit.py
python verification/research/audit_multiagent_closure.py
python verification/research/paper_closure_analytic_audit.py
python verification/research/paper_closure_risk_lp_audit.py
python verification/research/paper_closure_private_stage_audit.py
python verification/research/paper_closure_completeness_audit.py
python verification/research/paper_closure_invariant_audit.py
python verification/research/audit_belief_closure.py
python verification/research/audit_compact_feller.py
python verification/research/paper_closure_birkhoff_audit.py
python verification/research/audit_stationary_random.py
python verification/research/paper_closure_regenerative_audit.py
python verification/research/paper_closure_metric_coupling_audit.py
python verification/research/paper_closure_autonomy_ae_audit.py
python verification/research/paper_closure_measurable_product_audit.py
python verification/research/paper_closure_nonfinite_counterexample_audit.py
python verification/research/paper_closure_specialized_boundary_audit.py
python verification/research/paper_closure_information_audit.py
python verification/research/paper_closure_full_path_product_audit.py
python verification/research/paper_closure_discounted_initial_audit.py
python verification/research/paper_closure_regenerative_moment_audit.py
python verification/research/paper_closure_through_risk_audit.py
python verification/research/audit_x1_matrix_tables.py
python verification/research/audit_nat_private_clock.py
python verification/research/paper_closure_measurable_clock_audit.py
python verification/research/paper_closure_acceptance_evidence.py --refresh
```

Some audit drivers require local per-module diagnostic logs in
`.lake/closure-build`; inspect each driver's requirements. Those logs are local
evidence, not a substituted CI source identity. The original release, papers,
application, archived receipts, core sources, and dependency pins are preserved.

The [acceptance ledger](acceptance_evidence.md) maps all 45 supplied case IDs
to actual declarations, semantic compiler mutations, exact Python executions,
or explicit information/interface gates. These evidence types remain distinct.
Durable receipt and raw-log copies retain their measured bytes; the discovered
artifact-link tests check that their saved hashes survive publication.

The [local combined build](local_integration_build.json) passed all 4,456 jobs
for the original core and 628-module research root, with its measured source
snapshot unchanged during compilation. Final Git source-head and synthetic-
merge CI evidence is recorded separately on the pull request.
