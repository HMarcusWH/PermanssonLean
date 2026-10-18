# Exact finite hard-risk optimization

The 17 modules listed by `paper_closure_risk_lp_audit.py` construct a total
rational solver for finite-horizon, time-dependent controlled systems with
rational initial masses, transition probabilities and terminal scores.

The generic constructor enumerates finite active constraint subsets, computes
rational Gram/Cramer candidates, filters feasibility and selects a rational
objective maximizer. Every real vertex occurs among the candidates. Candidates
from other active subsets need not themselves be vertices. Compactness and an
extreme point of the maximizing face prove completeness; a nonempty compact
feasible polytope cannot be missed. No external optimizer or supplied optimum
is assumed. This is a mathematical total algorithm, without an efficiency claim.

The actual history law uses real behavioral control distributions and records
all previous states and controls. Its state/action marginals satisfy the flow
equations. Conversely, the legal Markov rule `x/d`, with an admissible fallback
at zero-mass states, realizes every coordinate of a feasible flow. That single
reconstruction works simultaneously for every terminal score. The monitor
adapter tracks the actual physical/control word and full monitor state.

`solveRiskFlow_none_iff_no_behavioral_policy` certifies infeasibility against
every allowed real history policy. `solveRiskFlow_some_actual_optimal` returns
an actual legal policy, its exact rational success, risk feasibility, and
optimality against that same full policy class. All flow coordinates are proved
to lie in `[0,1]`; the final solver does not assume boundedness of its polytope.

The actual three-state fixture gives success `4/5+p/10` and danger `p/10` under
one normalized chronological probability law. Risk at most `1/20` forces
success at most `17/20`; a fair control mixture attains it. The all-risky control
is infeasible. Separate exact-computation fixtures cover dependent and duplicate
constraints, an empty feasible set, and a zero-dimensional feasible polytope.

The source-bound receipt `research/paper_closures/risk_lp_receipt.json` records
221 exported signatures and their actual transitive axioms, with only
`propext`, `Classical.choice` and `Quot.sound` allowed. Every source was
re-elaborated and its source/artifact hashes checked before and after the audit.
The mandatory discovered integration test runs the audit against current files.

This establishes expected terminal-score optimization. The optional dynamic
dual-certificate checker is separate, as are unbounded horizons and adaptive
asymptotic synthesis.
