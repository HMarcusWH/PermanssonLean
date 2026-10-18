# Observation-admissible finite belief optimization

`BeliefKernel`, `BeliefAlpha`, `BeliefHistory`, `BeliefFilter`,
`BeliefChronology` and `BeliefMonitor` treat the entire hidden augmented state,
including every event-monitor coordinate. A controller receives only its
observations and previous controls. The Bayes update is normalized when the
observation has positive probability; a declared default handles zero likelihood.
The weighted posterior identity remains valid at zero likelihood.

The finite alpha-vector construction is a genuine upper envelope with an
attaining observation/control tree. An actual normalized word law identifies
the recursion with the terminal hidden-state integral. Every real behavioral
observation-history policy is bounded by that value, and an observation-only
tree attains it. Forward unnormalized filtering, action likelihoods and
positive-history conditional probabilities are proved separately.

The monitor adapter uses the actual fixed physical world and strategic update
rows. Hidden monitor memory stays inside the belief state, and its literal
trace reward agrees with the terminal augmented-state reward. The witness gives
observation-admissible value `1/2`, while an illegal hidden-state peek gives `1`;
it also checks zero-probability defaults and successor observation timing.

`audit_belief_closure.py` checks all 116 exported declarations and their
transitive axioms. The discovered integration wrapper runs the positive
witness and audit. Frozen receipts and raw audit output are copied under
`research/paper_closures/`. This proves finite mathematical attainment;
optimization of arbitrary real inputs is not claimed to be executable.
