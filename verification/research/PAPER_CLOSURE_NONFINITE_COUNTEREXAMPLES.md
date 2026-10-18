# C-01: nonfinite occupation falsifiers

Both witnesses use the same genuinely homogeneous Markov kernel on the
countably infinite discrete state space `Nat`: each state moves to its
successor. From initial state zero, the actual canonical path law is proved
equal to the Dirac law of the clock path. No time-dependent transition is
substituted for this physical state.

The first witness escapes: every singleton empirical mass tends to zero.
Weak convergence on the discrete space would force every singleton of a
putative limiting probability to have mass zero, contradicting normalization.
Thus the empirical laws have no probability-valued weak limit.

The second witness is a fixed two-point descriptor of the same clock.
Block `k` runs between `(k+1)!` and `(k+2)!`, and has label `k mod 2`.
At its endpoint, the discrepancy of the average from the final block's
label is at most `1/(k+2)`. Even and odd endpoint averages consequently
converge to zero and one. Both the scalar empirical averages and the
two-point descriptor empirical probability laws fail to converge, almost
surely under the actual canonical law.

All three sources compile under pinned Lean 4.34.0. The discovered
integration test passed, freshly auditing all 33 named declarations and
their transitive axioms against the exact source hashes. The source-bound
receipt permits only `propext`, `Classical.choice`, and `Quot.sound`.

These falsifiers reject unrestricted nonfinite
occupation conclusions; they preserve the hypotheses of the separately
proved regenerative and stationary-with-initial-absolute-continuity profiles.
