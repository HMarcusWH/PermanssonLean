# Exact finite observation-history policy trees — numeric scope

The `finite-belief-tree` command implements a bounded finite-horizon controller in which
an observation is sampled **before** the action at each stage. A selected action is
required to be legal for **every hidden joint state of positive posterior mass**.
The realized world state then changes under `P(x'|s,x,a)`; the strategic state is
updated afterward under `U(s'|s,x,a,x')`. The next observation is sampled from
`Q(o|x')`. Neither future observations nor the latent state are available to the
controller as decision inputs.

The input supplies the full finite model `alpha/P/U`, initial joint prior,
world-dependent observation kernel, final joint-state rewards, and horizon.
The original `alpha` is source-bound but not asserted to equal the optimized
observation-history controller. No external source/model identification is inferred.

The engine supports **1–3 transitions**, at most **2 strategic states**, **3 world
states**, **3 actions**, and **3 observation labels**, with exact rational rows.
The reported optimum is over the complete deterministic observation-history
policy class on this finite bounded model. Branches of zero observation mass
have no normalized posterior and no inferred action; there is no fabricated
history support. Intermediate actions have no separate stage reward, and
terminal rewards are applied only after the declared number of transitions.

## Independent verification

The producer performs normalized Bayesian dynamic programming. The separate
checker (`receipts/belief_tree.py`) performs unnormalized flow optimization
from the original `P/U` data and independently replays the terminal law along
the **actual selected decision tree**. It rejects omitted observation branches,
hidden-state clairvoyance, wrong action chronology, unsupported actions,
invalid posterior mass, modified source kernels and forged certification flags.
A separate two-stage regression enumerates all **64** feasible decision trees
in a small instance by direct summation over state/observation trajectories.

The example's best two-stage policy scores **55/64**. Its best legal blind
action sequence scores **3/4**, giving an observational information premium
of **7/64**. The same second-stage signal can lead to different actions after
different first-stage observations, confirming genuine history dependence.

## Limitations and scientific status

This is not a general unbounded or continuous-state POMDP solver, nor a
certificate for stochastic history-dependent policies outside the declared
finite deterministic policy class. No posterior is identified empirically.
No Lean bridge has been compiled for these literal inputs. `lean_status`
remains `NOT_EXECUTED`, `empirical_identification` is `NOT_IDENTIFIED`, and
`scientific_claims_verified` is `false`. A successful numeric computation or
receipt check does not establish Exact GR, PR constitution, mathematical CERT,
application release acceptance, or publication approval.

The original v0.1.0 legacy application and accepted historical releases are
unchanged. Dedicated active CI workflow migration requires separate review.
