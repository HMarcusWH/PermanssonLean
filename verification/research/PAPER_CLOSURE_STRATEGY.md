# U03: full behavioral deviations and original trace bridge

The new `ActionTrace` histories retain the initial state and every subsequent
joint action and next state. A behavioral rule selects a real finite probability
row using only this past history. The fixed opponent's current action is then
drawn independently, and the original physical/update timing is retained. The
interface therefore includes arbitrary time-dependent and history-dependent
behavioral rules; it does not give the deviator the current opponent draw.

The discounted verification proof works for any finite state and action types,
bounded real rewards, and a discount in `[0,1)`. It proves the exact finite
telescoping identity including the terminal value, absolute convergence, a
geometric payoff-tail bound, vanishing terminal correction, the infinite
performance-difference identity, and attainment under averaged Bellman
equalities. The expected-path theorem integrates the actual infinite retained
action trace. `Row.ofMeasure` admits every initial probability measure.

For X1 the exact pure-action loss is `9/211` precisely when the old world is
depleted and the indexed player extracts. Both indexed players and every full
behavioral rule are covered. The integrated identity uses the same action trace
for the reward and the discounted bad-event count. The baseline candidate acts
according to `piExtract`; an incentive result with the learner's update kernel
does not claim that the historical learner action rule is an equilibrium.

`ActionTraceOriginalBridge` identifies every finite state prefix and proves
literal equality of the erased infinite state-path measure with the original
typed `pathLaw`, provided its row is the actual induced kernel. The X1 concrete
bridge discharges that row premise against the actual baseline atom theorem.

No equilibrium uniqueness, opponent-correlated current draws, or risk-sensitive
objective is asserted. Private-random-seed implementation is represented by the
nonanticipating behavioral probability-rule interface. The axiom/source receipt
lists the exact checked source scope, hashes, compiler version and dependencies.
