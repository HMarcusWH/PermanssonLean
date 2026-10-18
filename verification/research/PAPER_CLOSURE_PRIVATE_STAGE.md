# Private-control robust stage

`PrivateControlStageModel`, `PrivateControlStageOptimizer` and
`PrivateControlStageFixture` formalize the finite stage game in which nature
sees the control distribution and chooses before the independent private
control is realized. The normalized actual stage law samples nature and the
control independently. Pure nature choices attain the minimum over arbitrary
real nature distributions.

The total exact rational LP constructor returns a rational control simplex
point and a value. Its feasible region includes a proved lower payoff floor,
including tables whose payoffs are all negative. The returned controller
guarantees its value against every real mixed nature law, an actual pure nature
law attains it, and it dominates every real control mixture.

Matching versus opposite rewards has private value `1/2`, while every pure
control has worst value zero. The separately defined revealed-control law also
has value zero. An all-negative table returns value `-7`. These distinguish the
private stage from the existing nature-after-realized-control dynamic game.

`paper_closure_private_stage_audit.py` checks all 59 exported signatures and
their transitive axiom dependencies, binds the source and compiler artifact
hashes, and permits only the three standard Lean axioms. The discovered
`test_paper_private_stage_lean.py` passed against the frozen sources.

This is an exact private stage theorem. It does not substitute private timing
for the separately proved revealed-control recursion or assume a hidden model
is chosen afresh when it was committed for the entire horizon.
