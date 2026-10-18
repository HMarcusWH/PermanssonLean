# Constructed first-moment transport completeness

This track proves A-COMPLETE for a complete separable metric space with its
Borel measurable space. `FirstMomentProbability y₀` consists of actual
probability measures whose distance from the fixed point `y₀` is integrable.
The distance is the original infimum of integrable coupling costs. The
separately verified first-moment KR theorem identifies it with the original
supremum over individually bounded measurable 1-Lipschitz tests.

`KRDualSeparation` first proves that a zero original dual bound forces equal
probability measures. Scaling arbitrary bounded Lipschitz tests gives equal
integrals, and the pinned Portmanteau theorem and Hausdorff weak topology give
equal laws. This discharges the separation axiom of the actual transport
metric, alongside the dual triangle and symmetry calculations.

`GluedCouplingSequence` disintegrates each supplied adjacent joint law into
its genuine conditional Markov kernel. The Ionescu–Tulcea construction gives
a probability measure on countable sequences. The proof identifies every
coordinate marginal with the specified original probability measure and
every adjacent joint distribution with the supplied coupling. Thus the
integral of each actual step distance equals that coupling's actual cost.

`SummableStepLimit` proves that summable expected step distances imply
almost-sure summability. Completeness of the underlying space gives a limit;
the pinned measurable-limit construction makes the chosen limit measurable.
Its first moment follows from the initial first moment and the summable
distance tail. Mapping the genuine path law by a coordinate and that limit
constructs a coupling whose cost is bounded by the expected tail.

Finally, every Cauchy sequence has a strictly increasing subsequence with
successive distances below a summable geometric sequence. The definition of
the nonempty coupling-cost infimum supplies actual couplings with costs
below those same bounds. The constructed limit and the Cauchy property give
convergence of the entire sequence. `FirstMomentProbability.completeSpace`
packages this as an actual `CompleteSpace` instance.

All seven dedicated modules compile with pinned Lean 4.34.0. The discovered
post-build integration test passed its 60-declaration transitive-axiom audit
in 81.485 seconds, allowing only `propext`, `Classical.choice` and `Quot.sound`.
The published receipt binds every source SHA256. Infinite-ambient regressions
include a geometric sequence of real Dirac laws, transport distance three,
and constancy forced by a genuinely glued chain of zero-cost couplings.
These theorems do not assert general optimal-plan attainment or any
invariant-law or ergodic conclusion; those are separate results.
