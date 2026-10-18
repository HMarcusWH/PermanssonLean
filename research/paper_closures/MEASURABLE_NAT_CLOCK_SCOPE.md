# General measurable natural private clocks

F-CLOCK and F1-P03 select a new typed clock-augmented baseline, actual
successor update and chronological projection. They contain no finite-action,
finite-world or countable-original-state premise. The neighboring finite
feasibility and finite mediation profiles state those restrictions explicitly.

The independently checked `NatPrivateClock` profile already supplies a genuine
unbounded natural clock and full projection for countable strategic spaces
and finite action/world spaces. Its atom proof is appropriate to that profile.
The additive modules below supply the same primitive closure without those
coordinate restrictions:

- `MultiAgent/MeasurableNatPrivateClock.lean` selects a countable family of
  kernels measurably by the natural clock, using product measurability. Every
  original coordinate is an arbitrary measurable space. The opponent's own
  private state stores and actually advances the clock. Player one's update,
  the common update and the physical kernel are pulled back along the stated
  projection. Strictness, common exogeneity and declared action feasibility
  are inherited from the corresponding original mechanisms.
- `MultiAgent/MeasurableNatClockTransport.lean` proves the whole induced
  alpha/P/U measure is the scheduled original measure with its successor
  clock attached. It uses product pushforwards and the original setwise
  induced-kernel integrals, with no singleton-atom or finite-sum reduction.
  Existing chronological path uniqueness then gives full infinite path-law
  projection, and therefore every finite prefix, for any initial probability
  law. The opponent-locked replacement uses the same lifted physical object.
- `MultiAgent/MeasurableNatClockFixture.lean` instantiates every original
  coordinate, including both actions and the world, by the real line. Its
  declared opponent action at time t is t, so the schedule is nonperiodic.
  The actual clock advances, a stalled clock has probability zero, and the
  full projection holds for arbitrary real-coordinate initial laws.

This is a new lifted model; it does not alter the update or state type of a
frozen original baseline. A common clock reading treated variables remains
outside the exogenous-common premise. No claim of strategic optimality,
causal identification or a universally admissible anchor menu is added.

The executable source/signature/transitive-axiom audit is
`verification/research/paper_closure_measurable_clock_audit.py`. Its durable
receipt and raw checked statements are
`measurable_nat_clock_receipt.json` and
`measurable_nat_clock_signatures_axioms.txt`; the discovered test is
`test_paper_measurable_clock_lean.py`. All three modules passed, followed by
fresh source-bound recompilation and a 51-declaration signature/transitive
axiom audit. The discovered integration test passed in 27.772 seconds.
This local execution remains independent of future head/merge CI.
