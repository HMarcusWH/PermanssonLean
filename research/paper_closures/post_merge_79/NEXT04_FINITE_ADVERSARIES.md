# NEXT-04.1 — time-varying projected-history arithmetic adversaries

**Status:** independently executed finite exact-fraction fixtures; the source-specific **Lean projected transport adapter remains NOT FORMALIZED**. This is preparatory executable verification, not mathematical closure of E1-G01/E1-P01.

The test builds chronological *joint prefix distributions*, not marginal-at-time-T output only, for a fine state `(visible,hidden)` and a coarse visible process. Fine rows have time-varying bounds `eta=(1/10,1/5,1/4)` with a hidden-mode-dependent defect; the coarse law initially differs by event-TV `eps=1/7`. The exact product envelope `1-(1-eps)*prod(1-eta)=94/175` bounds the observed full projected-prefix discrepancy. The projection is not assumed Markov; two hidden states sharing one visible value yield different visible transition laws.

Additional adversaries: zero per-row defect does NOT erase initial-law mismatch; a unit defect can make the entire prefix law mutually singular; a positive fixed leak does not support exact infinite retention merely because finite survival is high. Every assertion is rational arithmetic. Independent fresh execution of the five tests passes.

These tests do **not** construct a common fine-history subkernel, prove its domination after actual projection, establish measurable countably-generated lifting, identify general initial-law trajectories, or instantiate the original discounted constitutive margin. Those are the true remaining NEXT-04 proof obligations and must be supplied in a later same-scope extension before a full NEXT-04 acceptance label.

No changes to prior Lean math, accepted releases, source pins, core or application. Keep draft. No merge, publication, release, or source-bound certificate claim until independently reviewed.
