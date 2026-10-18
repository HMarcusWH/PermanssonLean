# NEXT-03.2 — finite positive-support SCM (F-05)

The added `PositiveMediationWitness.lean` instantiates the **existing** `SCM.mediation_identification` theorem, not a new causal-identification principle. Its two treatments and two mediators have strictly positive observational treatment/mediator cells, unlike the nonidentification counterexample with unobserved cells. All four nested expectations differ in the intended finite constructed profile: 7/3, 5/3, 10/3, 8/3, respectively at (false,false), (false,true), (true,false), (true,true). Nonzero mediator response is visible in the last two.

The observed mediator noise has P(U=true)=2/3, assignment is fair, and the outcome is a deterministic function of treatment and mediator. The exactly same noise law drives both observational and intervened terms. Positive mass comes from the explicit observations, not an unverified positivity assertion.

## Acceptance and limitations

* The original generic theorem and its mandatory positivity hypotheses are not changed. New Lean proofs must compile under pinned 4.34.0 with the default axiom allowlist; the source-only draft is not yet certified.
* Independent standard-library Python fractions regression contains four successful tests. These do not claim Lean or empirical identification.
* The original F-05 existing positive arithmetic needs a separate source/routing check if a reviewer requires exact identity to that historic fixture; this is an additional explicit Lean positive instance, not a retroactive replacement.
* No real-world causal data, external observational model identification, general mediation without positivity, or applied PR certification is claimed.
* The PR changes exactly one root import and adds one Lean module, one Python test and this document; protected source, pins and workflow unchanged.

No merge, release or settings change authorized.
