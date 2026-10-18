# First-moment transport identification

This construction uses the original `IsKRTest`, `W1DualLE`,
`IntegrableCoupling` and `couplingW1` interfaces. It applies to arbitrary
probability laws with finite first moments on a separable pseudometric space
with its Borel sigma algebra. Every Polish metric space satisfies the stated
topological profile. The first moment is measured about an explicitly supplied
point. Tests are individually bounded, with no common norm-one restriction.

The quantizer inspects the first n+1 points of an actual dense sequence whose
first point is the supplied reference point. An explicit recursion keeps the
closest center, retaining the earlier center on ties. Each finite index map
is measurable. Its distance error is bounded by distance to the reference
point and tends pointwise to zero. Dominated convergence then proves that
the actual integrated errors vanish under both laws.

A finite test on the center pseudometric is extended by a finite McShane
infimum and clipped at its finite radius. This globally bounded one-Lipschitz
function fixes every center value, including repeated centers. Consequently
the original dual bound transfers to the two finite quantized laws with
only their actual integrated errors added.

Finite transport separation produces a real joint probability with the exact
quantized marginals. For every positive-mass cell, the lifting measure uses
the actual normalized restricted law. Zero-mass cells use a fixed Dirac law;
the transport marginal equations force all their weights to vanish. The
finite mixture of cell-product laws is proved to be a probability measure
with exactly the original two marginals. Its distance cost is integrable by
the original first moments. The triangle inequality bounds its cost by the
finite center cost and the two integrated quantization errors.

Taking the vanishing-error limit identifies the original coupling infimum
with the supremum of the original absolute KR integral differences. No
quantizer, extension, coupling lift, duality theorem or optimal coupling is
an input hypothesis. The construction does not prove general optimal-plan
attainment or completeness of the first-moment probability space; those are
separate construction obligations.

All six modules compile with pinned Lean 4.34.0. The discovered post-build
integration test passes its 72-declaration transitive-axiom audit, with only
`propext`, `Classical.choice` and `Quot.sound`. The published receipt binds
every source SHA256. The regressions prove exact transport distance three
for Dirac laws on the infinite ambient space of real numbers and reject a
bound of two, alongside the quantizer anchor and equal-law checks.
