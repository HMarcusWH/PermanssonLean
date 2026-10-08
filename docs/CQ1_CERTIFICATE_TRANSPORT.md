# CQ-1 Part 3 — certificate transport and adversarial validation

**Status:** Research PR #38 under construction. Only an exact head commit with
passing Research Lean and transitive axiom audit is formally verified. This is
not part of the immutable v0.1.8 theory or its application statuses.

## Key distinction

Part 2 already proves quantitative survival and output-margin errors on a
frozen comparison domain. Part 3 seeks a **fully typed finite certificate**
for the *approximate model itself*. The second baseline and intervention are
different strategic-world models with the **original world kernel P held fixed**.
Neither Exact GR/PR nor QSD is transferred.

For point-separating measurable joint-state spaces, the initial-state
distinguishability of point-started path laws can transport the same state
comparison domain B₁ **without equality of the induced kernels**. This does
not imply equality of effects, properties, or asymptotic classifications.

Write `e(L,δ) = 1-(1-δ)^L`, for `0≤δ≤1`. The proposed exact-model
transport keeps true finite-path expectations distinct from approximate
numerical output values:

```text
etaStar = ENNReal.ofReal (min 1 (eta.toReal + e(L,delta0)))
kappaStar = kappa - e(L,delta0) - e(L,deltaJ)
Require kappaStar > 0, uniform global kernel TV, and fixed world P.
```

The clamped error meets the original finite-persistence gate `etaStar≤1`
even when its survival claim is vacuous. Error-ledger terms `b0,bJ`
belong to output reporting and must **not** change the underlying model's
true constitutive-margin definition.

## Planned checks

- Construct new comparison set for approximate model from two distinct
  original states using the zeroth canonical path marginal.
- Promote real survival lower bound to `IsFinitePersistent` with explicit
  finite mass and `ℝ≥0∞ ↔ ℝ` reasoning.
- Show approximate exact-output profile's infimum is its actual uniform
  constitutive margin, not a reported numerical proxy.
- Prove transported `FiniteConstitutiveCertificate` with positive remaining
  model margin.
- Provide nonzero kernel-TV, exact-rational regression fixture using a
  four-state strategic/world transition table and a constant frozen world
  transition generator.
- Prove adversarial zero-horizon and changed-world exclusion in Lean, and
  show error-budget exhaustion has no positive margin guarantee.

The rational script is **not** a proof of a typed strategic factorization;
only the Lean declarations establish such claims. A sampled finite grid
cannot establish the infinite-domain positive-pointwise / zero-infimum
phenomenon. If this counterexample is later added, it must be a genuine
all-states analytic Lean theorem or an explicitly specified infinite model.

## Firewall

Research source files must be direct imports of `PermanssonResearch.lean`.
The separate Research Lean job builds the target, runs axiom/placeholder
audits, and executes the Python rational fixtures. Original Lean, historical
verification, and Linux/Windows application checks must remain green.
No frozen `PermanssonLean/`, paper, toolchain, application, or release evidence
files are changed.
