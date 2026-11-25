# Independent partial formal-arithmetic audit of MaximinKiteNE

Source: *An Exact Polynomial-Time Algorithm for 1/5-Approximate Nash Equilibria in Bimatrix Games*, Google Research / Cogentic, 2026-11-25.
Pinned release: https://github.com/google-research/google-research/blob/4a7bc8ab0bc7/cogentic_research_papers/bimatrix_nash_equilibrium/paper.pdf
PDF Git blob SHA: `ace37421def2812d90c437ad80d2cfaeb91f2294`.

## Scope

The independent checker establishes a computational enclosure of the **entire cube** for the algebraic inequality in Lemmas 5.2 and 5.4, using equations (4.1)–(4.8) as transcribed from the source. It does not execute MaximinKiteNE, certify the preceding analytic reduction in Lean, or establish a bit-complexity result by itself. The source PDF was extracted from the GitHub blob, not independently visually rendered. The check is not a Lean proof, external peer review, or a claim of source-certified formalization.

## Replay

On Linux with GCC (or a suitable Clang supporting signed 128-bit integer arithmetic):

```sh
g++ -O2 -std=c++17 -fsanitize=undefined -fno-sanitize-recover=all check_H.cpp -o check_H
./check_H 8 1000000
./check_H 16 1000000
python3 check_constants.py
```

Do not compile with `-DNDEBUG`, or run Python with `-O`: assertions implement checks. Successful runs return 0 only after all initial boxes have been covered and certified. A resource-limit result returns 2, not success.

## Enclosure argument

Write `a=c1, b=c2`, `A=(b+f*a-2*f)/2`, `B=(b-f*a)/2`. The source's integral J is `1/8` times the integral over `[0,1]` of the positive part of the affine interpolation `(1-t)A+tB`. Convexity makes the composite trapezoid rule an **upper bound** for any positive integer N; when A,B have the same sign on a box the integral is evaluated exactly. Every other term follows the source's definitions. The low-gate variance is upper-bounded by its cap unless the whole box satisfies `a+b <= 2`, when the sharper minimum is used. The five closed initial z intervals split at `3/4, 7/8, 1, 2`, so discontinuity boundaries remain covered by the appropriate adjacent branch. Each root also spans `a,b in [1/4,4]`.

A value interval stores integer endpoints scaled by `2^40`. Multiplication and division use signed 128-bit intermediate integers with floor/ceiling enclosure. For each fixed box upper function, interval automatic differentiation encloses derivatives along line segments, with hulls across max/min kinks. The function is locally Lipschitz and absolutely continuous along each segment. Thus a centered interval bound from the center value plus the derivative intervals times coordinate displacements is valid, as is the direct interval expression. The tighter of the two is used. A leaf is certified only if its integer upper bound is at most `floor(-2^40/3000)`. Otherwise both closed halves are recursively checked. There is no monotonicity pruning. A floating-point heuristic chooses the subdivision axis only; it cannot cause acceptance. Sanitizer runs detect signed-integer undefined behavior during replay.

The bound reported is the largest accepted upper endpoint, not an estimate of the actual global maximum. The final arithmetic sum checks and an endpoint counterexample are separate in `check_constants.py`.

## Endpoint finding

In Lemma 5.4, Case 2(c), p. 33, for `z=21/20, f=26/25, c2=f*z=273/250`, the paper's `0<d_R<=1/16` condition holds with `d_R=21/500`, and `u_M=0`. Its literal derivative estimate `h_tilde'(0+) <= -3f/512` is false there: the smooth derivative cancels and the left slope of the kink in t is zero, giving `h_tilde'(0+)=lambda=949/100000>0`. This is a repairable endpoint omission, not a counterexample to the theorem. The claimed uniform bound on h follows at the endpoint by continuity from `c2 < f*z`; the independent enclosure covers the endpoint directly.
