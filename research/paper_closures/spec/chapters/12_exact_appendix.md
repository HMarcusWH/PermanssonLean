# X1 exact arithmetic appendix

These are candidate rational certificate literals, computed independently for this paper specification. The final Lean implementation must prove their equality to the actual typed kernels and original property. Full state order, matrices, all horizons zero through three and all 54 effects are in `certificates/x1_exact_tables.json`.

## Horizon-three outputs at all nine replete starts

For E, all nine starts have baseline and reset value $\frac{227}{500}$, and action/joint value $\frac{3171}{4000}$. The corresponding effects are $\frac{271}{800}$, $0$, $\frac{271}{800}$.

For L the following table retains every start. Action and joint terminal values coincide, but their full next-state and path laws need not coincide.

| Memory $(q_1,q_2)$ | Baseline | Action or joint | Update reset |
|---|---:|---:|---:|
| $(0,0)$ | $\frac{2062936471}{6400000000}$ | $\frac{3171}{4000}$ | $\frac{20543}{51200}$ |
| $(0,1)$ | $\frac{686994469}{2560000000}$ | $\frac{3171}{4000}$ | $\frac{185549}{512000}$ |
| $(0,2)$ | $\frac{121690031}{512000000}$ | $\frac{3171}{4000}$ | $\frac{41417}{128000}$ |
| $(1,0)$ | $\frac{686994469}{2560000000}$ | $\frac{3171}{4000}$ | $\frac{185549}{512000}$ |
| $(1,1)$ | $\frac{8381459}{32000000}$ | $\frac{3171}{4000}$ | $\frac{41417}{128000}$ |
| $(1,2)$ | $\frac{1172162957}{5120000000}$ | $\frac{3171}{4000}$ | $\frac{145787}{512000}$ |
| $(2,0)$ | $\frac{121690031}{512000000}$ | $\frac{3171}{4000}$ | $\frac{41417}{128000}$ |
| $(2,1)$ | $\frac{1172162957}{5120000000}$ | $\frac{3171}{4000}$ | $\frac{145787}{512000}$ |
| $(2,2)$ | $\frac{5050479049}{25600000000}$ | $\frac{3171}{4000}$ | $\frac{62953}{256000}$ |

## Exact absolute effects

| Memory | Action or joint effect | Update effect |
|---|---:|---:|
| $(0,0)$ | $\frac{3010663529}{6400000000}$ | $\frac{504938529}{6400000000}$ |
| $(0,1)$ | $\frac{1342445531}{2560000000}$ | $\frac{240750531}{2560000000}$ |
| $(0,2)$ | $\frac{284197969}{512000000}$ | $\frac{43977969}{512000000}$ |
| $(1,0)$ | $\frac{1342445531}{2560000000}$ | $\frac{240750531}{2560000000}$ |
| $(1,1)$ | $\frac{16986541}{32000000}$ | $\frac{1972791}{32000000}$ |
| $(1,2)$ | $\frac{2886717043}{5120000000}$ | $\frac{285707043}{5120000000}$ |
| $(2,0)$ | $\frac{284197969}{512000000}$ | $\frac{43977969}{512000000}$ |
| $(2,1)$ | $\frac{2886717043}{5120000000}$ | $\frac{285707043}{5120000000}$ |
| $(2,2)$ | $\frac{15243920951}{25600000000}$ | $\frac{1244820951}{25600000000}$ |

The learner action/joint infimum is attained at $(0,0)$; its update infimum at $(2,2)$. An illustrative point calculation at $(1,1)$ cannot replace either full comparison-domain minimum.

## Executed-check record

The included independent checker passed 27 test methods with zero failures, errors or skips. It additionally rejects mutations of each of the 54 supplied absolute effects, each of the six minima, a minimizing start, a stochastic-but-wrong matrix, a horizon, a table entry and intervention labels. This is executed finite evidence, not a deductive check of the entire manuscript or a Lean build.
