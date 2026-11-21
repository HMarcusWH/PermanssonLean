# Paper v2.0.1: compatibility and corrections

[Current documentation](README.md) · [Mathematical crosswalk](MATHEMATICAL_CROSSWALK.md) · [Glossary](GLOSSARY.md) · [Residual status](RESIDUAL_STATUS.md)

The reviewed manuscript **v2.0.1** incorporates **58 recorded corrections and clarifications** to the internal draft 2.0. They have mixed mathematical and editorial significance. The exact [review-findings register](../../paper2/v2.0.1/indices/review_findings.json), [revision-verification record](../../paper2/v2.0.1/indices/revision_verification.json) and [review-report PDF](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Review_Report_2026-11-20.pdf) are the authoritative records.

The revision does not constitute 58 alleged defects in the earlier published papers or the repository's Lean proofs. Several changes make an existing formal source premise explicit in the manuscript; some correct a manuscript argument, predicate conflation or notation; others repair bibliography and layout. Historical source/specification files and acceptance dispositions retain their identities.

The separately dated [historical documentation errata](HISTORICAL_DOCUMENTATION_ERRATA.md)
record corrections found after this manuscript review. They include the
[Q-05 baseline/intervention sentence](HISTORICAL_DOCUMENTATION_ERRATA.md#q05-baseline-and-intervention-sentence),
the original closure draft's editorial defects and a legacy fixture's narrative
inconsistency. These current explanations leave the historical source bytes and
the 58-item manuscript revision register unchanged.

The final reviewed PDF has **218 pages** and SHA-256 `56a6ea1538e0a31f8555f4457b706e96d159ed96d3e1add7bba7b6847e4b3d17`. The earlier 217-page draft and 219-page review candidate are distinct artifacts retained in the review history, not interchangeable names for the delivered PDF. See the [publication manifest](../../paper2/v2.0.1/PUBLICATION_MANIFEST.json).

## Consequential mathematical distinctions

### X1: region descriptor and reachable descriptor laws

`DescriptorHasTwoValues` fails on the declared replete region because `h(q,x)=x` is constant there. The different predicate `IsDescriptorNondegenerate` holds through same-start finite-time descriptor laws whose true masses are 1 and 13/20. Leakage still obstructs Exact GR. Passing to the complete comparison domain and proving a positive finite-horizon constitutive margin does not repair every original regime gate.

The occupation discussion also separates class-dependent **joint-state** limits, equal world pushforwards within each mode and unequal targets between the two modes. The historical lane sentence saying time-zero equality does not *establish* nondegeneracy is valid; the manuscript correction must not be projected onto that sentence as a source error. Review IDs: `CTRL-07`, `CTRL-08`. Paper routes: [`sec:C23`](MATHEMATICAL_CROSSWALK.md#c23) and [`app:L`](MATHEMATICAL_CROSSWALK.md#appendix-l).

### Shell normalization and specialized conditionality

In the finite real one-shell setting, let $T$ be the self-adjoint successor compression, $W$ the inherited predecessor space and $P_W$ its orthogonal projection. Assume $H=P_WT|_W\geq 0$ and $\lambda<0$; then $R=(H-\lambda I)^{-1}$ exists. For a raw nonzero shell vector $c$, put $b=P_WTc$, $e=c/\lVert c\rVert$ and $b_e=b/\lVert c\rVert$. The scalar secular function $F(\lambda)=\langle e,Te\rangle-\lambda-\langle b_e,Rb_e\rangle$ has derivative

$$
F'(\lambda)=-1-\lVert Rb_e\rVert^2
           =-1-\frac{\lVert Rb\rVert^2}{\lVert c\rVert^2}.
$$

The strict negative sign survives the correction. The omitted norm factor matters numerically for a nonunit vector. The scalar-shell result has one-dimensional shell scope; general shells require matrix Schur reasoning. Singular eliminated blocks require compatibility and a preimage or restricted inverse. The complex inner product is conjugate-linear in its first argument, and the Hermitian self-form must be real before a sign comparison is made. Review IDs: `ROOT-06` through `ROOT-09`; paper routes: [`sec:C26`](MATHEMATICAL_CROSSWALK.md#c26) and [`app:M`](MATHEMATICAL_CROSSWALK.md#appendix-m). The natural analytic/source identification assumptions remain explicit.

### Least-positive blocks and lower-set transport

A least-positive block must itself satisfy the positivity predicate and be below every positive admitted block. Minimal positivity similarly includes positivity as well as absence of a smaller positive member. Nonempty fibers or surjectivity justify strict inverse-image inclusion; restriction of the admitted carrier concerns availability of lower alternatives needed for lifting. These are separate conditions. Review IDs: `Q01`, `Q02`, `Q12`; paper routes: [`sec:C11`](MATHEMATICAL_CROSSWALK.md#c11) and [`app:F`](MATHEMATICAL_CROSSWALK.md#appendix-f).

### Probability mass and path/score scope

The common-mass total-variation estimate uses probability initial laws. The bundled primitive interface includes the separately requested joint-state `(Y,Y)` common-kernel condition. For a nonzero retained infinite product, summability must be accompanied by initial defect below one and every step defect below one; a single unit defect destroys retained mass. Bounds for a declared score sequence use that sequence's actual marginal-error premises and do not automatically control survival forever. The canonical initial-mismatch adapter remains separately identified under [Later Q1](RESIDUAL_STATUS.md#later-q1). Review IDs: `Q03`, `Q04`, `Q05`, `Q13`; paper routes: [`sec:C12`](MATHEMATICAL_CROSSWALK.md#c12), [`sec:C13`](MATHEMATICAL_CROSSWALK.md#c13) and [`app:G`](MATHEMATICAL_CROSSWALK.md#appendix-g).

### Metrics, measurable selectors and four process laws

An invariant probability constructor requires a nonempty state space. The generic empirical-limit selector is stated in a complete separable metric law space with its Borel sigma-algebra and measurable empirical-law maps. A genuine metric is needed for the recurrent-class uniqueness implication; a zero pseudometric can identify distinct states while an identity chain has multiple classes. Continuous-descriptor scalar/compact weak profiles and the separate measurable-descriptor first-moment profile keep their actual assumptions. The robustness adapter needs all four actual global property factorizations and the stated dual row-defect metric. Review IDs: `Q06` through `Q10`; paper routes: [`sec:C14`](MATHEMATICAL_CROSSWALK.md#c14), [`sec:C15`](MATHEMATICAL_CROSSWALK.md#c15) and [`app:H`](MATHEMATICAL_CROSSWALK.md#appendix-h).

### Chronology, nonempty control sets and null histories

Finite hidden, observation and decision sets, frozen intervention menus and comparison sets require their relevant nonemptiness hypotheses. The original comparison-set gate includes path-law nontriviality. An all-histories autonomy statement uses the model-specified next-key row, including at null histories, rather than an arbitrary version of a conditional distribution there. Pushforward notation places the map before the measure. Residence uses `j + m ≤ t`, and the worst-start set minimizes the pointwise absolute effect. Review IDs: `CTRL-01`, `CTRL-03`, `CTRL-05`, `CTRL-10` through `CTRL-14`; paper routes: [`sec:C18`](MATHEMATICAL_CROSSWALK.md#c18), [`sec:C20`](MATHEMATICAL_CROSSWALK.md#c20), [`sec:C24`](MATHEMATICAL_CROSSWALK.md#c24), [`app:J`](MATHEMATICAL_CROSSWALK.md#appendix-j) and [`app:K`](MATHEMATICAL_CROSSWALK.md#appendix-k).

### Measurement and joint coverage

The outer-certificate theorem assumes a nonempty random uncertainty set, a level in `[0,1]`, a measurable coverage event and actual simultaneous coverage. Deterministic completion bounds use normalized observations and coverage in `[0,1]`, with zero contribution at zero coverage. They do not manufacture that statistical coverage premise. Reporting-rate identification assumes fixed known positive exposure and a nonnegative latent rate; inactive-channel equality is tied to the declared finite observation window. The pricing one-transition statement is basin-root-qualified. The GSCRD consensus rule leaves calibration disagreement unknown and is not ordinary Boolean conjunction. The certificate has **nine distinct coordinates**, without a claim of their statistical independence. Review IDs: `ROOT-02` through `ROOT-05`, `ROOT-10` through `ROOT-12`; paper routes: [`sec:C28`](MATHEMATICAL_CROSSWALK.md#c28) and [`app:N`](MATHEMATICAL_CROSSWALK.md#appendix-n).

### Foundation profiles and formal specializations

Grounding maps are measurable. The EGR embedding handles both the reference-mass and nonempty-interior branches. The finite occupation proof constructs a measurable stopped endpoint explicitly; the regeneration transfer uses the exact forward and reverse average shifts. Other repairs state the filtration, extended-valued measurable Green competitors, leakage range and joint-state obstruction precisely. The paper's coordinate-change argument is distinguished from same-space formal endpoints, and its general L1 argument from the cited constant-approximant specialization. Review IDs: `FND-001` through `FND-013`. These differences are recorded in the [mathematical crosswalk](MATHEMATICAL_CROSSWALK.md), not hidden behind a blanket claim that every prose theorem is a verbatim Lean statement.

## Complete correction register

The 58 rows below preserve the unique finding IDs. The exact JSON retains the original reviewers' varying severity vocabularies, evidence and consolidation provenance. Supplementary findings already associated with these IDs are not counted again. Manuscript file paths are members of the source ZIP.

| Finding | Manuscript location | Applied correction / reading summary |
|---|---|---|
| FND-001 | sections/C05.tex / eq:C05-groundingmaps | Added measurable G, B_G and h_G to the setup, preserving the original grounded definition. |
| FND-002 | sections/C06.tex / thm:C06-embedding | Added int(S_E x B)=S_E x int(B) and the nonempty S_E argument in both directions. |
| FND-003 | appendices/D_occupation.tex / eq:D-dirac-law | Constructed Z directly as the measurable stopped coordinate Y_{T_C} with a fixed fallback in the nonempty ambient space Y; gave the countable inverse-image formula and lambda(C)=1 from almost-sure absorption. The finite source case remains unchanged. |
| FND-004 | appendices/E_ergodic.tex / lem:E-regenerative-transfer | Replaced the shortcut with the exact forward and reverse average-reindexing identities. Only the fixed initial reward is divided by T. |
| FND-005 | sections/C05.tex / thm:C05-representation | Explicitly distinguished the paper coordinate-change proof from the same-space formal source results. |
| FND-006 | appendices/E_ergodic.tex / cor:E-L1 | Added an explicit scope sentence identifying that formal specialization and its regenerative use. |
| FND-007 | appendices/D_occupation.tex / lem:D-block | Specified a nonempty standard Borel state space, measurable K-invariant C, the hitting-time definition, 0<p<=1, and the explicit quantifier over the stated starting states. |
| FND-008 | appendices/C_foundations.tex / prop:C-Green | Added extended-valued measurable functions. |
| FND-009 | appendices/D_occupation.tex / lem:D-innovation | Introduced the filtration explicitly and retained F_{t+1}-measurability with zero F_t conditional mean. |
| FND-010 | sections/C04.tex / def:C04-quasi | Stated 0<=epsilon<=1 before using (1-epsilon)^H. |
| FND-011 | sections/C10.tex / thm:C10-occupation | Specified the same sample length T on the shifted path. |
| FND-012 | appendices/A_foundations.tex / ex:A-escaping-Dirac | Added n>=1. |
| FND-013 | appendices/D_occupation.tex / final subsection: Two elementary original-gate obstructions | Replaced physical space by joint state space. |
| Q01 | sections/C11.tex, def:C11:minimal | Required P(D) as well as containment in every positive admitted block. |
| Q02 | sections/C11.tex, thm:C11:minimality proof | Explicitly invoked the first transport hypothesis at b=a. |
| Q03 | sections/C12.tex, C12:primitiveTV | Recorded the (Y,Y) instance and its automatic availability under countably generated primitive output sigma-algebras. |
| Q04 | sections/C13.tex, C13:commonmass | Explicitly specified probability initial laws. |
| Q05 | sections/C13.tex, C13:wholepath | Added epsilon<1 and eta_n<1 for every n as requirements for nontrivial retained mass. |
| Q06 | sections/C14.tex, thm:C14:invariant | Made nonempty Y explicit in the theorem statement. |
| Q07 | sections/C15.tex, C15:frozenproperty; appendices/H_metric_occupation.tex, H:fixedproperty | Specified a complete separable metric law space, its Borel sigma-algebra and measurability of each empirical-law map; made Phi explicitly real-valued. Mirrored the corrected hypotheses in Appendix H. |
| Q08 | sections/C15.tex, C15:profiles | Required a genuine metric for this uniqueness implication and explained why a pseudometric identifying distinct states is insufficient. |
| Q09 | sections/C15.tex, C15:profiles | Stated these source assumptions before the scalar/compact weak-topology profiles, keeping the distinct measurable-descriptor first-moment profile separate. |
| Q10 | sections/C15.tex, thm:C15:margin | Specified separable Borel metric spaces and row defects in the dual sense of equation C14:dual. |
| Q11 | appendices/F_grammar.tex, F:boolean | Gave e_alpha, e_U and e_alphaU separate headed columns and individual entries. |
| Q12 | appendices/F_grammar.tex, F:orders | Separated nonempty-fiber/surjectivity requirements for strictness from absence of lower alternatives in a restricted admitted carrier. |
| Q13 | appendices/G_path_transport.tex, G:discount | Replaced that categorical sentence with the exact limitation: the bound controls the declared score sequence under its marginal-error premises, which do not automatically cover survival forever. |
| CTRL-01 | sections/C18.tex | A probability row and a fixed default belief require a nonempty state space; normalized observation rows also require a nonempty observation space. This makes already intended existence assumptions explicit. |
| CTRL-02 | sections/C18.tex | The equality is a weighted sum of scalar continuation scores. Replace punctuation by multiplication and group the inner product. |
| CTRL-03 | sections/C18.tex | Both cited monitored-history theorems have [Nonempty D]. Empty D has no behavioral control probability row and no maximizing tree at positive horizon. |
| CTRL-04 | sections/C20.tex | The class contributes its absorption weight multiplied by the all-true indicator. |
| CTRL-05 | sections/C20.tex | The original comparison-set object supplies two distinct initial path laws, hence nonemptiness, and the checked input supplies a positive menu size. State those premises where the finite extrema are introduced. |
| CTRL-06 | sections/C22.tex | A probability atom is the product of controller, Nature, and transition probabilities; use multiplication spacing. |
| CTRL-07 | sections/C23.tex | Distinguish joint-state occupation laws from their physical-world pushforwards, and distinguish within-mode class agreement from between-mode target differences. |
| CTRL-08 | sections/C23.tex | Retain the two valid Exact-GR objections: DescriptorHasTwoValues fails and invariance fails. Explain that IsDescriptorNondegenerate holds using the same basin start at times 0 and 1. These are distinct predicates, so the original claim that expansion repairs neither descriptor nondegeneracy nor invariance needed correction. |
| CTRL-09 | sections/C24.tex | Use explicit measure evaluation parentheses and integration spacing. |
| CTRL-10 | sections/C24.tex | The source defines the next-key row by kernel composition at every history. Make this pointwise object explicit; no stronger observational implication follows. |
| CTRL-11 | sections/C24.tex | Use the explicit attachment map and write map-pushforward-measure, matching the paper definition and Appendix L. |
| CTRL-12 | appendices/J_control.tex | Use j+m<=t so early horizons automatically have no complete block and every index stays in the observed word. |
| CTRL-13 | appendices/J_control.tex | Place the coordinate map before the pushforward marker, as elsewhere in the manuscript. |
| CTRL-14 | appendices/K_algorithms.tex | Use Delta_i, the pointwise absolute effect already defined in C20, because the receipt minimizes effects rather than treated event probabilities. |
| ROOT-01 | sections/C29.tex: native replay source note | Replaced them with emit_golden_bridge and emit_source; all printed source labels now pass a literal-presence check. |
| ROOT-02 | sections/C28.tex: thm:outer-certificate | Stated a nonempty random set, 0 <= alpha <= 1, and a measurable coverage event explicitly. The theorem remains conditional on actual joint coverage. |
| ROOT-03 | sections/C28.tex: measurement windows | Specified coverage and observed normalized values in [0,1], with zero weighted contribution at zero coverage and no imputed observation value. |
| ROOT-04 | appendices/N_cases.tex: prop:poisson-thinning | Specified a fixed known positive exposure and a nonnegative latent rate. |
| ROOT-05 | appendices/N_cases.tex: prop:inactive-channel | Fixed a finite observation horizon and a common zero-input protocol, and proved equality of observed path laws only on that window. |
| ROOT-06 | sections/C26.tex: opening | Stated conjugate-linearity in the first argument at the start of the specialized track. |
| ROOT-07 | sections/C26.tex: eq:C26:derivative; appendices/M_specialized.tex: M:firstbad | Introduced e=c/&#124;&#124;c&#124;&#124;, b_e=b/&#124;&#124;c&#124;&#124; and theta=<e,Te>; the derivative is -1-&#124;&#124;R b_e&#124;&#124;^2 = -1-&#124;&#124;R b&#124;&#124;^2/&#124;&#124;c&#124;&#124;^2. The strict negative sign is unchanged. An exact nonunit-shell counterexample detects the omitted factor. |
| ROOT-08 | appendices/M_specialized.tex: M:firstbad | Defined c_- as the odd shell projection of g and c_+ as the even shell projection of D^{-1}g, making coefficient-one normalization in the transfer identities explicit. |
| ROOT-09 | sections/C26.tex: C26:detection | Used conjugation symmetry of the complete spectral multiset and absolute convergence to state Hermitian symmetry and real self-values. |
| ROOT-10 | sections/C28.tex: pricing descriptor paragraph | Restricted the one-transition statement explicitly to every basin root. All-basin occupation and invariance conclusions remain unchanged. |
| ROOT-11 | sections/C28.tex: outer-set interpretation and certificate coordinates | Specified uniformity over the model family and comparison set, and changed nine orthogonal coordinates to nine distinct coordinates. |
| ROOT-12 | sections/C28.tex: GSCRD predicate P3 | Clarified that the source uses a consensus rule, leaving disagreement between the two calibrations unknown. The archived rule itself is preserved. |
| ROOT-13 | references.bib: RudolfWang2025 | Corrected the authors to Daniel Rudolf and Andi Q. Wang. |
| ROOT-14 | sections/C28.tex; references.bib: BrownMacKay2025 | Added the NBER working paper citation and retained the January 2026 revision identity used by the frozen workpack. The current later revision is not silently substituted. |
| ROOT-15 | build_index.py | Expanded the checker to all 49 content inputs, input-file existence, unlabeled numbered items, and literal source-label presence. The check explicitly remains separate from semantic equivalence. |
| ROOT-16 | sections/C01.tex; main.tex; preamble.tex; README.txt | Added nonbreaking part references, improved the reading-guide wording, and marked the corrected source and PDF as reviewed draft v2.0.1. The baseline and source diff are preserved. |
| ROOT-17 | appendices/D_occupation.tex: final paragraph | Shortened the final paragraph without changing its two obstruction claims, to remove the source-only page. |
| ROOT-18 | sections/C06.tex: source-result wording | Changed the wording to distinct source results to remove the split without altering the mathematical assertion. |

## What the recorded review establishes

The register records 389 supplementary exact checks: 326 foundations, 43 quantitative and 20 specialized. A separate X1 record contains 272 exact checks. The pricing certificate enumerates 361,201 declared finite-grid trigger pairs; those pairs are not counted as test assertions or added to the 389. These are saved manuscript-review observations, not new executions performed by this documentation update.

The structural record has 147 numbered items, 603 labels and 538 source-citation occurrences, with no missing references, bibliography keys, input files, cited source paths or literal source labels. Literal source-label presence is a structural check. It does not prove elaborated type equivalence. The earlier saved 536-citation screen remains an explicitly earlier review snapshot; the refreshed final record is 538.

The manuscript review was internal AI-assisted mathematical, source, editorial and visual review. It did not perform a fresh full-repository Lean build, independently certify equivalence of all 7,690 lexical units, reprove the complete specialized analytic source package or issue empirical certification of historical applications. Historical-clause and Appendix P obligations remain visible in [earlier-paper concordance](EARLIER_PAPER_CONCORDANCE.md) and [residual status](RESIDUAL_STATUS.md). Execution and review evidence can be followed through [verification](VERIFICATION.md).

## Compatibility policy

The correction record applies to the reviewed manuscript edition. It does not change the frozen v0.1.8 formalization, Application Standard wire vocabulary, source guards, software versions or historical release/case decisions. A later mathematical or implementation change requires its own statement, source identity and evidence. A later editorial change to the paper requires a new artifact/version record rather than silently replacing the reviewed PDF bytes.
