# Verification and reproduction for manuscript v2.0.1

[Current documentation](README.md) · [Getting started](GETTING_STARTED.md) · [Publication manifest](../../paper2/v2.0.1/PUBLICATION_MANIFEST.json) · [Documentation review](DOCUMENTATION_REVIEW.md)

Verification has several scopes. The table below states what each operation checks and what additional evidence remains separate. The commands are reproduction instructions; their presence does not assert a new execution. Observed results for this documentation change belong in [DOCUMENTATION_REVIEW.md](DOCUMENTATION_REVIEW.md) and source-bound external CI records.

The [review report](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Review_Report_2026-11-20.pdf), [58-finding revision record](../../paper2/v2.0.1/indices/review_findings.json) and [revision verification](../../paper2/v2.0.1/indices/revision_verification.json) describe the completed manuscript review. The [source ZIP](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip) includes `review/pdf_visual_qa.json`, `review/review_report_visual_qa.json` and `coverage/final_pdf_qa.json` for the inspected PDF snapshots. Earlier QA records in the same package remain tied to their original snapshots and page ranges.

| Check | Object checked | Separate question |
|---|---|---|
| Asset SHA-256 comparison | Exact PDF, ZIP, review PDF and exposed index bytes | Trust in the checksum source and mathematical correctness |
| Manuscript index / TeX build | Source labels, references, bibliography and typesetting | Lean execution and semantic equivalence |
| Included exact arithmetic | Specified model calculations and finite examples | Empirical identification and broader theorem hypotheses |
| Default Lean build | Pinned frozen-core build target | Separate research-root build |
| Research Lean build | Pinned research-root compilation | Independent case acceptance and theorem-to-paper equivalence |
| Generated instance replay / axiom audit | Actual reflected bounded instance and the stated axiom policy | Applicability to external data or an unrepresented model |
| Independent numerical checker | Receipt/input identity and exact relations within its contract | Lean kernel execution and empirical claims |
| Integrity / inherited source checks | Canonical protected objects, source identities and allowed changes | Mathematical adequacy or independent security approval |
| Case acceptance / empirical review | The separately declared criterion and its evidence | No other row automatically supplies this decision |

## 1. Verify the published bytes

From `paper2/v2.0.1` in the checkout:

```bash
sha256sum -c SHA256SUMS
```

The checksum file covers the published artifacts and seven exposed index copies. Check the exact names and digests against the [manifest](../../paper2/v2.0.1/PUBLICATION_MANIFEST.json). On platforms without `sha256sum`, compute SHA-256 with the platform's standard checksum utility and compare the same complete values. The source ZIP also contains its own `MANIFEST.json`; preserve its archive member identities when extracting it.

## 2. Rebuild the manuscript in a separate directory

Extract the [reviewed source ZIP](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip) and work in its `Permansson_Regimes_v2_0_1` directory. Use the Python/TeX requirements in the included `README.txt`.

```bash
bash build.sh
```

For an index/typesetting-only run:

```bash
python3 build_index.py
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

The index checks all 31 main sections and 16 appendices, label/reference consistency and bibliography keys. A sibling `PermanssonLean` checkout enables its source-path check. Compare the recorded engine versions if PDF byte reproducibility matters. Keep a newly generated `build/main.pdf` separate from the exact published reviewed artifact.

## 3. Reproduce included exact calculations

From that extracted source directory:

```bash
python3 computations/brown_mackay_exact.py
python3 computations/noninvariance_exact.py
python3 computations/x1_exact.py
```

The pricing script checks the frozen 601×601 grid, **361,201 pairs**, using exact arithmetic. The X1 record contains **272 checks**. The manuscript revision review separately records **389 exact checks**: 326 foundational, 43 quantitative and 20 specialized. These are different calculation sets and should not be added to a theorem count or described as a fresh complete Lean build.

The package includes a replay program for the 326 foundation checks. From the
same **fresh extracted source directory**, run:

```bash
python3 review/foundations_exact_checks.py
```

The script writes `review/foundations_exact_results.json` beside itself, so run
it in the extracted working copy and retain the original archive unchanged.
The three supplementary result records have different reproduction scope:

| Archive member, relative to the extracted source root | Recorded checks | Packaged replay program |
| --- | ---: | --- |
| `review/foundations_exact_results.json` | 326 | `review/foundations_exact_checks.py` |
| `review/quantitative_exact_checks.json` | 43 | No standalone replay program included |
| `review/specialized_exact_checks.json` | 20 | No standalone replay program included |

The latter two remain retained records in the original ZIP. A separately
identified [new reproduction addendum](../../paper2/reproduction/v2.0.1/README.md)
now provides commands for all 63 outputs. From the **repository root**, run:

```bash
python3 -B paper2/reproduction/v2.0.1/replay.py
```

Use `--full` for all computed values and source references, or
`--output /absolute/path/to/new-replay-results.json` to create a new result file.
The runner checks the immutable ZIP/member identities, computes the values
without passing archived answers to either arithmetic module, and compares exact
names, ordering, actual and expected strings. It also runs twelve additional
arithmetic controls and five runner controls, counted separately from the 63
retained outputs. The [new manifest](../../paper2/reproduction/v2.0.1/REPLAY_MANIFEST.json)
and [observed results](../../paper2/reproduction/v2.0.1/REPLAY_RESULTS.json) identify
this later work.

These are newly authored programs. Unrecorded endpoint, shell and Gram inputs
use explicitly declared new fixtures; matching outputs do not recover the
missing original programs or authenticate their original execution. The
[review verification index](../../paper2/v2.0.1/indices/revision_verification.json)
continues to state the original review scope. The original archive is unchanged.

Archived empirical/application workpacks retain their own specifications, input cutoffs and reproduction requirements. A compact repository fixture is not a reconstruction of unavailable historical raw data. The [earlier-paper concordance](EARLIER_PAPER_CONCORDANCE.md) identifies those roles and remaining gaps.

## 4. Build the pinned formal source

The mathematical source is `c5a36cd6189e2a249d5f4bc11f31698917dc8b10`. The toolchain is `leanprover/lean4:v4.34.0`, and the recorded mathlib commit is `5ed2965256430c3649e86755f9576b54eca72435`. Use the checked-in pins. From the repository root:

```bash
lake exe cache get
lake build
lake build PermanssonResearch
```

The default root directly lists 63 of the 64 frozen-core modules; `PermanssonLean/Regime/SurvivalBridge.lean` is explicitly not directly listed. The research root directly lists all 710 research modules at the source snapshot. Direct-import coverage is a source fact, distinct from the compiler execution result. The [research build guide](../RESEARCH_BUILD.md) and unchanged [Lean workflows](../../.github/workflows/) describe their original axiom and placeholder checks.

The reviewed paper does not claim a newly executed complete Lean build or individual semantic certification of all 7,690 lexical source units. Use the [mathematical crosswalk](MATHEMATICAL_CROSSWALK.md) to compare actual statements and hypotheses, then [residual status](RESIDUAL_STATUS.md) for stronger or separately evidenced requirements.

## 5. Application and native replay

Use [application compatibility](APPLICATION_COMPATIBILITY.md) to select the exact profile and its documented independent checker. Follow the [successor application](../../apps/permansson/application-successor/README.md) and [native C10](../../apps/permansson/closure-successor/README.md) / [C11](../../apps/permansson/closure-successor-c11/README.md) instructions for actual invocation, supported input bounds, generated Lean and receipt behavior.

Native replay requires a clean source checkout, the pinned compiler and a fresh output directory outside the repository. A source-bound theorem for a bounded reflected instance does not alter unexecuted runtime fields in another report. Preserve distinctions between exact numerical verification, Lean kernel execution, independent acceptance, release approval, empirical identification and publication approval.

For application documentation changes, run from the full repository root:

```bash
python -B -m unittest discover -s apps/permansson/application-successor/tests -p 'test_docs_registry.py' -v
python -B -m unittest discover -s apps/permansson/application-successor/tests -p 'test_inventory.py' -v
python -B -m unittest discover -s apps/permansson/application-successor/tests -p 'test_root_portability.py' -v
python apps/permansson/application-successor/scripts/inventory.py --check
```

The documentation test checks profile/family/report-field coverage, indexing and local links that remain inside a standalone application tree. The portability regression imports the four real affected test modules in shallow, overridden and ordinary repository layouts and exercises existing CLI/documentation checks; it does not require Lean. The inventory checker checks its shape, tracked paths and counts. It does not verify every candidate file hash. When documentation or test bytes change, compare their candidate SHA-256 values directly, refresh any existing candidate Git blob identity, and preserve recovery hashes, proof/trust states and historical fields. `--write-current` recomputes counts only; stage new tracked application files before using it.

## 6. Preserve repository and source identity

From a genuine, clean, committed full Git checkout with the referenced historical objects available:

```bash
python verification/repository_gate.py
python -B -m verification.integrity.preservation --repo . --candidate ACTUAL_COMMITTED_SHA --report /tmp/paper2-preservation.json
python verification/research/pr113_a2_successor_identity.py --repo . --head ACTUAL_COMMITTED_SHA --out /tmp/paper2-a2-identity.json
```

Replace `ACTUAL_COMMITTED_SHA` with the real full 40-character candidate SHA and choose fresh detached report paths outside the checkout. The unversioned A2 successor script above is the profile matching the audited f0 source. The staged active30 v2 proposal remains a separate unapproved profile; publication does not activate it or change workflow/guard rules.

After application inventory changes are committed, its detached local identity receipt can be produced from the repository root:

```bash
python apps/permansson/application-successor/scripts/inventory.py --receipt /tmp/paper2-inventory-receipt.json
```

That receipt records the actual head, trees and manifest digest; it is self-produced local identity evidence. CI run identities, independent review and source-controlled status records retain their separate roles. A tracked document cannot truthfully record its own unknown final containing commit before that commit exists.

## 7. Assess the claim at its literal scope

For each claim, read the paper statement, its source endpoint, the allowed input/initial/comparison domains, execution record and negative controls. Review the [seven named residuals and broader limits](RESIDUAL_STATUS.md). Historical 45-case decisions and 11 later claim records stay at their recorded statuses until their own independent criteria are met. Neither a new index nor a successful publication check changes them.

Read the [original verification guide](../../verification/README.md) together with
the current recipes below and the [version lineage](VERSION_LINEAGE.md).
Historical commands retain their original context; several produce new artifacts
or now discover a broader test suite. Report the exact source, environment,
command, exit status and observed evidence whenever claiming a new execution.

## 8. Use current recipes for historical material

These instructions clarify commands in the preserved verification, closure and
release guides. They leave the original guides and evidence unchanged. The
[historical documentation errata](HISTORICAL_DOCUMENTATION_ERRATA.md) identify the
associated editorial and fixture caveats. Start each command below at the
**repository root** unless another directory is stated.

### Python-only D0 finite-menu checks

With the historical D0 environment, CPython 3.13, limit discovery to D0 tests:

```bash
python3 -B -m unittest discover -s verification/research -p 'test_d0_*.py' -v
```

This selects the 36 D0 Python tests present at the documentation-audit baseline;
it does not invoke Lean. To generate new golden certificates and independently
recheck one, choose a fresh external scratch directory:

```bash
d0_output_dir=$(mktemp -d /tmp/permansson-d0-XXXXXX)
python3 -B verification/research/d0_golden.py "$d0_output_dir"
python3 -B verification/research/d0_recheck_certificate.py "$d0_output_dir/python_three_state.json"
```

The independent rechecker uses forward probability flow. Its `VALID` result
means consistency with the supplied finite problem, under the
`EXACT_FINITE_MENU_CALCULATION` scope. To check a trusted input identity, supply
`--expected-problem-sha256` with an independently trusted digest. A digest inside
the same certificate does not authenticate that input.

By contrast, discovery with `-p 'test_*.py'` is the **full research suite**.
It includes mandatory compiler fixtures and declaration audits. Run it only
after the pinned compiler, dependencies and both build targets in the
[research build guide](../RESEARCH_BUILD.md#reproduce-locally) are available.
The closure audits also retain their per-module diagnostic requirements under
`.lake/closure-build`; inspect each driver's requirements as explained in the
[historical closure guide](../../research/paper_closures/README.md).
Unavailable imports, compiler artifacts or diagnostic records are failures or
invalid evidence, not successful negative controls.

### Read-only checks and artifact producers

| Operation | What it writes | Current invocation rule |
| --- | --- | --- |
| `paper_closure_imports.py` without `--write` | No source changes | Omit `--write` for an import-coverage check |
| `paper_closure_source_audit.py` | A new canonical-source identity report | Supply the explicit scratch `--output` below |
| `paper_closure_strategy_audit.py`, `paper_closure_analytic_audit.py` and their closure-audit wrappers | New compiler/audit records; some default receipt paths are tracked historical evidence | Use an explicit, distinct `--output` under `.lake/closure-build` |
| `paper_closure_acceptance_evidence.py` | A new ledger; `--refresh` also executes exact and Lean evidence checks | Supply `--output-dir .lake/acceptance-evidence-report`, including for refresh |
| `release/v0.2.0/verify_release.py` | No shipped-kit changes | Verify the accepted kit without `--allow-draft`; historical Git objects are required |
| `release/v0.2.0/build_release.py` | Rewrites its kit's PDF, TeX, maps and manifest in place | Use only an isolated disposable historical worktree or copy |
| `release/mathematical-closure-1/build.py` | A new detached draft, source archive and build receipt | Use a fresh output directory outside the repository, as below |

After the pinned Lean research build and required module diagnostics, these
examples keep generated reports separate from retained evidence:

```bash
mkdir -p .lake/closure-build
python3 -B verification/research/paper_closure_source_audit.py --output .lake/closure-build/source-audit.json
python3 -B verification/research/paper_closure_strategy_audit.py --output .lake/closure-build/strategy-audit.json
python3 -B verification/research/paper_closure_analytic_audit.py --output .lake/closure-build/analytic-audit.json
python3 -B verification/research/paper_closure_risk_lp_audit.py --output .lake/closure-build/risk-lp-audit.json
python3 -B verification/research/paper_closure_acceptance_evidence.py --refresh --output-dir .lake/acceptance-evidence-report
```

The other `paper_closure_*_audit.py` wrappers in the historical closure recipe
delegate to the strategy or analytic auditor and accept the same `--output`
option. Give each a distinct filename. Their `.lake` diagnostics and compiled
artifacts remain necessary; an output option does not remove those prerequisites.
The analytic auditor records its signatures path relative to the repository,
so an arbitrary external `/tmp` output is not a substitute for this ignored
in-repository destination. The separate `audit_*` drivers in that recipe use
their declared `.lake` scratch locations. Inspect any other producer's output
contract before execution; if it cannot redirect writes away from retained
artifacts, run it in an isolated disposable historical worktree or copy.

Fresh output means a new execution record. Preserve any earlier scratch report
you intend to cite before rerunning a producer into the same destination.
Generating a valid partial acceptance ledger can return success; its individual
case dispositions remain authoritative. Do not copy the generated ledger over
the published ledger or interpret its process exit status as independent
mathematical acceptance.

For the shipped accepted companion, use the read-only verifier:

```bash
python3 -B release/v0.2.0/verify_release.py
```

Install the kit's pinned [requirements](../../release/v0.2.0/requirements.txt)
and fetch its referenced source, base and synthetic-merge Git objects first, as
specified in the [release guide](../../release/v0.2.0/README.md#final-acceptance-evidence).
The verifier checks the captured release records; it does not independently
obtain new GitHub review or CI evidence. For any regeneration, check
`git diff --name-only` before and after: none of the preserved tracked artifacts
should change in the working checkout.

### Detached original closure-draft build

The original draft records starting main
`17c315f7df7abf457eb94d393bd526d46da6f6f4`. That is its historical starting point,
not the current branch head or a new release identity. Its README's escaped
Markdown fences are corrected here for readability; the thirteen original
manuscript source files remain unchanged.

With the draft's TeX dependencies, BibTeX and Poppler installed, select a fresh
external directory (the example below must not already contain evidence to
preserve), then run the original two commands from the repository root:

```bash
python3 release/mathematical-closure-1/build.py --mode draft --render --out /tmp/permansson-closure
python3 release/mathematical-closure-1/verify_release.py --manifest /tmp/permansson-closure/manifest.lock.json
```

The builder binds the new receipt to the actual checkout head and copies all
thirteen original source members into the new archive. The verifier checks
archive/source integrity and returns `accepted: false` for this draft.
**DRAFT / NOT ACCEPTED / NOT PUBLISHED** remains the applicable status.
Rendering pages does not itself perform visual inspection or independent review.
See the [closure-draft erratum](HISTORICAL_DOCUMENTATION_ERRATA.md#original-closure-draft-formatting-and-abstract)
for the abstract copyedit reserved for a separately identified successor edition.
