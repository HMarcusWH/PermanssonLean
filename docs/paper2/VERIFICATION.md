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

The latter two are retained result records. Their presence supports inspection
of the recorded checks; it does not supply a command to rerun them. A later
reconstruction would be new reproduction work with its own source and receipt.
The [review verification index](../../paper2/v2.0.1/indices/revision_verification.json)
states the original review scope.

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
python apps/permansson/application-successor/scripts/inventory.py --check
```

The documentation test checks profile/family/report-field coverage, indexing and local links that remain inside a standalone application tree. The inventory checker checks its shape, tracked paths and counts. It does not verify every candidate document hash. When documentation bytes change, compare those SHA-256 values directly and refresh truthful current documentation entries while preserving historical fields. `--write-current` recomputes counts only; stage new tracked application files before using it.

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

Use the [original verification guide](../../verification/README.md) for historical package-specific commands and the [version lineage](VERSION_LINEAGE.md) to distinguish their authorities. Report the exact source, environment, command, exit status and observed evidence whenever claiming a new execution.
