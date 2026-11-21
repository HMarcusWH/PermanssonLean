# Paper v2.0.1 documentation review

[Current documentation](README.md) · [Manuscript review](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Review_Report_2026-11-20.pdf) · [Verification guide](VERIFICATION.md)

**Initial review date:** 20 November 2026; **documentation follow-up:** 21 November
2026. The [merged-head record and follow-up scope](#merged-head-verification-and-21-november-follow-up)
below give the later observed state. Earlier candidate counts and execution
records retain their original scope. This record concerns publication metadata and
repository documentation, plus the later reproduction and test-portability
follow-up. The mathematical/editorial manuscript review is a
separate record with its own computations, source checks and limitations.

## Source identities and change scope

| Role | Identity |
| --- | --- |
| Mathematical source | `c5a36cd6189e2a249d5f4bc11f31698917dc8b10` |
| Pre-upload documentation baseline | `f0dee1c11a20f96c9a11b380e942b9252e6ebe44` |
| First exact manuscript-asset commit | `5160a32eecec9d5f17713416f7f58ec2df67e744` |
| Initial publication package review head | `8630e80b604223aa0fadff92d6a7c2749cd8be5b` in [PR #128](https://github.com/HMarcusWH/PermanssonLean/pull/128) |
| New reproduction addendum head | `39f97d409e2731d286bbf5b835a8ae6acc038667` in [PR #128](https://github.com/HMarcusWH/PermanssonLean/pull/128) |

The current-documentation change adds twelve `docs/paper2/` pages, updates the
four permitted repository entry points, and completes reading links in the two
new publication hubs. The exact PDF, source ZIP, review PDF and seven copied
indexes remain unchanged. The initial publication phase had fifteen new paths;
the later reproduction addendum adds six. This Markdown phase adds twelve
current-documentation pages.

The original 41-path plan updated twelve preexisting Markdown documents and
one application inventory JSON, and added twenty-eight paths including the PDF.
The subsequent request to investigate and implement the remaining fixes extends
that scope to **55 paths: 35 additions and 20 updates**. The fourteen added
scope entries are six new reproduction files, one new application regression,
four existing test modules and three additional bridge documents. The twenty
updates comprise fifteen Markdown files, four test modules and one inventory.
Application-local fixes and manifest reconciliation belong to the dependent
application phase; this central-documentation record does not assert that its
later candidate hashes have already been reconciled.

## Coverage inspected

| Object | Documentation result | Limit |
| --- | --- | --- |
| Paper structure | All 31 sections and 16 appendices have literal crosswalk anchors | Navigation is not a new theorem-equivalence proof |
| Numbered items | All 147 numbered mathematical items have a paper route | Item count includes the manuscript's different statement kinds |
| Printed source citations | All 538 source-anchor occurrences are routed | Occurrences may repeat a file or declaration |
| Lean inventory | All 798 files are accounted for by the reviewed grouped index; 64 core, 710 research, 24 other | 7,690 lexical declaration/example units are not individual semantic certifications |
| Earlier-paper obligations | 51 obligations and 201 requirement rows retain their exact dispositions | Five historical-delta entries, one wording clarification and three incomplete reconciliations remain distinguished |
| Preserved guide | All 46 chapters, 56 literal cases and 166 catalog entries have reading routes | Existing 15/30/11 case dispositions remain unchanged |
| Application scope | All 26 exact profiles, commands, checkers and 24 candidate families are mapped | Numeric bounds and Lean reflection limits remain separate |
| Corrections | All 58 reviewed findings are indexed | These concern internal draft 2.0-to-2.0.1 manuscript changes |
| Residuals | Seven named Appendix P obligations and broader limits remain visible | Theorem presence, reconciliation, execution, acceptance and identification are separate |

## Publication checks already observed

At the initial publication package head `8630e80b604223aa0fadff92d6a7c2749cd8be5b`:

- All ten asset/index SHA-256 checks passed; the seven public indexes match their
  named reviewed ZIP members byte-for-byte.
- Publication navigation checked 39 inline links with no missing destination.
- All 341 text documents designated for preservation and the preserved guide
  edition objects match the planning baseline.
- The existing repository gate completed **67/67** checks.
- The existing canonical frozen-source preservation gate returned **PASS**.
- The current A2 source-identity check completed with its stated
  `SOURCE_IDENTITY_CANDIDATE_NEEDS_INDEPENDENT_SECURITY_REVIEW` result. This is its
  source-identity scope; it is not independent security or mathematical approval.

## Current-documentation inspection

The completed maps were generated from the reviewed source indexes and the
preserved guide's literal chapter, case and catalog records. Their structural
checks compared actual identifiers, titles, criteria, dispositions and paths;
the 201 earlier-paper rows retain the 192/5/1/3 status distribution. Existing
heading anchors and the exact historical README title/package-version strings
required by the repository gate were retained.

Independent cross-reviews checked all 47 section/appendix routes, 147 numbered
items, 538 source-citation occurrences, 201 earlier-paper content rows and 58
correction identifiers against the reviewed records. They also checked the
46 guide chapters, 56 case records, 166 catalog entries, 26 numeric profiles
and 24 candidate families. One local notation clarification was incorporated:
the shell-normalization explanation now defines its resolvent and inverse-domain
assumptions before the derivative. No unresolved findings remained in these
focused document reviews; they are not external peer review or formal proof
certification.

The initial integrated current-documentation check inspected 3,644 inline links,
2,045 local Markdown anchors and 167 distinct pinned GitHub objects, with no
missing targets or preservation discrepancies. These counts describe the
current-documentation phase and will grow when the application map is added.

The local application documentation check was also run in an isolated copied
application: five tests passed and one repository-only inventory test was
appropriately skipped. With the actual bridge module inventory available, all
six documentation-registry tests passed. The dependent application phase must
repeat its checks after binding actual publication/documentation commit URLs
and refreshing the manifest.

Final candidate identities, current-head preservation/source checks and GitHub
CI results belong to the actual PR check records and detached execution
receipts. This tracked file does not assert its own containing commit or a
future CI result. No fresh full Lean build, universal manuscript/declaration
equivalence audit, independent case acceptance or empirical identification is
claimed by these documentation checks.

## Preservation and review boundaries

Original `paper/`, `provenance/`, `application/`, accepted release records, the
root citation, protected core source and inherited PR79 documents remain
unchanged. Current explanations are additive under `paper2/` and `docs/paper2/`.
The guide PDF/Markdown, chapter/case maps and module manifest retain their
edition identities. No checker allowlist, workflow, schema, dependency,
toolchain or mathematical source is changed to accommodate the new paper.

See [version lineage](VERSION_LINEAGE.md), [compatibility and corrections](COMPATIBILITY_AND_CORRECTIONS.md)
and [current residual status](RESIDUAL_STATUS.md) for the boundaries readers need
when interpreting the publication.


## Scope and workorder completion audit

The initial completeness audit compared all 25 workorders against the actual
files and open PRs. It accounted for all 41 originally planned paths. The later
remaining-fix scope extends that set to the 55 paths listed below. This section
records their implementation destinations and the remaining post-merge condition;
it does not replace CI or claim that an open PR is merged.

### Observed candidate identities

| Candidate inspected | Commit | Evidence location |
| --- | --- | --- |
| Publication package | `8630e80b604223aa0fadff92d6a7c2749cd8be5b` | [PR #128](https://github.com/HMarcusWH/PermanssonLean/pull/128) |
| Initial complete central documentation | `2f20d86e42a8b0ed15f59d5a480a2b61efc80f7a` | [PR #129](https://github.com/HMarcusWH/PermanssonLean/pull/129) |
| Initial complete application/metadata candidate | `f4c4f8de4ed91e91c94d90a1ea45b31378c684a2` | [PR #130](https://github.com/HMarcusWH/PermanssonLean/pull/130) |

These are observed predecessors of the follow-up documentation corrections.
Each PR's current body records its later checked head and tree; the application
PR includes the complete detached inventory receipt for its current candidate.
Neither this table nor that receipt claims independent review authority.

At the initial complete application candidate, all 41 paths matched the planned
scope, all nine changed/new inventoried documentation hashes matched, all six
documentation-registry and thirteen inventory tests passed, and the inventory
check passed. The repository gate passed 67/67 and canonical preservation
returned PASS. The A2 result retained
`SOURCE_IDENTITY_CANDIDATE_NEEDS_INDEPENDENT_SECURITY_REVIEW`.

The initial final-stack link count was **3,781 link occurrences**, including
**177 pinned GitHub link occurrences to 172 distinct commit/path objects**.
The initial central-documentation count of 167 pinned occurrences happened to
contain 167 distinct objects. Later receipts distinguish these two counts
explicitly.

### Follow-up findings and repairs

The full file and content audit found no missing publication asset, source-bundle
dependency, mathematical crosswalk row, earlier-paper requirement, guide record,
profile or candidate family. It identified the following documentation repairs:

- The central compatibility page now states the shared `FiniteWorldInput`
  reflection limits for adaptive grammar, CQ-1 transport and risk-infeasibility:
  1–2 strategic states, 1–2 world states and 1–2 actions, hence at most four joint
  states. All numeric registry scope strings remain exact.
- The verification guide now gives the packaged 326-check foundation replay
  command. It distinguishes the 43 quantitative and 20 specialized retained
  result records, whose original standalone replay programs are not included
  in the reviewed ZIP.
- The current review now includes the explicit path scope, workorder
  reconciliation and reproducible preservation comparison below.

The exact packaged `review/foundations_exact_checks.py` was replayed in a
fresh external extraction during the follow-up audit: exit status 0, **326/326
checks passed**. This verifies that packaged calculation program at the reviewed
ZIP identity; it is separate from Lean compilation and from the original
63 retained quantitative/specialized review results.

### Later reproduction and usability fixes

The [new reproduction addendum](../../paper2/reproduction/v2.0.1/README.md)
recomputes all **63 retained outputs** with exact rational arithmetic and
reports **12 additional arithmetic controls** and **five comparison controls**.
All passed in the observed run. Seven file/path-handling probes checked the
normal command, an unrelated working directory, copied programs with an explicit
archive, two altered-archive failures, refusal to overwrite a file and creation
of a new result file. All eighteen unique literal manuscript references in the
two modules resolve to labels in the reviewed archive. The
[manifest](../../paper2/reproduction/v2.0.1/REPLAY_MANIFEST.json) and
[result record](../../paper2/reproduction/v2.0.1/REPLAY_RESULTS.json) retain the
new code identities and fixture boundaries. The original archive/result bytes
are unchanged; this does not recover the original review execution.

Four application test modules previously evaluated `APP.parents[2]` at import,
which failed in a shallow standalone extraction even with a source-root
override. Their new depth-checked default preserves ordinary repository and
explicit-override behavior. The permanent `test_root_portability.py` runs four
layout/override cases against the actual affected modules. Before the fix,
three shallow cases failed and the ordinary-layout case passed; after the fix,
all four passed, exercising sixteen selected existing tests in subprocesses.
These are application-test portability changes, with no numerical runtime or
Lean theorem change.

The application acceptance table and the adaptive, CQ-1 transport and
risk-infeasibility bridge pages now agree on the reflected `FiniteWorldInput`
domain: 1–2 strategic states, 1–2 world states and 1–2 actions, hence at most
four joint states. Numeric profile bounds and evidence statuses retain their
own meanings. Both native CLI README examples now specify the repository
working directory. The application phase refreshes current candidate hashes
and inventory membership without changing recovery identities or proof/trust
states.

The three additional bridge documents were among the original preserved text
candidates. Their explicit correction changes the current preserved-text count
from the historical **341** to **338 of 353** baseline text documents. All
other baseline objects outside the expanded allowlist remain unchanged.

### Workorder dispositions

| Workorder | Implementation or remaining condition |
| --- | --- |
| PUB-01 | [Publication hub](../../paper2/README.md) and [edition package](../../paper2/v2.0.1/README.md): all three reviewed assets. |
| PUB-02 | [Manifest](../../paper2/v2.0.1/PUBLICATION_MANIFEST.json), [checksums](../../paper2/v2.0.1/SHA256SUMS) and [citation](../../paper2/v2.0.1/CITATION.bib), with the actual first asset commit. |
| PUB-03 | [Seven public indexes](../../paper2/v2.0.1/indices/), copied exactly from the reviewed ZIP. |
| NAV-01 | [Repository landing page](../../README.md): current paper and qualified original-edition routes. |
| NAV-02 | [Central index](../README.md), [current index](README.md) and both publication hubs. |
| NAV-03 | [Research build guide](../RESEARCH_BUILD.md): pinned inventory and historical build scope. |
| NAV-04 | [Preserved-guide landing page](../reference/README.md): distinct guide and paper editions. |
| NAV-05 | [Current index](README.md) and [getting started](GETTING_STARTED.md): reading, reproduction, source and contributor routes. |
| MAP-01 | [Mathematical crosswalk](MATHEMATICAL_CROSSWALK.md): 47 structural routes, 147 numbered items, 538 citations, all 798 Lean files and 41 historical math-guide routes. |
| MAP-02 | [Earlier-paper concordance](EARLIER_PAPER_CONCORDANCE.md): 51 obligations and 201 requirements, retaining all 235 label / 37 source-file joins. |
| MAP-03 | [Guide-to-paper map](GUIDE_TO_PAPER.md): all 46 chapters, 56 cases and 166 catalog records. |
| STATUS-01 | [Residual ledger](RESIDUAL_STATUS.md): seven named obligations and separately scoped broader limits. |
| VERSION-01 | [Version lineage](VERSION_LINEAGE.md): publication, software, guide and historical candidate identities. |
| SEMANTICS-01 | [Corrections](COMPATIBILITY_AND_CORRECTIONS.md): all 58 reviewed findings and their qualified mathematical distinctions. |
| SEMANTICS-02 | [Current glossary](GLOSSARY.md): edition-qualified definitions and evidence vocabulary. |
| VERIFY-01 | [Verification instructions](VERIFICATION.md), including the packaged foundation replay command and the precise limits of retained supplementary records. |
| VERIFY-02 | This review, including the exact allowlist, reproducible comparison and candidate/CI distinctions below. |
| APP-01 | [Application compatibility](APPLICATION_COMPATIBILITY.md): all 26 numeric profiles and 24 candidate families, with numeric and reflected domains separately stated. |
| APP-02 | [PR #130](https://github.com/HMarcusWH/PermanssonLean/pull/130): local `PAPER2_MAPPING.md` and both application entry points. |
| APP-03 | [PR #130](https://github.com/HMarcusWH/PermanssonLean/pull/130): capability, evidence, reviewer and acceptance orientation additions. |
| APP-04 | [PR #130](https://github.com/HMarcusWH/PermanssonLean/pull/130): both native CLI reading routes with immutable external links. |
| APP-05 | [PR #130](https://github.com/HMarcusWH/PermanssonLean/pull/130): nine explicit documentation-hash comparisons, one new mapping row, current counts and detached receipt. |
| CHECK-01 | Phase A/B/C local checks retain their separate source identities. PRs #128–130 are merged; their main-target workflow observations and the actual merged head are recorded [below](#merged-head-verification-and-21-november-follow-up). Retargeting is complete. |
| CHECK-02 | Complete for the original publication stack at merged head `09c4341c22dfb22c750bfb02d4eaa4486782b77d`: reader-route, preservation, source-identity and inventory checks passed, and all six observed main workflows succeeded in the dated observation [below](#merged-head-verification-and-21-november-follow-up). The later documentation follow-up has its own candidate checks. |
| RELEASE-01 | Optional paper-specific tag/release was not performed; its prerequisite is the completed post-merge CHECK-02 gate. |
| FOLLOWUP-REPRO | [PR #128](https://github.com/HMarcusWH/PermanssonLean/pull/128): six separately identified reproduction files, exact archive/member checks and a retained new execution record. |
| FOLLOWUP-USABILITY | [PR #130](https://github.com/HMarcusWH/PermanssonLean/pull/130): four test-root fixes, a four-case permanent regression, four reflection-scope corrections, two native command clarifications and refreshed candidate metadata. |

### Exact cumulative changed-path allowlist

This completed **55-path historical snapshot** ends at merged head
`09c4341c22dfb22c750bfb02d4eaa4486782b77d` and is relative to pre-upload baseline
`f0dee1c11a20f96c9a11b380e942b9252e6ebe44`.
`A` means a new path and `M` an existing path updated by the complete stack:
35 additions and 20 updates, comprising fifteen existing Markdown files,
four existing test modules and one JSON inventory. The two publication hubs occur in both publication and navigation
PRs but count only once in this cumulative list.

<!-- PAPER2_SCOPE_BEGIN -->
```text
M	README.md
M	apps/permansson/application-successor/IMPLEMENTATION_MANIFEST.json
M	apps/permansson/application-successor/README.md
M	apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md
M	apps/permansson/application-successor/docs/ADAPTIVE_LEAN_BRIDGE.md
M	apps/permansson/application-successor/docs/CAPABILITY_SCOPES.md
M	apps/permansson/application-successor/docs/CQ1_TRANSPORT_LEAN_BRIDGE.md
M	apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md
A	apps/permansson/application-successor/docs/PAPER2_MAPPING.md
M	apps/permansson/application-successor/docs/README.md
M	apps/permansson/application-successor/docs/REVIEWER_GUIDE.md
M	apps/permansson/application-successor/docs/RISK_INFEASIBILITY_LEAN_BRIDGE.md
M	apps/permansson/application-successor/tests/test_docs_registry.py
M	apps/permansson/application-successor/tests/test_extended_cli.py
M	apps/permansson/application-successor/tests/test_integration.py
M	apps/permansson/application-successor/tests/test_numeric.py
A	apps/permansson/application-successor/tests/test_root_portability.py
M	apps/permansson/closure-successor-c11/README.md
M	apps/permansson/closure-successor/README.md
M	docs/README.md
M	docs/RESEARCH_BUILD.md
A	docs/paper2/APPLICATION_COMPATIBILITY.md
A	docs/paper2/COMPATIBILITY_AND_CORRECTIONS.md
A	docs/paper2/DOCUMENTATION_REVIEW.md
A	docs/paper2/EARLIER_PAPER_CONCORDANCE.md
A	docs/paper2/GETTING_STARTED.md
A	docs/paper2/GLOSSARY.md
A	docs/paper2/GUIDE_TO_PAPER.md
A	docs/paper2/MATHEMATICAL_CROSSWALK.md
A	docs/paper2/README.md
A	docs/paper2/RESIDUAL_STATUS.md
A	docs/paper2/VERIFICATION.md
A	docs/paper2/VERSION_LINEAGE.md
M	docs/reference/README.md
A	paper2/README.md
A	paper2/reproduction/v2.0.1/README.md
A	paper2/reproduction/v2.0.1/REPLAY_MANIFEST.json
A	paper2/reproduction/v2.0.1/REPLAY_RESULTS.json
A	paper2/reproduction/v2.0.1/quantitative_replay.py
A	paper2/reproduction/v2.0.1/replay.py
A	paper2/reproduction/v2.0.1/specialized_replay.py
A	paper2/v2.0.1/CITATION.bib
A	paper2/v2.0.1/PUBLICATION_MANIFEST.json
A	paper2/v2.0.1/Permansson_Regimes_v2_0_1_Review_Report_2026-11-20.pdf
A	paper2/v2.0.1/Permansson_Regimes_v2_0_1_Reviewed_Manuscript_2026-11-20.pdf
A	paper2/v2.0.1/Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip
A	paper2/v2.0.1/README.md
A	paper2/v2.0.1/SHA256SUMS
A	paper2/v2.0.1/indices/all_lean_written_connections.json
A	paper2/v2.0.1/indices/earlier_paper_written_obligations.json
A	paper2/v2.0.1/indices/manuscript_label_index.json
A	paper2/v2.0.1/indices/review_findings.json
A	paper2/v2.0.1/indices/revision_verification.json
A	paper2/v2.0.1/indices/source_citation_index.json
A	paper2/v2.0.1/indices/statement_index.json
```
<!-- PAPER2_SCOPE_END -->

### Reproduce the cumulative scope and preserved-byte comparison

Run the following from a **clean full Git checkout containing the completed
merged snapshot** `09c4341c22dfb22c750bfb02d4eaa4486782b77d`. The comparison pins
that historical snapshot even when run from a later checkout. The original
central-documentation PR alone lacked the dependent application additions. This comparison
uses only Git, Python's standard library and the allowlist in this tracked page;
it does not require the original planning workspace.

It compares full tree entries, including object type and file mode. It also
reconstructs all 353 baseline Markdown/text/CFF candidates and explicitly
checks the 338 currently designated unchanged text documents. The complete changed-path
comparison preserves all other baseline objects outside the listed updates,
including the guide edition artifacts.

```bash
python3 - <<'PY_CHECK'
from pathlib import Path, PurePosixPath
import json
import subprocess

baseline = "f0dee1c11a20f96c9a11b380e942b9252e6ebe44"
def git(*args):
    return subprocess.check_output(["git", *args])

if git("status", "--porcelain", "--untracked-files=no").strip():
    raise SystemExit("Use a clean committed checkout.")
candidate = "09c4341c22dfb22c750bfb02d4eaa4486782b77d"
review = git("show", candidate + ":docs/paper2/DOCUMENTATION_REVIEW.md").decode()
start = "<!-- PAPER2_" + "SCOPE_BEGIN -->"
end = "<!-- PAPER2_" + "SCOPE_END -->"
scope = review.split(start, 1)[1].split(end, 1)[0]
allowed = {}
for line in scope.splitlines():
    if line.startswith(("A\t", "M\t")):
        status, path = line.split("\t", 1)
        allowed[path] = status

def tree(ref):
    result = {}
    for entry in git("ls-tree", "-rz", ref).split(b"\0"):
        if entry:
            metadata, path = entry.split(b"\t", 1)
            result[path.decode()] = tuple(metadata.decode().split())
    return result

before, after = tree(baseline), tree(candidate)
actual = {}
for path in before.keys() | after.keys():
    if before.get(path) != after.get(path):
        actual[path] = "A" if path not in before else (
            "D" if path not in after else "M")
assert actual == allowed, "Changed paths differ from the declared scope."
assert len(allowed) == 55
assert sum(s == "A" for s in allowed.values()) == 35
for path, status in allowed.items():
    if status == "M":
        assert before[path][:2] == after[path][:2], path
    else:
        assert after[path][:2] == ("100644", "blob"), path
text_paths = {
    p for p in before if PurePosixPath(p).suffix in {".md", ".txt", ".cff"}
}
preserved = text_paths - allowed.keys()
assert len(text_paths) == 353 and len(preserved) == 338
assert all(before[p] == after.get(p) for p in preserved)
print(json.dumps({
    "status": "PASS",
    "baseline": baseline,
    "candidate": candidate,
    "changed_paths": len(actual),
    "preserved_text_documents": len(preserved),
    "mode_and_object_identity_compared": True
}, indent=2))
PY_CHECK
```

Then use the existing canonical preservation and A2 commands in
[the verification guide](VERIFICATION.md#6-preserve-repository-and-source-identity),
and the explicit app-hash/inventory checks recorded in
[PR #130](https://github.com/HMarcusWH/PermanssonLean/pull/130).
A successful path comparison establishes the declared change boundary; the
individual mathematical and application claims retain their own evidence scope.

### Historical merge-stage condition

The pre-merge record required the actual final merged head, its CI, reader
routes and detached identity receipt. At that time PRs #129 and #130 targeted
their preceding branches and needed retargeting after their parents merged.
The completed retargeting and merged-head observations are recorded below.
The optional paper release remains separate and has not been performed.

## Merged-head verification and 21 November follow-up

### Observed merged publication and documentation state

All times in this subsection are **Europe/Stockholm (CET)**. The three PRs were
merged on **21 November 2026**:

| PR | Final candidate head | Merge commit | Merge time |
| --- | --- | --- | --- |
| [#128](https://github.com/HMarcusWH/PermanssonLean/pull/128) | `39f97d409e2731d286bbf5b835a8ae6acc038667` | `49acf3f25ab799e517f62516a97e8c38fa4d3795` | 00:08:00 |
| [#129](https://github.com/HMarcusWH/PermanssonLean/pull/129) | `8e07982a34e76f02591f97afbc70d2e8967e22e5` | `7a7ae30b6eaf4c25ef3d8867f23763390c969457` | 00:08:57 |
| [#130](https://github.com/HMarcusWH/PermanssonLean/pull/130) | `df30635f58a437d9440436c52aaa869bfe2d7b5f` | `09c4341c22dfb22c750bfb02d4eaa4486782b77d` | 00:09:20 |

The inspected merged head is
[`09c4341c22dfb22c750bfb02d4eaa4486782b77d`](https://github.com/HMarcusWH/PermanssonLean/commit/09c4341c22dfb22c750bfb02d4eaa4486782b77d),
with tree `97b912dc780f3644e3984003be6de217bd1827eb`. Its tree equals the final
candidate tree inspected for PR #130. Fresh checks in a clean detached checkout
of the **merged commit itself** observed:

- The declared 55-path comparison and original publication asset/index identities
  passed; 338 of the 353 baseline text documents were designated unchanged and
  remained byte-identical.
- The existing repository gate passed **67/67**. Canonical preservation returned
  **PASS** for its 369 protected objects.
- The A2 source-identity result remained
  `SOURCE_IDENTITY_CANDIDATE_NEEDS_INDEPENDENT_SECURITY_REVIEW` with
  `independent_security_review=false` and `mathematical_acceptance=false`.
- The application inventory passed. Its detached receipt binds the merged head,
  application tree `3402b625b3b3e77a2e5f8ef92cfa52b9d6eee2e1`, and manifest SHA-256
  `5248ef7e4ea2dde3ca8427948fb34557fc998dba7434b80baf7be56f60f44aeb`.
- The complete document-link scan found **5,437** occurrences, including **5,250**
  resolved local or repository links, with no missing target, suspect Markdown
  anchor or malformed inline-link candidate. A separate recursive check resolved
  **7,597** repository links in **517** pinned Markdown contexts, with no target
  or anchor discrepancy. External availability and mathematical validity have
  separate evidence requirements.

At the earlier **00:54:12 CET** observation, Research Lean was still in progress.
The later main-branch observation at **01:04:53 CET on 21 November 2026** confirms
that all six workflows at the same merged head completed successfully:

| Workflow at merged head `09c4341c` | Observed result |
| --- | --- |
| [Executable verification](https://github.com/HMarcusWH/PermanssonLean/actions/runs/44834661818) | Completed: success |
| [Application contract](https://github.com/HMarcusWH/PermanssonLean/actions/runs/44834661978) | Completed: success |
| [Research integrity](https://github.com/HMarcusWH/PermanssonLean/actions/runs/44834661690) | Completed: success |
| [Lean](https://github.com/HMarcusWH/PermanssonLean/actions/runs/44834661687) | Completed: success |
| [Integrity portability](https://github.com/HMarcusWH/PermanssonLean/actions/runs/44834661742) | Completed: success |
| [Research Lean](https://github.com/HMarcusWH/PermanssonLean/actions/runs/44834661756) | Completed: success |

**CHECK-01:** the retargeting and merge steps are complete. **CHECK-02:** the
original publication stack's merged-head local checks and all six observed main
workflows are complete at this observation. This closes that post-merge
documentation gate; it does not supply CI for the later documentation candidate.
An installed workflow, a successful run and a live required-check rule are
different evidence; see the
[current operations index](../operations/README.md). No release or independent
acceptance follows from these documentation checks.

### Documentation audit corrections

The later audit identified sixteen documentation corrections. This follow-up
implements them and the separately scoped E-05 evidence-navigation improvement.
The identifiers below are the **21 November documentation audit** identifiers;
they are distinct from the earlier manuscript and publication workorders.

| Audit item | Correction and reading route |
| --- | --- |
| DOC-01 | This merged-head record, dated CI observations and a separate follow-up scope replace stale retargeting instructions. |
| DOC-02 | The [operations index](../operations/README.md) distinguishes active owner-engineering policy v2, historical 25-workflow handoffs and inactive 30-workflow proposals. |
| DOC-03 | [Receipt documentation](../../apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md) describes profile-specific raw records, checker output, scientific reports and native results separately; the capability, release, acceptance, reviewer and belief guides use the same distinctions. |
| DOC-04 | The [application README](../../apps/permansson/application-successor/README.md) labels the native wrapper as numeric execution and links genuine compiler replay separately. |
| DOC-05 | The [architecture guide](../../apps/permansson/application-successor/docs/ARCHITECTURE.md) routes archive operations to successor policy v2 and retains the independent-review boundary. |
| DOC-06 | [Grammar/quotient scope](../../apps/permansson/application-successor/docs/NUMERIC_GRAMMAR_QUOTIENT.md) and receipt terminology distinguish the published numeric release from what an individual result assesses. |
| DOC-07 | The application README and [roadmap](../../apps/permansson/application-successor/docs/ROADMAP.md) state command working directories and repository-relative paths. |
| DOC-08 | [Native proof guidance](../../apps/permansson/application-successor/docs/NATIVE_PROOF_REPLAY.md) states actual workflow triggers, concrete-fixture evidence and reflection exclusions. |
| DOC-09 | The [historical errata](HISTORICAL_DOCUMENTATION_ERRATA.md) explain the unresolved-identification fixture's inconsistent narrative while preserving its structural-validation result and original bytes. |
| DOC-10 | The [C10 README](../../apps/permansson/closure-successor/README.md) corrects “arbitary” to “arbitrary”. |
| DOC-11 | Native proof guidance distinguishes deterministic identical regeneration from changed or mismatched bytes. |
| DOC-12 | The [bridge candidate history](../../apps/permansson/application-successor/docs/LEAN_APPLICATION_BRIDGE_CANDIDATE.md) dates the original 25-workflow statement. |
| DOC-13 | The [verification guide](VERIFICATION.md) gives the D0-only Python command and separate full-research-suite prerequisites. |
| DOC-14 | The verification guide distinguishes read-only checks from artifact producers and supplies detached output routes. |
| DOC-15 | The verification guide renders the historical draft commands correctly; the historical errata record its formatting and abstract grammar defects without rewriting the original thirteen-source draft. |
| DOC-16 | The historical errata supply the corrected Q05 baseline/intervention sentence. |
| PUB-03, optional audit improvement | The [E-05 residual entry](RESIDUAL_STATUS.md#e-05) links the newer finite controls while retaining `PARTIAL_SCOPE` and the original source-specific obligations. |

### Exact follow-up scope against the audited merged head

This change set has **26 paths: two additions and twenty-four updates**, relative to
`09c4341c22dfb22c750bfb02d4eaa4486782b77d`. It includes the five current-documentation
link-pin updates and fourteen existing inventory-row hash refreshes. The
cross-review extended DOC-03 to five companion guides that repeated the same
universal receipt-field claim. Publication,
theorem-source and historical-evidence pins retain their distinct identities.
The original 55-path record above remains tied to its completed snapshot.

<!-- DOCUMENTATION_AUDIT_SCOPE_BEGIN -->
```text
M	apps/permansson/application-successor/IMPLEMENTATION_MANIFEST.json
M	apps/permansson/application-successor/README.md
M	apps/permansson/application-successor/docs/ACCEPTANCE_STATUS.md
M	apps/permansson/application-successor/docs/ARCHITECTURE.md
M	apps/permansson/application-successor/docs/CAPABILITY_SCOPES.md
M	apps/permansson/application-successor/docs/EVIDENCE_AND_RECEIPTS.md
M	apps/permansson/application-successor/docs/LEAN_APPLICATION_BRIDGE_CANDIDATE.md
M	apps/permansson/application-successor/docs/NATIVE_PROOF_REPLAY.md
M	apps/permansson/application-successor/docs/NUMERIC_BELIEF_CONTROL.md
M	apps/permansson/application-successor/docs/NUMERIC_GRAMMAR_QUOTIENT.md
M	apps/permansson/application-successor/docs/PAPER2_MAPPING.md
M	apps/permansson/application-successor/docs/RELEASE_ACCEPTANCE.md
M	apps/permansson/application-successor/docs/REVIEWER_GUIDE.md
M	apps/permansson/application-successor/docs/ROADMAP.md
M	apps/permansson/closure-successor-c11/README.md
M	apps/permansson/closure-successor/README.md
M	docs/README.md
A	docs/operations/README.md
M	docs/paper2/APPLICATION_COMPATIBILITY.md
M	docs/paper2/COMPATIBILITY_AND_CORRECTIONS.md
M	docs/paper2/DOCUMENTATION_REVIEW.md
A	docs/paper2/HISTORICAL_DOCUMENTATION_ERRATA.md
M	docs/paper2/README.md
M	docs/paper2/RESIDUAL_STATUS.md
M	docs/paper2/VERIFICATION.md
M	docs/paper2/VERSION_LINEAGE.md
```
<!-- DOCUMENTATION_AUDIT_SCOPE_END -->

From a clean committed checkout of the follow-up candidate, reproduce its scope
and the unchanged identity of every other tracked path with:

```bash
python3 - <<'PY_FOLLOWUP'
import json
import subprocess

def git(*args):
    return subprocess.check_output(["git", *args])

if git("status", "--porcelain", "--untracked-files=no").strip():
    raise SystemExit("Use a clean committed follow-up checkout.")
baseline = "09c4341c22dfb22c750bfb02d4eaa4486782b77d"
candidate = git("rev-parse", "HEAD").decode().strip()
review = git("show", candidate + ":docs/paper2/DOCUMENTATION_REVIEW.md").decode()
start = "<!-- DOCUMENTATION_AUDIT_" + "SCOPE_BEGIN -->"
end = "<!-- DOCUMENTATION_AUDIT_" + "SCOPE_END -->"
scope = review.split(start, 1)[1].split(end, 1)[0]
allowed = dict(line.split("\t", 1)[::-1] for line in scope.splitlines()
               if line.startswith(("A\t", "M\t")))

def tree(ref):
    result = {}
    for entry in git("ls-tree", "-rz", ref).split(b"\0"):
        if entry:
            metadata, path = entry.split(b"\t", 1)
            result[path.decode()] = tuple(metadata.decode().split())
    return result

before, after = tree(baseline), tree(candidate)
actual = {path: "A" if path not in before else "D" if path not in after else "M"
          for path in before.keys() | after.keys() if before.get(path) != after.get(path)}
assert actual == allowed, "Changed paths differ from the follow-up scope."
assert len(allowed) == 26 and list(allowed.values()).count("A") == 2
for path, status in allowed.items():
    assert after[path][:2] == (before[path][:2] if status == "M" else ("100644", "blob")), path
print(json.dumps({"status": "PASS", "baseline": baseline, "candidate": candidate,
                  "changed_paths": len(actual), "all_other_tree_entries_unchanged": True}, indent=2))
PY_FOLLOWUP
```

The [follow-up PR #131](https://github.com/HMarcusWH/PermanssonLean/pull/131)
records its actual committed head, detached preservation/A2 and
inventory receipts, link and command checks, and that head's own workflow runs.
This file does not self-report its containing commit or substitute the merged
baseline's successful checks for the follow-up candidate's checks. Existing
source-identity guards and acceptance rules remain unchanged.
