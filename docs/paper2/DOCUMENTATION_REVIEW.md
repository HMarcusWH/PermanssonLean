# Paper v2.0.1 documentation review

[Current documentation](README.md) · [Manuscript review](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Review_Report_2026-11-20.pdf) · [Verification guide](VERIFICATION.md)

**Review date:** 20 November 2026. This record concerns publication metadata and
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
| CHECK-01 | Phase A/B/C local checks have separate observed source identities. Existing CI is reported in the corresponding PR; main-target CI for dependent PRs awaits retargeting. |
| CHECK-02 | Final merged-head review remains pending. Candidate checks and the complete application hash reconciliation are recorded in [PR #130](https://github.com/HMarcusWH/PermanssonLean/pull/130). |
| RELEASE-01 | Optional paper-specific tag/release was not performed; its prerequisite is the completed post-merge CHECK-02 gate. |
| FOLLOWUP-REPRO | [PR #128](https://github.com/HMarcusWH/PermanssonLean/pull/128): six separately identified reproduction files, exact archive/member checks and a retained new execution record. |
| FOLLOWUP-USABILITY | [PR #130](https://github.com/HMarcusWH/PermanssonLean/pull/130): four test-root fixes, a four-case permanent regression, four reflection-scope corrections, two native command clarifications and refreshed candidate metadata. |

### Exact cumulative changed-path allowlist

This list is relative to pre-upload baseline
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

Run the following from a **clean full Git checkout of the complete candidate**
(the application PR or eventual merged head). The central-documentation PR
alone intentionally lacks the dependent application additions. This comparison
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
    raise SystemExit("Use a clean committed candidate checkout.")
candidate = git("rev-parse", "HEAD").decode().strip()
review = Path("docs/paper2/DOCUMENTATION_REVIEW.md").read_text()
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

### Remaining merge-stage gate

The implementation and local candidate evidence are present in the PR stack.
CHECK-02 still requires the **actual final merged head**, its required CI,
reader routes and detached identity receipt. PR #129 and PR #130 target their
preceding branches; retargeting to `main` after their parents merge allows
the existing main-target workflows to run. The optional paper release remains
separate and is not represented as completed.
