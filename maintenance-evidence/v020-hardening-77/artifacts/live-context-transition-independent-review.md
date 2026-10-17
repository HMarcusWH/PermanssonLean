# Independent review of the captured PR77 head transition

Reviewed on 2026-10-17 by the archive review agent. This review made no repository edits or GitHub mutations. It independently read the helper and saved report, opened their exact input artifact ZIPs, exercised the production context validator on those saved contexts, and read canonical local Git commit objects. No CI suite was rerun.

Disposition: the actual report establishes source binding and rejection of superseded evidence. Its explicit separation of source binding from job success and before-green chronology is accurate.

## Exact source bindings and controls

Both contexts identify PR77 in `HMarcusWH/PermanssonLean`, the accepted release/base `d8a4ffb5b63eb9359a4c0af9134b4f9a3c529618`, and a real `pull_request` event:

| Captured pair | Head H | Synthetic S | Checked tree |
|---|---|---|---|
| Previous | `e314ccc2b3587065425a0357874ad5580cce841d` | `b96e30d8b38575796a8c598c028488e449b85a8d` | `c430331aa4cf9a0847c85f6b1ca76777c6ae7a54` |
| Current at this exercise | `cc114ee60ff8749b3bb64bb24a8d5e76d2120af9` | `86ff0d8ce3482935d2ff09ee24c260d309f069d1` | `bc2af29f32f6b89b5ea927ea04a6579422e4e6eb` |

Independent controls passed for each actual H/B/S tuple. Each canonical S has the exact ordered parents `(B, H)` and the captured tree. Applying the previous captured context to the current H/B/S rejected with exactly `E_CONTEXT`.

The previous context comes from `hardening-pr77/12110875886.zip` (run 39058545127, attempt 1); the new context comes from `hardening-pr77-prebase-acceptance/hardening-windows-portability-reports.zip` (run 39061789338, attempt 1). Both selected `context.json` values exactly equal their report entries. These are context identity controls; using a portability artifact as the second context does not establish that the separate archival job passed.

## Chronology and its limits

The saved `hardening-pr77/check-runs-h2-final.json` contains exactly nine completed, successful checks, all for H=`e314ccc...`. Their latest completion is the research check at **2026-10-17 18:46:03 UTC**. Canonical Git author and committer timestamps for H=`cc114ee...` are **19:16:58 UTC**, 30 minutes 55 seconds later. The captured GitHub run collection independently records all six workflows for that new head as created at **19:17:07 UTC**; the collection was fetched at 19:26:11.443 UTC. The PR capture fetched at 19:26:08.921 UTC identifies that new H/B/S.

These records support the stated order: the previous head was already all-green before the new-head run creation. They do **not** demonstrate an update before the previous head became green, nor a wall-clock push time derived solely from Git's author-controlled dates. The new-head initial check capture at 19:26:10.463 UTC still contains unfinished checks; that observation is distinct from when the source-binding report was generated. The helper correctly leaves job-success and before-green chronology to separate evidence.

The helper's `base-change` mode additionally requires a changed head, so it does not model a head-constant/base-only movement. This does not affect the reviewed head-change exercise. A later final H/B/S needs its own exact-source evidence. No publisher authentication, counted GitHub approval, completed OPS case, fresh Lean run, or final merged-main acceptance follows from this review.

## File identities (SHA-256)

| File under `artifacts/` | SHA-256 |
|---|---|
| `check_live_context_transition.py` | `cb2813b61ed10e884044d1355f0d1a0cf6ab516dfc2887ce3eb23475fed06b5a` |
| `hardening-pr77-prebase-acceptance/live-head-transition.json` | `a0e9afe6f9d3e9dc07f61f0e560283de2fef4137f3b71e18b3bd8a5bb24bc302` |
| `hardening-pr77/12110875886.zip` | `8165e7d6a878b251a3fdc43de5f5501ce98ad0e016225fe56b6255df630780d3` |
| `hardening-pr77-prebase-acceptance/hardening-windows-portability-reports.zip` | `be590e1c5323750e3aa32db9a98d1e4bde090655d10e1bd23ad1cc9187a2f148` |
| `hardening-pr77/check-runs-h2-final.json` | `b1893d553aaddc0bb01aed031b0148caaaf62fbf6980f0f06bbbc9f95e1888ad` |
| `hardening-pr77-prebase-acceptance/initial-runs.json` | `22d824ee2cc4c7be0e7f0071eba4588268e32f09782106bdb49a89ce6a7f47d9` |
| `hardening-pr77-prebase-acceptance/initial-pr77.json` | `48bc9e02066992db16f321a8be92cba16d93585f052679736a2e9b6b28203e25` |

This receipt helper and its captured JSON inputs remain review-sensitive. Checksums and canonical Git binding do not independently authenticate the publisher of those input captures. Only the explicitly named hardening files were inspected; unrelated material under `artifacts/` was not inventoried.
