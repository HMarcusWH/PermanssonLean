# Lean evidence and paper crosswalk

[Verification guide](../README.md) · [Full formalization map](../../docs/FORMALIZATION_MAP.md) · [Lean setup](../../docs/GETTING_STARTED.md#build-the-lean-proofs)

These files document the paper's immutable formalization snapshot. They do not
replace the Lean source tree or report the latest branch's CI status.

| File | How to read it |
|---|---|
| [LEAN_PROVENANCE.md](LEAN_PROVENANCE.md) | Snapshot `c018f79ea4ce46f4f679ad5bca254509778fc53c`, toolchain, and recorded CI identifiers |
| [LEAN_CI_EVIDENCE.json](LEAN_CI_EVIDENCE.json) | Machine-readable CI evidence for that snapshot |
| [THEOREM_CROSSWALK.md](THEOREM_CROSSWALK.md) | Seventeen selected release-audit entries with source locations; not the full theorem ledger |
| [LEAN_DECLARATION_CROSSWALK.json](LEAN_DECLARATION_CROSSWALK.json) | Machine-readable selected crosswalk |
| [Root import snapshot](PermanssonLean_root_imports_snapshot.lean) | The release import list; compare with the [live root module](../../PermanssonLean.lean) |

Start at the [complete theorem/definition ledger](../../docs/FORMALIZATION_MAP.md#source-to-lean-theorem-and-definition-ledger)
for coverage through Proposition 8.1. Source locations in the selected crosswalk
belong to the cited commit; they are not promised stable line numbers after future
formal development. The formalization map's milestone narrative retains build history.

For a fresh verification, run the pinned [build workflow](../../docs/GETTING_STARTED.md#build-the-lean-proofs)
and inspect CI for the exact commit under review. Do not substitute historical
snapshot success for a new head's result. A green build does not establish empirical
identification, source authenticity, or the non-core research claims.
