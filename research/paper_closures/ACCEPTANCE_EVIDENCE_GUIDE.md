# Reading and reproducing the acceptance ledger

[acceptance_evidence.md](acceptance_evidence.md) reports each of the 45 exact supplied case IDs. [acceptance_evidence.json](acceptance_evidence.json) gives declaration names, source hashes, receipt paths and hashes, individual execution results, and material gaps.

`LOCAL_EVIDENCE_COMPLETE` means the selected case has its listed local evidence. It does not close all 42 atlas targets, approve statement scope, establish current PR-head or synthetic-merge CI, or authorize merging. `PARTIAL` identifies missing execution or source binding. The supplied registry's original status is retained for provenance, separately from the current case status.

After the pinned Lean research build, reproduce the executions and regenerate with:

```text
python verification/research/paper_closure_acceptance_evidence.py --refresh
```

Without execution flags, the generator validates and reuses current source-bound receipts. `--run-exact` executes the selected independent Python checks. `--check-lean` executes the four-factor interface controls and selected declaration signature/axiom audit. `--output-dir .lake/acceptance-evidence-report` keeps generated reports outside the published directory. Generating a valid partial ledger returns success; the individual case statuses remain authoritative.

The evidence categories have different meanings:

- **Kernel-checked theorem or negative theorem:** a mathematical statement proved in Lean; a negative theorem is not a compiler mutation.
- **Semantic compiler mutation:** an actual changed false claim is rejected for its intended arithmetic, domain or typed-kernel obligation. Import, parser, missing-name and resource failures do not qualify.
- **Independent exact Python check:** an executed finite rational calculation or counterexample, with source hashes and individual test output. It does not replace a generic theorem.
- **Executed theorem-interface gate:** the actual four-factor theorem applies with all four data arguments; omitting only the fourth produces the expected type obligation. This is an interface rejection, not a mathematical countermodel.
- **Information-class, type or source-hypothesis gate:** the admitted policy domain or theorem premises are explicit. Locating such a gate in source never counts as executing a rejected mutation.

The selected declaration audit checks actual imported constants and their transitive axioms, binding its execution to current provider-source and compiled-artifact hashes. Owners' full source compilation receipts remain separate. Newly authored files without current artifacts remain pending. Anonymous fixture statements are linked to their actual source-bound fixture receipts rather than given invented declaration names.

Hashes identify the raw bytes actually measured. A Windows CRLF source and a Git/CI LF checkout can have different hashes despite equal text. This ledger does not normalize that mismatch into executed evidence: rerun checks in the current environment. Local receipts and genuine CI remain separate observations.

The generator is [paper_closure_acceptance_evidence.py](../../verification/research/paper_closure_acceptance_evidence.py); its explicit routing is [paper_closure_acceptance_cases.py](../../verification/research/paper_closure_acceptance_cases.py). It does not edit the supplied registry or another unit's receipts. Saved ledger links use durable receipts; scratch-only evidence is excluded. The raw-evidence inventory preserves exact owner-receipt copies under this directory, whose Git attributes preserve the measured bytes. Older owner receipts stay unchanged in their original locations; their copies avoid publishing a link with a hash changed by Git's newline conversion.
