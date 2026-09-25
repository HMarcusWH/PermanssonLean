# Contributing

[Repository home](README.md) · [Documentation index](docs/README.md)

Start from the [setup guide](docs/GETTING_STARTED.md). Keep a contribution focused
on one layer: documentation, application contract, executable verification, or
formal mathematics. Explain changes against the existing paper/contract rather
than silently strengthening a definition or reinterpreting a historical result.

## Before editing

Create a branch from the intended base and inspect the files you will change.
Check the [formalization boundary](docs/FORMALIZATION_MAP.md#completion-boundary)
and [application boundary](docs/APPLICATION_BOUNDARY.md). Version numbers have
different roles: paper v0.1.8, application draft 0.1.0, and the frozen Lean package
metadata. Do not synchronize them by renaming or bumping them together.

Do not edit frozen paper PDF/TeX, release hashes, historical reports, or evidence
bytes to make a test pass. A scientific extension needs its own definition,
hypotheses, proof/counterexamples, tests, and release boundary; see the
[research roadmap](docs/FUTURE_THEORY_ROADMAP.md).

## Documentation changes

Start at the root README and follow the links affected by your change. Put setup
in the getting-started guide, command semantics in the application standard/CLI
reference, and proof scope in the formalization map. Avoid copying historical
PASS counts into undated claims about a new run.

Use relative repository links and state the working directory for commands.
Distinguish a normal clone from an extracted release package. Test code examples
where the required environment is available, and report what was not executed.
Preserve existing anchors when practical. Check Linux/macOS and PowerShell
instructions without assuming environment activation is always permitted.

A documentation-only PR should change Markdown, not source code, dependencies,
schemas, workflows, fixtures, or release metadata. Add navigation around preserved
historical documents instead of rewriting their evidence.

## Application-contract changes

Run from the repository root after installing the application requirements:

```bash
python -m unittest discover -s application/tests -v
python application/examples/build_examples.py
python verification/application_gate.py
```

Add positive and negative regression cases for the changed rule. Check JSON/text
output, digest bootstrap, argument errors, exit codes, read-only behavior, raw
artifact bytes, and both supported CI platforms when relevant. Never use digest
proposal success as contract-validation success, or contract validation as
scientific certification.

Keep application studies outside `application/examples/` unless they are deliberate
synthetic fixtures. The fixture generator has an explicit `--write` mode; routine
testing does not require it. Review any intentional fixture change together with
its generator, hashes, and expected error codes. Do not upload private data or
credentials as evidence.

The current schema vocabulary and digest profile are versioned. Wire-rule changes
need an explicit application-version decision; do not quietly reinterpret an
existing identifier. Documentation clarifications alone do not change wire rules.

## Verification and Lean changes

Use the [verification guide](verification/README.md) for the commands and environment
for each layer. After a numerical change, rerun Runs 17–30 and the repository gate.
After a Lean change, build on the pinned toolchain and inspect the Lean workflow's
axiom/placeholder checks. New formal claims need an accurate paper-to-Lean mapping;
no placeholder or assumed theorem may stand in for the requested proof.

Do not present compact repository fixtures as a fresh reconstruction of unavailable
historical workpacks. Use the corresponding release package to reproduce a
package-level audit. A rerun in a different dependency environment must say so.

## Pull-request checklist

- State the base commit, changed layer, reason, and preserved boundaries.
- List exact checks and their actual results; distinguish local execution from CI,
  current-head results from earlier runs, and unrun checks from passed checks.
- Review the diff for unrelated files, evidence changes, and documentation drift.
  Read all new review comments, add regression coverage for fixes, and verify the
  updated head before describing the PR as green.

A green job or a clean automated review is evidence from that check, not a guarantee
that no issue can remain. Report a minimal reproduction with the command, commit,
working directory, versions, exit code, and redacted output when a problem is found.
