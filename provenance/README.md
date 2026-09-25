# Release provenance guide

[Repository home](../README.md) · [Paper guide](../paper/README.md) · [Verification guide](../verification/README.md)

This directory identifies the artifacts associated with the frozen v0.1.8 release.
It is not the provenance graph of a user's empirical application; that separate
format is described in the [Application Standard](../application/APPLICATION_STANDARD.md#5-rooted-provenance).

## Which record should I use?

| Record | Purpose |
|---|---|
| [Paper verification manifest](../docs/PAPER_VERIFICATION_MANIFEST.md) | Human-readable release identity, snapshot, verification layers, and scope |
| [Release metadata](../docs/releases/v0.1.8.json) | Machine-readable artifact names and hashes |
| [Paper build audit](v0.1.8/PAPER_BUILD_AUDIT.md) | Preserved editorial-final build summary |
| [PDF hash](v0.1.8/PAPER_PDF_SHA256.txt) / [TeX hash](v0.1.8/PAPER_TEX_SHA256.txt) | Distributed paper artifact identities |
| [Frozen suite hash](v0.1.8/TEST_SUITE_SHA256.txt) / [portable suite hash](v0.1.8/PORTABLE_TEST_SUITE_SHA256.txt) | Distinguish the evidentiary archive from its runnable derivative |
| [Release ZIP hash](v0.1.8/RELEASE_ZIP_SHA256.txt) | Identity of the complete Windows-safe release package |
| [Lean provenance and crosswalk](../verification/lean/README.md) | The paper's exact formalization commit and recorded CI |

## Repository versus release package

The repository hosts the final PDF/TeX and runnable verification source. It does not
duplicate the frozen destructive-suite ZIPs, full historical control workpacks, or
complete release ZIP. A GitHub-generated source archive is not the named release
package and must not be checked against its hash.

The same paper bytes can have different repository and distribution filenames.
The [paper guide](../paper/README.md) and release metadata explain those mappings;
hashes, not the word FINAL in a filename, identify the artifact. Use the repository
gate for the checked-in files:

```bash
python verification/repository_gate.py
```

Run this from the repository root with Python 3.13. For external package
reproduction, obtain the exact named package from its distributor and use the
[release-gate guide](../verification/v0.1.8_release_gate/README.md). The repository
records identifiers; it does not supply a download endpoint for missing assets.

Later documentation or application-standard commits do not change the paper's
immutable mathematical snapshot or historical PASS records. Keep fresh test results
attached to their own commit/environment rather than editing these records.
