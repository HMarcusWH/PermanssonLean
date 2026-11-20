# Getting started with the reviewed second edition

[Current documentation](README.md) · [Publication hub](../../paper2/README.md) · [Verification](VERIFICATION.md)

## Read without installing anything

Open the [reviewed manuscript PDF](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Reviewed_Manuscript_2026-11-20.pdf). Its 31 sections and appendices A–P form one paper. For a first pass, read sections 1, 3–6 and 31; then follow the part corresponding to the question you are studying.

| Reading goal | Paper route |
|---|---|
| Foundations, original predicates and equilibrium predecessor | Sections 1–6; appendices A–C |
| Finite and nonfinite occupation, classification and restart | Sections 7–10; appendices D–E |
| Admitted interventions, certificates and quantitative preservation | Sections 11–16; appendices F–I |
| Control, games, multi-agent mechanisms and causal models | Sections 17–25; appendices J–L |
| Specialized algebra, constructed cases and earlier applications | Sections 26–28; appendices M–N |
| Algorithms, source evidence and remaining obligations | Sections 29–31; appendices O–P |

Use the [glossary](GLOSSARY.md) for terminology and the [mathematical crosswalk](MATHEMATICAL_CROSSWALK.md) for source declarations. The preserved [v1.1.1 reference guide](../reference/README.md) has its own 46-chapter structure; use the [guide-to-paper map](GUIDE_TO_PAPER.md) to move between them.

## Reproduce the manuscript

Download and extract the [reviewed source/concordance ZIP](../../paper2/v2.0.1/Permansson_Regimes_v2_0_1_Source_and_Concordance_2026-11-20.zip) into a fresh directory. Enter its `Permansson_Regimes_v2_0_1` directory and read `README.txt` before running commands. Python 3 and a standard TeX Live or MiKTeX installation are required; the source README lists the TeX packages. The included exact calculation scripts use the Python standard library.

From that extracted source directory, run:

```bash
bash build.sh
```

The script checks and regenerates the manuscript index, runs the three included exact calculations and typesets `build/main.pdf`. It records the engine versions in `build/build_environment.txt`. On Windows, run the script in a Bash environment or use the equivalent commands from `README.txt`.

To typeset without rerunning those calculations:

```bash
python3 build_index.py
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=build main.tex
```

Typesetting is possible without a repository checkout. If the index builder finds a sibling `PermanssonLean` checkout, it also checks cited source paths. A successful TeX build is a manuscript-build result; it does not execute the complete Lean repository. PDF bytes may differ across TeX environments, so compare the recorded environment and content before making a byte-reproducibility claim.

## Review or build the Lean source

For the manuscript's mathematical source, use a clean checkout of `c5a36cd6189e2a249d5f4bc11f31698917dc8b10` and the checked-in toolchain/dependency files. From the repository root:

```bash
lake exe cache get
lake build
lake build PermanssonResearch
```

The default target and the separate research root cover different source sets. The [research build guide](../RESEARCH_BUILD.md) preserves historical compiler evidence and explains the build routes. The [verification guide](VERIFICATION.md) distinguishes compilation, axiom checks, generated instance replay and independent acceptance. Routine reproduction should retain the pinned `lean-toolchain` and `lake-manifest.json`.

## Run an application or validate a report

The [successor application](../../apps/permansson/application-successor/README.md) exposes 26 exact finite profiles, independent checkers and bounded source-bound Lean candidate families. Choose a profile through [application compatibility](APPLICATION_COMPATIBILITY.md), then use the package's actual command and supported-input documentation. The native [C10](../../apps/permansson/closure-successor/README.md) and [C11](../../apps/permansson/closure-successor-c11/README.md) replay tools remain separate.

For the frozen draft Application Standard v0.1.0, use the original [reporting walkthrough](../GETTING_STARTED.md) and [canonical standard](../../application/APPLICATION_STANDARD.md). Its report validation contract remains tied to the earlier paper. Current paper terminology does not silently change its schemas, identifiers or output fields.

## Contribute to the current documentation

Start with the repository's preserved [contribution rules](../../CONTRIBUTING.md) and the [version-lineage explanation](VERSION_LINEAGE.md). Current publication assets live under `paper2/`; current paper reading and source maps live under `docs/paper2/`. Original `paper/`, `provenance/`, `application/` and accepted historical release material have preservation contracts. The inherited A2 source-identity contract also preserves older documentation outside its five named exceptions.

Keep a change's scope explicit. A Markdown-only documentation PR follows the existing contributor rule. Publication PDF/ZIP/checksum/index additions are publication-artifact work. Application documentation changes may also require the package's existing inventory metadata to be reconciled. Its relative links must work when the application is copied or installed alone.

Before changing a mathematical claim, compare the paper statement, source declaration and all hypotheses. Document any semantic change through the appropriate mathematical review process. A renamed section or new link is not new proof or acceptance evidence. Changes to an edition's reviewed PDF/source need a new version and review record; preserve the preceding edition.

Record the actual checked commit, commands, environment and outcomes in the appropriate review evidence. Detached current-head receipts belong outside the checkout. Use [DOCUMENTATION_REVIEW.md](DOCUMENTATION_REVIEW.md) for this edition's documentation implementation evidence.
