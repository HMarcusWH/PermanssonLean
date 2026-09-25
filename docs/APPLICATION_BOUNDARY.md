# Application contract versus formal verification

The [Application Standard](../application/README.md) is a separately versioned draft
serialization/validation layer for v0.1.8 Sections 10.5-10.7. Its
[rule crosswalk](../application/APPLICATION_STANDARD.md#1-authority-and-source-crosswalk)
separates source-derived requirements from implementation conventions.

This is a fourth verification concern, not added Lean coverage:

| Check | What it establishes | What it does not establish |
|---|---|---|
| Lean build/audit | Encoded theorem declarations on the pinned toolchain | Empirical premises or causal identification |
| Runs 17-30 | Executable falsification/regression checks | Deductive proof |
| Release/repository gates | Specified artifact and provenance synchronization | Scientific truth of application inputs |
| Application contract gate | Schema, hash, reference, declared-scope and consistency checks | Mathematical proof, authentic registration, source truth, support, identification or statistical coverage |

The formalization ledger through Proposition 8.1 is unchanged. No application
status field is promoted to a theorem, and no validator PASS promotes an application
to a certified PR. The paper's nine orthogonal certificate dimensions are retained.
A well-formed record may report INVALID or STRUCTURALLY_UNRESOLVED; robust pointwise
PR may retain direction ambiguity or an unresolved uniform gap.

The [future theory roadmap](FUTURE_THEORY_ROADMAP.md) remains research, not v0.1.8.
No changes are made to the paper PDF/TeX, Lean source/import graph/toolchain,
CITATION.cff, frozen run artifacts, release hashes or Appendix E status.
