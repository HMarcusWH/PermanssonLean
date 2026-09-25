# Reading glossary

[Repository home](../README.md) · [Documentation index](README.md) · [Paper](../paper/README.md)

These are reading aids for the repository's terminology, not replacements for the
paper's definitions or hypotheses. The paper remains the authority for mathematics;
the [Application Standard](../application/APPLICATION_STANDARD.md) defines the JSON contract.

| Term | Meaning here | Authoritative location |
|---|---|---|
| GR — Generated Regime | A declared regime specification satisfied by the generated joint process. Exact GR includes exact persistence and the declared occupation-convergence requirements. | Paper Section 4; [formalization map](FORMALIZATION_MAP.md#third-proof-milestone--exact-generated-regime-semantics) |
| PR — Permansson Regime | An Exact GR with a predeclared strategic-generator component constitutive of a defining property under an admissible frozen intervention. It is relative to that protocol and comparison set. | Paper Section 5 |
| EGR — Equilibrium-Generated Regime | The Paper-I predecessor; equilibrium certifies the selected strategic generator rather than becoming a primitive of the generalized regime layer. | [Foundational paper guide](../paper/supporting/foundational/README.md); paper Section 6 |
| Strategic generator | The pair of action-selection and strategic-update mechanisms, alpha and U. P is the separate world-transition mechanism. | Paper Section 3 |
| Typed intervention | A declared replacement specifying which mechanisms change and which remain fixed. A world/structural intervention is not silently relabelled strategic. | Paper Section 5.3 |
| Grounded property | A property that uses only information retained by the frozen relevance map g, with the required factorization. Grounding is not empirical identification. | Paper Section 5.2 |
| Constitutive effect / uniform margin | The property-output distance under intervention, and its infimum over the declared comparison set. Pointwise nonzero effects do not alone imply a common positive margin. | Paper Section 5.4 |
| Quasi-regime | A finite-horizon persistence object with declared horizon and tolerance; not an Exact PR. | Paper Section 4.4 |
| QSD — quasi-stationary distribution | An optional killed-process eigenmeasure certificate. It does not by itself establish the uniform finite-persistence gate. | Paper Sections 4.4 and 15.11 |
| Identified set | The structural models retained by the evidence and assumptions. Robust application claims quantify over the full relevant model/state set, not a representative or majority. | Paper Section 10.6 |
| Application certificate | The nine independent reporting dimensions; validity, direction, and uniform gap are not a single interchangeable verdict. | Paper Table 5; [standard vocabulary](../application/APPLICATION_STANDARD.md#3-orthogonal-certificate-vocabulary) |
| Semantic pipeline / pipeline ID | The jointly declared semantic choices and their versioned content digest. Hash consistency is not proof of authentic preregistration. | [Standard Section 4](../application/APPLICATION_STANDARD.md#4-frozen-semantic-pipeline) |
| Provenance DAG | A directed acyclic graph of claims and dependencies ending at declared roots. Structural validity does not authenticate the roots. | [Standard Section 5](../application/APPLICATION_STANDARD.md#5-rooted-provenance) |
| Fixture | A deliberately constructed test/example bundle. An expected-invalid fixture tests rejection; it is not a failed scientific experiment. | [Examples](../application/examples/README.md) |
| CI / gate | Continuous-integration jobs and pass/fail checks, each with a limited scope. Application, numerical, proof, and artifact checks establish different things. | [Verification guide](../verification/README.md) |
| Frozen snapshot | A specific source commit or artifact hash. Later repository documentation does not retroactively change that historical object. | [Provenance guide](../provenance/README.md) |

## Common distinctions

A record with `contract_valid=true` can still contain `validity=INVALID` or
`STRUCTURALLY_UNRESOLVED`. A successful digest proposal can still have
`contract_valid=false`. Robust pointwise PR can have ambiguous direction or an
unresolved uniform gap. These are intended distinctions, not conflicting labels.
See the [boundary table](APPLICATION_BOUNDARY.md) before interpreting any PASS.
