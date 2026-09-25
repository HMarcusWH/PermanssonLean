# Application JSON schemas

[Application home](../README.md) · [Canonical standard](../APPLICATION_STANDARD.md) · [CLI reference](../validator/README.md)

Start with [application_bundle.schema.json](application_bundle.schema.json), the
schema for a complete `application.json`. It composes five domain schemas and
shared definitions. There are seven schema files, not seven independent reports.

| Schema | Role |
|---|---|
| [application_bundle](application_bundle.schema.json) | Versions, application ID, artifacts, and the complete report envelope |
| [application_certificate](application_certificate.schema.json) | Nine independent status dimensions and the protocol/pipeline links |
| [semantic_pipeline](semantic_pipeline.schema.json) | Frozen semantic bindings, component inventory, and selection account |
| [intervention_protocol](intervention_protocol.schema.json) | Typed targets, held-fixed components, replacements, and assessments |
| [provenance_graph](provenance_graph.schema.json) | Declared claims, dependencies, and evidence roots |
| [identified_set](identified_set.schema.json) | Model/state quantification, uncertainty, direction, and uniform-gap declarations |
| [common](common.schema.json) | Shared identifiers, artifact records, and regime assertions |

The dialect is JSON Schema 2020-12. `$id` and `$ref` URLs identify resources in the
validator's **local registry**; they are not promised public download endpoints.
Unknown fields are rejected. Explicit null values are not shorthand for success.

A schema-only check is insufficient: hashes, references, chronology, target
partitions, provenance cycles, and reporting consistency need the
[full validator](../validator/README.md). From the repository root after setup:

```bash
python application/validator/validate_application.py application/examples/grounded_pr_minimal/application.json --json
```

See the [example bundles](../examples/README.md) for complete records and the
[standard crosswalk](../APPLICATION_STANDARD.md#1-authority-and-source-crosswalk)
for which rules come from the paper versus implementation conventions. Do not
edit a schema to make a particular application pass; contract changes require
versioning and regression review.
