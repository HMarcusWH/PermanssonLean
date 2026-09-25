# Offline application validator

From the repository root, install `application/requirements.txt`, then run:

```bash
python application/validator/validate_application.py path/to/application.json --json
```

Python interface:

```python
from pathlib import Path
from application.validator.validate_application import load_json, validate_document
path = Path("path/to/application.json")
result = validate_document(load_json(path), path.parent)
assert result["scientific_claims_verified"] is False
```

The JSON Schema registry is bundled, versioned and closed to network retrieval.
Only bundle-local files are read. Validation does not write files or execute proof,
data-transformation or other application code. Use `--digest` to print a proposed
semantic-pipeline identifier; review and record it explicitly in the manifest and
certificate before external registration. It is not an auto-repair switch.

Exit codes and the digest algorithm are specified in
[APPLICATION_STANDARD.md](../APPLICATION_STANDARD.md). Input/configuration errors
exit 2; contract violations exit 1; a conforming record exits 0. `validity=INVALID`
is a possible value *inside* a conforming record and is not the CLI exit status.
