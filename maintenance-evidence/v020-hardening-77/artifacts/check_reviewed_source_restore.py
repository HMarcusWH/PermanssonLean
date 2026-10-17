"""Local source restoration only; the Linux CI gate separately enforces offline replay."""
from dataclasses import asdict
import hashlib
import json
from pathlib import Path
import sys

workspace = Path(__file__).resolve().parents[1]
repository = workspace / 'PermanssonLean-hardening'
sys.path.insert(0, str(repository))
from verification.archive.manifest import validate_manifest, read_bounded, strict_json
from verification.archive.verify_bundle import validate_tooling, parse_objects, restore_history
from verification.archive.create_bundle import derive_registry, validate_bindings
from verification.integrity.git_objects import GitRepo
from verification.integrity.ci_context import capture_context

source = workspace / 'artifacts/Permansson-v020-supplement-1-reviewed'
destination = workspace / 'artifacts/hardening-reviewed-source-restore'
manifest = validate_manifest(source)
validate_tooling(source, manifest)
registry = strict_json(read_bounded(source / 'refs.json'))
objects = parse_objects(source / 'objects.jsonl')
restored = restore_history(source / 'history.bundle', destination, registry, objects)
if derive_registry(restored) != registry:
    raise SystemExit('Restored registry differs from fixed accepted authority')
validate_bindings(restored, registry)
repo = GitRepo(repository)
head = repo.run('rev-parse', 'HEAD').decode().strip()
report = dict(format='Permansson.Hardening.LocalSourceRestore.v1', status='PASS',
              context=asdict(capture_context(repo, head)),
              manifest_sha256=hashlib.sha256((source / 'archive-manifest.json').read_bytes()).hexdigest(),
              bundle_sha256=manifest['bundle']['sha256'], bundle_size=manifest['bundle']['size'],
              refs=len(registry['refs']), input_commits=len({row['commit'] for row in registry['refs']}),
              objects=len(objects), tooling_source=manifest['tooling']['source_commit'],
              network_isolation='NOT_ENFORCED', artifact_replay='NOT_PERFORMED',
              fresh_lean_execution='NOT_PERFORMED', publisher_authentication=False)
(workspace / 'artifacts/hardening-reviewed-source-restore.json').write_bytes(
    (json.dumps(report, sort_keys=True, indent=2) + '\n').encode())
print(json.dumps(report, sort_keys=True))
