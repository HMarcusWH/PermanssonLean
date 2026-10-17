"""Refresh external, unexecuted ledger provenance from a reviewed canonical T."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

p = argparse.ArgumentParser()
p.add_argument('--repo', required=True)
p.add_argument('--tooling', required=True)
p.add_argument('--input', required=True)
p.add_argument('--output', required=True)
a = p.parse_args()
sys.path.insert(0, str(Path(a.repo).resolve()))
from verification.integrity.git_objects import GitRepo

target = Path(a.output)
if target.exists():
    raise RuntimeError('Refuse to overwrite previous provenance')
ledger = json.loads(Path(a.input).read_bytes())
if not ledger['template_only'] or len(ledger['cases']) != 108:
    raise RuntimeError('Expected unexecuted complete template')
if any(c['status'] != ('DEFERRED_BY_USER' if c['level'] == 'authorized_rollout' else 'PENDING_EVIDENCE')
       for c in ledger['cases']):
    raise RuntimeError('Template already contains execution claims')
repo = GitRepo(a.repo)
try:
    repo.commit(a.tooling)
    tree = repo.tree(a.tooling)
    def refresh(record):
        entry = tree[record['path'].encode()]
        if entry.mode != '100644' or entry.object_type != 'blob':
            raise RuntimeError('Nonregular provenance input')
        payload = repo.blob(entry.oid)
        record.update(commit=a.tooling, git_blob=entry.oid,
                      sha256=hashlib.sha256(payload).hexdigest())
    refresh(ledger['registry_source'])
    registry = json.loads(repo.blob(tree[b'verification/integrity/test_coverage.json'].oid))
    canonical = {row['id']: row for row in registry['cases']}
    supplied = {row['id']: row for row in ledger['cases']}
    if len(canonical) != 108 or len(supplied) != 108 or set(canonical) != set(supplied):
        raise RuntimeError('Template requirement IDs differ from canonical registry')
    for identity, row in supplied.items():
        expected = canonical[identity]
        if (row['level'] != expected['level'] or row['suite'] != expected['suite']
                or row['required_methods'] != expected['methods']):
            raise RuntimeError('Template level/suite/method mapping differs: ' + identity)
        if row.get('actual_result') is not None or row.get('checked_sha') is not None or row.get('evidence') != []:
            raise RuntimeError('Template contains execution fields: ' + identity)
    for condition in ledger['additional_acceptance_conditions']:
        if (condition['status'] != 'PENDING_EVIDENCE' or condition.get('actual_result') is not None
                or condition.get('checked_sha') is not None or condition.get('checked_tree') is not None
                or condition.get('evidence') != []):
            raise RuntimeError('Additional acceptance condition already contains execution')
    for key, value in ledger['maintenance_context'].items():
        expected = ('HMarcusWH/PermanssonLean' if key == 'repository'
                    else [] if key in ('review_evidence', 'workflow_runs') else None)
        if value != expected:
            raise RuntimeError('Template maintenance context already populated: ' + key)
    ledger['registry_controls'] = registry['controls']
    refresh(ledger['additional_acceptance_conditions'][0]['production_tooling_source'])
    for record in ledger['contract_document_provenance']['amended_active_documents']:
        refresh(record['active'])
    ledger['acceptance_plan_provenance']['amendments'].append(
        'The active implementation specification also requires local candidate=HEAD and full canonical T/C code+guide closure; standalone replay supplies no candidate-CI acceptance.')
    raw = (json.dumps(ledger, indent=2, sort_keys=True) + '\n').encode()
    target.write_bytes(raw)
    print(json.dumps({'status': 'PROVENANCE_REFRESH_ONLY', 'tooling': a.tooling,
                      'cases': 108, 'pending': 96, 'deferred': 12,
                      'bytes': len(raw), 'sha256': hashlib.sha256(raw).hexdigest()}))
finally:
    repo.close()
