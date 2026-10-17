"""Validate captured real PR contexts and reject superseded acceptance evidence."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import zipfile

p = argparse.ArgumentParser()
p.add_argument('--repo', type=Path, required=True)
p.add_argument('--old-zip', type=Path, required=True)
p.add_argument('--new-zip', type=Path, required=True)
p.add_argument('--old-head', required=True)
p.add_argument('--old-base', required=True)
p.add_argument('--old-synthetic', required=True)
p.add_argument('--new-head', required=True)
p.add_argument('--new-base', required=True)
p.add_argument('--new-synthetic', required=True)
p.add_argument('--kind', choices=['head-change', 'base-change'], required=True)
p.add_argument('--report', type=Path, required=True)
a = p.parse_args()
sys.path.insert(0, str(a.repo.resolve()))
from verification.integrity.ci_context import require_pr_acceptance
from verification.integrity.git_objects import GitRepo
from verification.integrity.reports import HardeningError

def context(path):
    with zipfile.ZipFile(path) as z:
        entries = [e for e in z.infolist() if e.filename == 'context.json']
        if len(entries) != 1 or entries[0].file_size > 65536:
            raise ValueError('Expected one bounded context.json')
        result = json.loads(z.read(entries[0]))
    if result.get('format') != 'Permansson.Hardening.CIContext.v1':
        raise ValueError('Unexpected context format')
    return result

old, new = context(a.old_zip), context(a.new_zip)
repo = GitRepo(a.repo)
for captured, head, base, synthetic in [
    (old, a.old_head, a.old_base, a.old_synthetic),
    (new, a.new_head, a.new_base, a.new_synthetic),
]:
    require_pr_acceptance(captured, head=head, base=base, synthetic=synthetic)
    commit = repo.commit(synthetic)
    if commit.parents != (base, head) or captured['checked_tree'] != commit.tree:
        raise ValueError('Captured context differs from canonical synthetic objects')
if a.old_head == a.new_head or a.old_synthetic == a.new_synthetic:
    raise ValueError('Transition did not change head and genuine synthetic identity')
if a.kind == 'head-change' and a.old_base != a.new_base:
    raise ValueError('Head-only live exercise must hold the base fixed')
if a.kind == 'base-change' and a.old_base == a.new_base:
    raise ValueError('Base-change exercise requires an actual new base')
try:
    require_pr_acceptance(old, head=a.new_head, base=a.new_base,
                          synthetic=a.new_synthetic)
except HardeningError as exc:
    if exc.code != 'E_CONTEXT':
        raise
else:
    raise ValueError('Superseded report was accepted for current objects')
report = dict(format='Permansson.Hardening.LiveContextTransition.v1', status='PASS',
              kind=a.kind, old_context=old, new_context=new,
              old_zip_sha256=hashlib.sha256(a.old_zip.read_bytes()).hexdigest(),
              new_zip_sha256=hashlib.sha256(a.new_zip.read_bytes()).hexdigest(),
              previous_pair_positive_control='PASS',
              current_pair_positive_control='PASS',
              previous_pair_for_current_objects='E_CONTEXT',
              source='captured-GitHub-artifact-contexts-and-canonical-Git-objects',
              scope='source-binding; job-success-and-before-green chronology are separate captured evidence')
a.report.parent.mkdir(parents=True, exist_ok=True)
a.report.write_bytes((json.dumps(report, sort_keys=True, indent=2)+'\n').encode())
print(json.dumps(dict(status='PASS', kind=a.kind, stale_result='E_CONTEXT')))
