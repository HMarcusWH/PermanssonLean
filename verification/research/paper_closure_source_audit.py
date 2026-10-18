"""Check all source-register references against canonical pinned Git blobs.

Working-tree line ending conversion cannot authenticate a source register.
This command reads the immutable commit objects instead. No files are changed.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess


def audit(repo: Path) -> dict:
    package = repo / 'research/paper_closures/spec'
    registry = json.loads((package / 'sources/source_register.json').read_text('utf-8'))
    reference = registry['source_commit']
    checks = []
    for row in registry['sources']:
        raw = subprocess.run(['git', 'show', f"{reference}:{row['path']}"],
                             cwd=repo, check=True, capture_output=True).stdout
        sha256 = hashlib.sha256(raw).hexdigest()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        passed = (len(raw) == row['bytes'] and sha256 == row['sha256'] and
                  blob == row['git_blob_sha1'])
        checks.append({'id': row['id'], 'path': row['path'],
                       'bytes': len(raw), 'sha256': sha256,
                       'git_blob_sha1': blob, 'status': 'PASS' if passed else 'FAIL'})
    return {'format': 'Permansson.PaperClosureSourceAudit.v1',
            'reference': reference, 'source_count': len(checks),
            'status': 'PASS' if all(r['status'] == 'PASS' for r in checks) else 'FAIL',
            'checks': checks,
            'boundary': 'Canonical source identity, not mathematical theorem verification.'}


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    result = audit(Path(__file__).resolve().parents[2])
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: v for k, v in result.items() if k != 'checks'}, indent=2))
    raise SystemExit(0 if result['status'] == 'PASS' else 1)
