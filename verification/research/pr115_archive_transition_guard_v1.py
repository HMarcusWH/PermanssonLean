"""Read-only PR115 gate diagnosis through the EXISTING PR113 migration contract.

No historical verifier, archived file, active workflow or review authority is
changed. The original mandatory archive job must remain FAIL/CLOSURE until an
independently reviewed and owner-authorized separate T/T2 profile is active.

An unapproved migration report cannot be used as a required-check substitute.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys

from pr113_tooling_migration import (audit as original_audit, T, B, SUPPLEMENT,
                                     EXPECTED_CHANGES, ToolingMigrationError,
                                     SHA40, git)

FORMAT = 'Permansson.PR115.ArchiveTransitionDiagnosis.v1'


def diagnose(repo: Path, head: str, *, include_staged: bool = True,
             original_t: str = T, original_b: str = B) -> dict:
    root = Path(repo).resolve(strict=True)
    if not isinstance(head, str) or SHA40.fullmatch(head) is None:
        raise ToolingMigrationError('candidate must have a full exact Git SHA')
    if not root.is_dir() or not (root / '.git').exists():
        raise ToolingMigrationError('requires a real Git source checkout')
    # Require clean, exact-source execution, not a local overlay, foreign
    # working tree, borrowed H or uncommitted workflow edits.
    if Path(git(root, 'rev-parse', '--show-toplevel').decode().strip()).resolve() != root:
        raise ToolingMigrationError('refusing a nested or foreign checkout')
    if git(root, 'status', '--porcelain=v1', '--untracked-files=all'):
        raise ToolingMigrationError('candidate source is not a clean Git checkout')
    baseline = original_audit(root, head, historical_t=original_t, release_base=original_b)
    if (baseline.get('current_workflow_file_count') != 25 or
            baseline.get('historical_archive_unchanged') is not True or
            baseline.get('new_successor_T_approved') is not False or
            baseline.get('independent_tooling_review') is not False or
            {row['path'] for row in baseline['changed_canonical_tooling']} != EXPECTED_CHANGES):
        raise ToolingMigrationError('legacy 25/T source preflight did not preserve review boundaries')
    staged = None
    if include_staged:
        # The staged profile was authored under PR113 and is reused, not
        # forked or rewritten under this application PR.
        from pr113_tooling_migration_v2 import audit as staged_audit
        staged = staged_audit(root, head, phase='staged')
        if (staged.get('new_successor_T_approved') is not False or
                staged.get('independent_security_review') is not False or
                staged.get('owner_activation_authorized') is not False or
                staged.get('current_reviewed_workflow_count') != 30 or
                staged.get('historical_original_workflow_count') != 25):
            raise ToolingMigrationError('staged 30-workflow contract is not the unapproved review candidate')
    return {
        'format': FORMAT,
        'status': 'CLOSURE_DRIFT_IDENTIFIED_REVIEW_REQUIRED',
        'candidate_head': head,
        'historical_tooling_commit_T': original_t,
        'historical_archive_base_B': original_b,
        'historical_manifest_sha256': baseline['historical_manifest_sha256'],
        'historical_tooling_file_count': baseline['historical_packaged_tooling_files_verified'],
        'current_workflow_count': baseline['current_workflow_file_count'],
        'proposed_staged_workflow_count': staged['current_reviewed_workflow_count'] if staged else None,
        'changed_tooling_blobs': baseline['changed_canonical_tooling'],
        'migration_source': 'verification/research/pr113_tooling_migration_v2.py' if staged else
            'verification/research/pr113_tooling_migration.py',
        'historical_snapshot_unchanged': True,
        'requires_distinct_original_T_offline_execution': True,
        'requires_current_H_integrity_execution': True,
        'requires_independent_security_review': True,
        'requires_owner_activation': True,
        'original_archive_current_candidate_gate_passed': False,
        'historical_archive_repair_accepted': False,
        'mathematical_acceptance': False,
        'publication_authorized': False,
    }


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo',required=True,type=Path)
    parser.add_argument('--head',required=True)
    parser.add_argument('--out',required=True,type=Path)
    parser.add_argument('--no-staged',action='store_true')
    opts=parser.parse_args(argv)
    try:
        out=opts.out.absolute()
        if (out.exists() or out.is_symlink() or
                any(p.is_symlink() for p in out.parents) or
                out == opts.repo.resolve() or opts.repo.resolve() in out.parents):
            raise ToolingMigrationError('diagnostic must be a fresh detached ordinary path')
        evidence=diagnose(opts.repo,opts.head,include_staged=not opts.no_staged)
        out.parent.mkdir(parents=True,exist_ok=True)
        out.write_text(json.dumps(evidence,sort_keys=True,indent=2)+'\n',encoding='utf-8')
        print(json.dumps({'status':evidence['status'],'source_head':evidence['candidate_head'],
                          'current_archive_gate_repaired':False},sort_keys=True))
        return 0
    except (OSError,KeyError,ToolingMigrationError,ValueError) as exc:
        print('PR115 archive migration candidate BLOCKED: '+str(exc),file=sys.stderr)
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
