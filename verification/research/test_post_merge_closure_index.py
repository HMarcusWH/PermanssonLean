"""NEXT-02: independently verify PR79 source/CI/receipt binding.

This is an additive index validator, NOT a Lean proof or formal release gate.
A strict release check must fail while strengthened fixtures remain pending.
The original source/receipt files are read-only; never rewrite them.
"""
from __future__ import annotations
from collections import Counter
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
DOC = ROOT / 'research/paper_closures/post_merge_79'
B = '39279799834ae536bda715dedecdc11a32bf6c82'
H = 'a1f1a77a301178e33412595265e823a873fb7301'
S = 'fa0441227aa8b245b384b01b32f3bfb43a897f07'
M = '674c1b557d99ab080afb65a797a99cb5840eab62'
TREE = 'b391f32f503f07bcfd7b29d8c24c1f9ad61eb19f'
EXPECTED_DISPOSITIONS = {
    'SELECTED_STATEMENT_VERIFIED': 13,
    'SCOPED_THEOREM_FORMALIZED': 23,
    'CORE_THEOREM_FORMALIZED_INTEGRATION_OPEN': 1,
    'CONDITIONAL_ADAPTER_FORMALIZED': 5,
}
EXPECTED_NORM = {'RAW': 234, 'CRLF': 4, 'LF_FINAL_CRLF': 16,
                 'LF_FINAL_TWO_CRLF': 1, 'UNRESOLVED': 1}


def read_index(filename: str) -> dict:
    data = (DOC / filename).read_bytes()
    if not data.endswith(b'\n'):
        raise ValueError('index needs canonical LF termination')
    if b'\r' in data:
        raise ValueError('index includes noncanonical CR')
    return json.loads(data)


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def git(*args: str) -> str:
    return subprocess.check_output(['git', *args], cwd=ROOT, stderr=subprocess.PIPE,
                                   timeout=60).decode().strip()


@lru_cache(maxsize=None)
def git_source(path: str) -> bytes:
    if path.startswith('/') or '..' in Path(path).parts or '\\' in path:
        raise ValueError('unsafe audited path')
    return subprocess.check_output(['git', 'show', f'{M}:{path}'], cwd=ROOT,
                                   stderr=subprocess.PIPE, timeout=60)


def normalized_source(data: bytes, kind: str) -> bytes:
    if kind == 'RAW':
        return data
    if kind == 'CRLF':
        return data.replace(b'\n', b'\r\n')
    if kind == 'LF_FINAL_CRLF':
        if not data.endswith(b'\n'): raise ValueError('missing expected LF')
        return data[:-1] + b'\r\n'
    if kind == 'LF_FINAL_TWO_CRLF':
        if not data.endswith(b'\n\n'): raise ValueError('missing expected LF LF')
        return data[:-2] + b'\r\n\r\n'
    raise ValueError('not a supported exact source transformation: '+kind)


def validate_source_reference(data: bytes, entry: dict) -> bool:
    if sha(data) != entry['canonical_sha256']:
        return False
    if entry['classification'] == 'UNRESOLVED':
        return False
    return sha(normalized_source(data, entry['classification'])) == entry['published_sha256']


def pending_release(decisions: dict) -> bool:
    if not decisions['full_selected_programme_accepted']:
        return True
    if decisions['pending_ids']:
        return True
    if any(case['acceptance_decision'] == 'PENDING_STRENGTHENED_FIXTURE'
           for case in decisions['cases']):
        return True
    if decisions['claims_not_accepted']:
        return True
    return False


class PostMergeIndexTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.index = read_index('source_ci_index.json')
        cls.norm = read_index('receipt_normalization.json')
        cls.decisions = read_index('acceptance_decisions.json')

    def test_h_b_s_m_tree_and_counts(self):
        d = self.index
        self.assertEqual(d['reference'], {
            'B': B, 'H': H, 'S': S, 'M': M, 'tree_H_S_M': TREE,
            'B_is_PR79_base': True, 'S_parent_order': ['B', 'H'],
            'M_parent_order': ['B', 'H'],
            'PR79': 'https://github.com/HMarcusWH/PermanssonLean/pull/79'})
        self.assertEqual(d['contract_count'], 42)
        self.assertEqual(len(d['contracts']), 42)
        self.assertEqual(len({r['id'] for r in d['contracts']}), 42)
        self.assertEqual(d['contract_dispositions'], EXPECTED_DISPOSITIONS)
        self.assertEqual(Counter(x['disposition'] for x in d['contracts']), EXPECTED_DISPOSITIONS)
        for r in d['contracts']:
            self.assertTrue(r['required_hypotheses'])
            self.assertTrue(r['selected_scope'])
            self.assertTrue(r['declarations'])
            for decl in r['declarations']:
                self.assertEqual(len(decl['source_sha256']), 64)
                self.assertTrue(decl['signature_header'])

    def test_exact_git_commit_graph_and_identity(self):
        # The CI checkout must have full history; a missing commit is a failed check, never a skip.
        self.assertEqual(git('rev-parse', f'{M}^{{tree}}'), TREE)
        self.assertEqual(git('rev-parse', f'{H}^{{tree}}'), TREE)
        # A PR synthetic merge is not necessarily reachable from a later
        # fetch-depth:0 checkout. Never equate an absent local S object with
        # failed historical CI; require authenticated archived metadata instead.
        has_S = subprocess.run(['git','cat-file','-e',S+'^{commit}'],
             cwd=ROOT, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
        if has_S:
            self.assertEqual(git('rev-parse', f'{S}^{{tree}}'), TREE)
            self.assertEqual(git('rev-list', '--parents', '-n', '1', S).split(), [S, B, H])
        else:
            self.assertEqual(self.index['reference']['S'], S)
            self.assertEqual(self.index['reference']['S_parent_order'], ['B','H'])
            self.assertEqual(self.index['reference']['tree_H_S_M'], TREE)
            self.assertIn('github.com/', self.index['reference']['PR79'])
        self.assertEqual(git('rev-list', '--parents', '-n', '1', M).split(), [M, B, H])
        self.assertEqual(git('rev-parse', f'{B}^{{commit}}'), B)

    def test_actual_old_theorem_source_hashes(self):
        # Validates EVERY declaration's original exact-source context against Git objects.
        for row in self.index['contracts']:
            for dec in row['declarations']:
                with self.subTest(atlas_id=row['id'], path=dec['path'], declaration=dec['declaration']):
                    content = git_source(dec['path'])
                    self.assertEqual(sha(content), dec['source_sha256'])
                    self.assertIn(dec['signature_header'].encode(), content.replace(b'\r\n', b'\n'))

    def test_ci_sources_and_local_artifacts_are_not_conflated(self):
        ci = self.index['CI']
        self.assertEqual(len(ci['PR79_source_head']), 10)
        self.assertEqual(len(ci['merged_main']), 6)
        self.assertEqual(len(ci['local_audit_archived_job_logs']), 22)
        self.assertEqual(len(ci['locally_verified_downloaded_GitHub_artifact_ZIPs']), 6)
        for field, expected in [('PR79_source_head', H), ('merged_main', M)]:
            for e in ci[field]:
                self.assertEqual(e['head_sha'], expected)
                self.assertEqual(e['conclusion'], 'success')
                self.assertIn('/actions/runs/', e['run_url'])
        self.assertEqual(ci['axiom_allowlist'], ['Classical.choice', 'Quot.sound', 'propext'])
        self.assertEqual(ci['Research_PR79_declarations'], 10443)
        self.assertEqual(ci['Research_PR79_test_methods'], 918)
        self.assertIn('UNVERIFIED', self.index['claimed_17_check_679_reference_census'])
        self.assertIn('NO_SUBMITTED_REVIEW', self.index['review_status'])

    def test_all_historical_receipt_transformations_or_declared_retirement(self):
        d = self.norm
        self.assertEqual(d['count'], 256)
        self.assertEqual(d['counts'], EXPECTED_NORM)
        self.assertEqual(Counter(x['classification'] for x in d['records']), EXPECTED_NORM)
        invalid = []
        for x in d['records']:
            with self.subTest(receipt=x['receipt'], source=x['source']):
                content = git_source(x['source'])
                self.assertEqual(sha(content), x['canonical_sha256'])
                if x['classification'] != 'UNRESOLVED':
                    self.assertTrue(validate_source_reference(content, x))
                else: invalid.append(x)
        self.assertEqual(len(invalid), 1)
        self.assertEqual(invalid[0]['source'], d['historical_mismatch_disposition']['source'])
        self.assertEqual(d['historical_mismatch_disposition']['status'],
                         'RETIRED_UNRECONCILED_OWNER_RECEIPT_BINDING')
        self.assertEqual(invalid[0]['published_sha256'],
                         d['historical_mismatch_disposition']['published_sha256'])

    def test_45_routed_decisions_are_not_certification(self):
        d = self.decisions
        self.assertEqual(d['case_count'],45)
        self.assertEqual(len(d['cases']),45)
        ids={x['id'] for x in d['cases']}
        self.assertEqual(len(ids),45)
        self.assertEqual(set(d['pending_ids']),
           {x['id'] for x in d['cases'] if x['acceptance_decision']=='PENDING_STRENGTHENED_FIXTURE'})
        self.assertFalse(d['full_selected_programme_accepted'])
        self.assertTrue(pending_release(d))
        self.assertTrue(d['claims_not_accepted'])
        self.assertTrue(d['unverified_owner_digest_retired_from_authority'])
        self.assertIn('PENDING',d['strict_release_gate'])

    def test_bad_source_binding_is_rejected(self):
        v={'classification':'RAW','canonical_sha256':sha(b'correct'),
           'published_sha256':sha(b'correct')}
        self.assertTrue(validate_source_reference(b'correct',v))
        self.assertFalse(validate_source_reference(b'incorrect',v))
        v['published_sha256']=sha(b'incorrect')
        self.assertFalse(validate_source_reference(b'correct',v))

    def test_bad_transform_does_not_pass(self):
        data=b'abc\ndef\n'
        v={'classification':'CRLF','canonical_sha256':sha(data),
           'published_sha256':sha(data.replace(b'\n',b'\r\n'))}
        self.assertTrue(validate_source_reference(data,v))
        v['classification']='RAW'
        self.assertFalse(validate_source_reference(data,v))

    def test_partial_row_cannot_be_declared_release_complete(self):
        d={'full_selected_programme_accepted':True,'pending_ids':['X-01'],
           'claims_not_accepted':[], 'cases':[]}
        self.assertTrue(pending_release(d))
        d['pending_ids']=[]
        d['cases']=[{'acceptance_decision':'PENDING_STRENGTHENED_FIXTURE'}]
        self.assertTrue(pending_release(d))
        d['cases']=[]
        d['claims_not_accepted']=['code review absent']
        self.assertTrue(pending_release(d))
        d['claims_not_accepted']=[]
        self.assertFalse(pending_release(d))


if __name__ == '__main__':
    if '--strict' in sys.argv:
        d=read_index('acceptance_decisions.json')
        if pending_release(d):
            print('FAIL_CLOSED: strengthened acceptance, review, or other required evidence still pending')
            raise SystemExit(2)
        print('Strict release-check gate passed')
    else:
        unittest.main()
