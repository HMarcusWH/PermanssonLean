"""Adversarial S01/S02 source, scope, proof and acceptance boundaries."""
from __future__ import annotations
import hashlib,json,tempfile,unittest
from pathlib import Path
from permansson_app.errors import AppError
from permansson_app.versioning import SourcePin
from permansson_app.resources import RunBudget
from permansson_app.semantics import SemanticScope,compare_semantics
from permansson_app.provenance import check_provenance
from permansson_app.evidence import EvidenceSet,record_digest
from permansson_app.acceptance import AcceptanceTarget,AcceptancePolicy,assess_acceptance
from permansson_app.claims import ClaimRegistry,resolve_claim,evaluate_claim_scope
from permansson_app.replay import ReplayTarget,evaluate_replay
from permansson_app.reports import scientific_report
from permansson_app.identity import canonical_bytes
from permansson_app.federation.contracts import ExchangeContract
from permansson_app.federation.compatibility import verify_compatibility
from permansson_app.federation.local_engine import offer_numeric_capabilities

SOURCE={'repository':'HMarcusWH/PermanssonLean','commit':'a'*40,'tree':'b'*40,
        'application':'successor.0.2','research':'research.0.2','paper':'0.1.8'}
IDENT={'profile':'Permansson.App.TypedRationalJCS.v1','sha256':'b'*64}

def scope():
    return {'property':'finite_survival','objective':'evaluate_only','comparator':'exact_equal',
            'policy_class':'fixed_alpha','nature_chronology':'single_model','horizon':3,
            'state_universe':['x0','x1'],'comparison_starts':['x0','x1'],'mode':'numeric'}

def node(n,parents=(),known_at='2026-10-02T00:00:00+00:00',frozen_at=None):
    return {'id':n,'kind':'source','sha256':'a'*64,'parents':list(parents),
            'event_at':'2026-10-01T00:00:00+00:00','known_at':known_at,'frozen_at':frozen_at}

def record(eid='test',kind='numeric_test',status='PASS',method='t1',platform='linux'):
    return {'format':'Permansson.App.EvidenceRecord.v1','evidence_id':eid,'kind':kind,
            'subject_sha256':'c'*64,'source_commit':SOURCE['commit'],'source_tree':SOURCE['tree'],
            'capability':'c10.fixed_six_state.numeric.v1','execution_profile':'numeric',
            'platform':platform,'method_ids':[method],'status':status,'artifact_sha256':'d'*64,
            'producer':'github-actions','reviewer':None}

class VersionTests(unittest.TestCase):
    def test_separate_identity(self):
        pin=SourcePin.parse(SOURCE);self.assertEqual(pin.commit,SOURCE['commit']);self.assertNotEqual(pin.identity()['sha256'],SOURCE['tree'])
    def test_change_paper_changes_identity(self):
        other=SourcePin.parse({**SOURCE,'paper':'0.1.9'})
        self.assertNotEqual(SourcePin.parse(SOURCE).identity(),other.identity())
    def test_bad_sha(self):
        with self.assertRaises(AppError):SourcePin.parse({**SOURCE,'commit':'G'*40})
    def test_extra_field_rejected(self):
        with self.assertRaises(AppError):SourcePin.parse({**SOURCE,'certified':True})
    def test_distinct_source_semantics(self):
        with self.assertRaises(AppError):SourcePin.parse({**SOURCE,'repository':'other/repo'})

class BudgetTests(unittest.TestCase):
    def test_shared_budget(self):
        r=RunBudget(2,4,3)
        r.tick(1,2);r.tick(1,2)
        self.assertEqual(r.receipt()['steps_used'],2)
        with self.assertRaises(AppError):r.tick(1,0)
    def test_byte_limit(self):
        r=RunBudget(10,2,3)
        with self.assertRaises(AppError):r.tick(1,3)
    def test_negative_costs_rejected(self):
        with self.assertRaises(AppError):RunBudget(10,2,3).tick(-1,0)
    def test_zero_limit_rejected(self):
        with self.assertRaises(AppError):RunBudget(0,2,3)

class ScopeTests(unittest.TestCase):
    def test_full_region(self):
        s=SemanticScope.parse(scope());self.assertEqual(compare_semantics(s,s,uniform=True)['status'],'SCOPE_MATCH')
    def test_partial_region_fails_uniform(self):
        x=scope();x['comparison_starts']=['x1'];s=SemanticScope.parse(x)
        with self.assertRaises(AppError):compare_semantics(s,s,uniform=True)
    def test_subset_is_not_full_scope(self):
        s=SemanticScope.parse(scope());x=scope();x['comparison_starts']=['x0']
        with self.assertRaises(AppError):compare_semantics(s,SemanticScope.parse(x))
    def test_hidden_chronology_switch_fails(self):
        s=SemanticScope.parse(scope());x=scope();x['nature_chronology']='committed_at_time_zero'
        with self.assertRaises(AppError):compare_semantics(s,SemanticScope.parse(x))
    def test_bad_future_horizon(self):
        x=scope();x['horizon']=True
        with self.assertRaises(AppError):SemanticScope.parse(x)
    def test_false_mode(self):
        x=scope();x['mode']='certified'
        with self.assertRaises(AppError):SemanticScope.parse(x)

class ProvenanceTests(unittest.TestCase):
    def test_acyclic_with_missing_times_is_unresolved(self):
        res=check_provenance([node('a',known_at=None),node('b',['a'])])
        self.assertFalse(res['origin_authenticated']);self.assertIn('a',res['missing_known_at'])
    def test_topological_order(self):
        res=check_provenance([node('b',['a']),node('a')]);self.assertEqual(res['topological_order'],['a','b'])
    def test_cycle(self):
        with self.assertRaises(AppError):check_provenance([node('a',['b']),node('b',['a'])])
    def test_unknown_parent(self):
        with self.assertRaises(AppError):check_provenance([node('a',['none'])])
    def test_derived_before_parent(self):
        with self.assertRaises(AppError):check_provenance([node('a',known_at='2026-10-03T00:00:00+00:00'),node('b',['a'])])
    def test_late_freeze(self):
        x=check_provenance([node('a',frozen_at='2026-10-04T00:00:00+00:00')],evaluation_start='2026-10-03T00:00:00+00:00')
        self.assertIn('a',x['late_freezes'])
    def test_future_knowledge(self):
        x=check_provenance([node('a')],cutoff='2026-10-01T00:00:00+00:00')
        self.assertEqual(x['excluded_future_knowledge'],['a'])
    def test_timezone_required(self):
        bad=node('a');bad['known_at']='2026-10-02T00:00:00'
        with self.assertRaises(AppError):check_provenance([bad])
    def test_mismatched_repeated_id(self):
        with self.assertRaises(AppError):check_provenance([node('a'),node('a')])

class EvidenceTests(unittest.TestCase):
    def test_external_pin(self):
        x=record();y=EvidenceSet.from_external_hashes([x],trusted_expected_digests={'test':record_digest(x)})
        self.assertEqual(len(y.records),1)
    def test_mutation_rejected(self):
        x=record();pin=record_digest(x);x['status']='SKIPPED'
        with self.assertRaises(AppError):EvidenceSet.from_external_hashes([x],trusted_expected_digests={'test':pin})
    def test_not_self_approval(self):
        x=record(kind='owner_approval',method='release',status='PASS')
        y=EvidenceSet.from_external_hashes([x],trusted_expected_digests={'test':record_digest(x)})
        self.assertEqual(y.records[0].kind,'owner_approval')
    def test_duplicate_record(self):
        x=record()
        with self.assertRaises(AppError):EvidenceSet.from_external_hashes([x,x],trusted_expected_digests={'test':record_digest(x)})
    def test_skipped_is_not_success(self):
        x=record(status='SKIPPED');y=EvidenceSet.from_external_hashes([x],trusted_expected_digests={'test':record_digest(x)})
        self.assertNotEqual(y.records[0].status,'PASS')
    def test_foreign_hash(self):
        with self.assertRaises(AppError):EvidenceSet.from_external_hashes([record()],trusted_expected_digests={'test':'0'*64})
    def test_unused_pin_rejected(self):
        x=record();with_pin={'test':record_digest(x),'other':'0'*64}
        with self.assertRaises(AppError):EvidenceSet.from_external_hashes([x],trusted_expected_digests=with_pin)
    def test_float_receipt_invalid(self):
        x=record();x['method_ids']=[0.5]
        with self.assertRaises(AppError):record_digest(x)

class ClaimTests(unittest.TestCase):
    def test_56_historical_and_later_entries(self):
        from importlib.resources import files
        raw=json.loads(files('permansson_app').joinpath('data/claim_registry.json').read_text())
        r=ClaimRegistry.parse(raw)
        self.assertEqual(len(r.claims),56)
        self.assertEqual(len([x for x in r.claims if x.classification=='historical_case']),45)
        self.assertEqual(len([x for x in r.claims if x.classification=='later_claim']),11)
        self.assertFalse(any(x.original_accepted for x in r.claims))
    def test_56_not_auto_certified(self):
        from importlib.resources import files
        r=ClaimRegistry.parse(json.loads(files('permansson_app').joinpath('data/claim_registry.json').read_text()))
        x=record();e=EvidenceSet.from_external_hashes([x],trusted_expected_digests={'test':record_digest(x)})
        claim=resolve_claim('X-01',r)
        self.assertFalse(evaluate_claim_scope(claim,e).mathematical_acceptance)
    def test_absent_claim(self):
        with self.assertRaises(AppError):resolve_claim('NONEXISTENT',ClaimRegistry(()))

class AcceptanceTests(unittest.TestCase):
    def target(self,mode='numeric'):
        return AcceptanceTarget.parse({'source':SOURCE,'subject_sha256':'c'*64,
         'wheel_sha256':'d'*64,'sdist_sha256':'e'*64,'capabilities':['c10.fixed_six_state.numeric.v1'],
         'platforms':['linux'],'execution_profile':mode})
    def policy(self):
        return AcceptancePolicy.parse({'format':'Permansson.App.AcceptancePolicy.v1',
         'required':{'c10.fixed_six_state.numeric.v1':{'numeric_test':['t1']}},
         'security_review_required':True,'owner_activation_required':True})
    def evidence(self,*values):
        return EvidenceSet.from_external_hashes(list(values),trusted_expected_digests={r['evidence_id']:record_digest(r) for r in values})
    def test_missing_is_blocked(self):
        x=assess_acceptance(self.target(),self.evidence(),self.policy())
        self.assertEqual(x.status,'BLOCKED_MISSING_EVIDENCE');self.assertFalse(x.authorized_release)
    def test_one_green_is_not_release(self):
        x=assess_acceptance(self.target(),self.evidence(record()),self.policy())
        self.assertFalse(x.authorized_release)
        self.assertIn('EXTERNAL_OWNER_RELEASE_ACTIVATION',x.missing)
    def test_skip_does_not_pass(self):
        x=assess_acceptance(self.target(),self.evidence(record(status='SKIPPED')),self.policy())
        self.assertEqual(x.status,'BLOCKED_FAILED_EVIDENCE')
    def test_other_source_does_not_fill(self):
        r=record();r['source_commit']='f'*40
        x=assess_acceptance(self.target(),self.evidence(r),self.policy())
        self.assertIn('c10.fixed_six_state.numeric.v1/linux/numeric_test/t1',x.missing)
    def test_windows_is_independent(self):
        tar=AcceptanceTarget.parse({'source':SOURCE,'subject_sha256':'c'*64,'wheel_sha256':'d'*64,'sdist_sha256':'e'*64,'capabilities':['c10.fixed_six_state.numeric.v1'],'platforms':['linux','windows'],'execution_profile':'numeric'})
        x=assess_acceptance(tar,self.evidence(record()),self.policy())
        self.assertIn('c10.fixed_six_state.numeric.v1/windows/numeric_test/t1',x.missing)
    def test_proof_mode_requires_evidence(self):
        x=assess_acceptance(self.target('lean_replay'),self.evidence(),self.policy())
        self.assertTrue(any('lean_compiler' in key for key in x.missing))
    def test_strict_all_caps(self):
        tar=self.target()
        with self.assertRaises(AppError):AcceptanceTarget.parse({'source':SOURCE,'subject_sha256':'c'*64,'wheel_sha256':'d'*64,'sdist_sha256':'e'*64,'capabilities':[],'platforms':['linux'],'execution_profile':'numeric'})

class ReplayTests(unittest.TestCase):
    def test_compiler_without_evidence_rejected(self):
        target=ReplayTarget.parse({'source_commit':'a'*40,'source_tree':'b'*40,'subject_sha256':'c'*64,
         'emitted_sha256':'d'*64,'theorem_type_sha256':'e'*64,'declaration':'Proof.theorem','toolchain':'lean4-v4.34.0'})
        transcript={'format':'Permansson.App.LeanReplayTranscript.v1',
                    **{k:getattr(target,k) for k in ('source_commit','source_tree','subject_sha256','emitted_sha256','theorem_type_sha256','declaration','toolchain')},
                    'compiler_exit':0,'axiom_audit_exit':0,'transitive_axioms':[],
                    'compiler_evidence_id':'a','audit_evidence_id':'b','negative_evidence_id':'c'}
        with self.assertRaises(AppError):evaluate_replay(target,transcript,EvidenceSet((),()))
    def test_axiom_injection_rejected(self):
        target=ReplayTarget.parse({'source_commit':'a'*40,'source_tree':'b'*40,'subject_sha256':'c'*64,
         'emitted_sha256':'d'*64,'theorem_type_sha256':'e'*64,'declaration':'Proof.theorem','toolchain':'lean4-v4.34.0'})
        transcript={'format':'Permansson.App.LeanReplayTranscript.v1',
                    **{k:getattr(target,k) for k in ('source_commit','source_tree','subject_sha256','emitted_sha256','theorem_type_sha256','declaration','toolchain')},
                    'compiler_exit':0,'axiom_audit_exit':0,'transitive_axioms':['axiom.Evil'],
                    'compiler_evidence_id':'a','audit_evidence_id':'b','negative_evidence_id':'c'}
        with self.assertRaises(AppError):evaluate_replay(target,transcript,EvidenceSet((),()))

class FederationTests(unittest.TestCase):
    def contract(self):return ExchangeContract.parse({'format':'Permansson.App.FederationContract.v1',
            'source':SOURCE,'capability':'c10.fixed_six_state.numeric.v1','mode':'numeric',
            'subject_sha256':'a'*64,'artifact_sha256':'b'*64})
    def test_contract_compatibility(self):
        c=self.contract();r=verify_compatibility(c,c,approved_capabilities=frozenset({c.capability}))
        self.assertFalse(r['permission_to_execute'])
    def test_forbidden_capability(self):
        c=self.contract()
        with self.assertRaises(AppError):verify_compatibility(c,c,approved_capabilities=frozenset())
    def test_unknown_local_engine(self):
        with self.assertRaises(AppError):offer_numeric_capabilities(frozenset({'fictional'}))
    def test_local_offer_read_only(self):
        r=offer_numeric_capabilities(frozenset({'c10.fixed_six_state.numeric.v1'}))
        self.assertFalse(r['permission_to_execute'])
    def test_report_looks_not_certified(self):
        r=scientific_report(SourcePin.parse(SOURCE),'numeric',IDENT,{'numeric':'SUPPORTED'})
        self.assertFalse(r['scientific_claims_verified']);self.assertEqual(r['scientific_certificate_dimensions']['lean'],'UNASSESSED')

if __name__=='__main__':unittest.main()
