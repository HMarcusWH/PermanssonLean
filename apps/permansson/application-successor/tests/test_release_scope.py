"""Release scopes: the default C10/C11 policy and the 26-profile successor policy.

The packaged default `acceptance_policy.json` still selects only the native
C10/C11 capabilities; a target naming an additive profile is blocked against
it as undeclared. The owner-selected successor scope is a separate, versioned
policy (`acceptance_policy.successor_numeric.v1.json`, format v3) for exactly
the 26 exact profiles, numeric only, on Linux CPython 3.12 and 3.13, naming the
real test-method IDs each capability needs. Its release authority is an
owner-engineering policy: the owner's activation is required and no
independent security review is claimed. No policy and no assessment authorizes
a release, a scientific claim or an identification on its own.
"""
from __future__ import annotations
import json
from pathlib import Path
import sys
import unittest

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.acceptance import AcceptancePolicy,AcceptanceTarget,assess_acceptance
from permansson_app.capabilities import registry
from permansson_app.evidence import EvidenceSet,record_digest

NATIVE={'c10.fixed_six_state.numeric.v1','c11.stationary_1_to_6.numeric.v1'}
POLICY=APP/'src/permansson_app/data/acceptance_policy.json'


def target(capabilities):
    return AcceptanceTarget.parse({
        'source':{'repository':'HMarcusWH/PermanssonLean','commit':'a'*40,'tree':'b'*40,
                  'application':'successor.0.2','research':'research.0.2','paper':'0.1.8'},
        'subject_sha256':'c'*64,'wheel_sha256':'d'*64,'sdist_sha256':'e'*64,
        'capabilities':list(capabilities),'platforms':['linux'],'execution_profile':'numeric'})


class ReleaseScopeTests(unittest.TestCase):
    def setUp(self):
        self.raw=json.loads(POLICY.read_text(encoding='utf-8'))
        self.policy=AcceptancePolicy.parse(self.raw)

    def test_policy_selects_exactly_the_native_capabilities(self):
        self.assertEqual(set(self.policy.required),NATIVE)
        self.assertEqual(set(registry()['capabilities']),NATIVE)
        self.assertTrue(self.policy.require_security_review)
        self.assertTrue(self.policy.require_owner_activation)

    def test_no_additive_profile_is_a_release_capability(self):
        profiles=set(registry()['exact_profiles'])
        self.assertEqual(len(profiles),26)
        self.assertFalse(profiles&set(self.policy.required))

    def test_target_with_an_additive_profile_is_blocked(self):
        empty=EvidenceSet.from_external_hashes([],trusted_expected_digests={})
        for name in sorted(registry()['exact_profiles']):
            with self.subTest(profile=name):
                result=assess_acceptance(target([name]),empty,self.policy).to_dict()
                self.assertEqual(result['status'],'BLOCKED_MISSING_EVIDENCE')
                self.assertIn('capability-not-declared:'+name,result['missing'])
                self.assertIs(result['authorized_release'],False)
                self.assertIs(result['scientific_claims_verified'],False)
                self.assertIs(result['empirical_identification'],False)

    def test_review_flags_cannot_be_dropped_silently(self):
        for flag in ('security_review_required','owner_activation_required'):
            changed={**self.raw,flag:'false'}
            with self.subTest(flag=flag),self.assertRaises(Exception):
                AcceptancePolicy.parse(changed)
        # Even a complete evidence set leaves the external review and activation missing.
        result=assess_acceptance(target(sorted(NATIVE)),EvidenceSet.from_external_hashes([],trusted_expected_digests={}),
                                 self.policy).to_dict()
        self.assertIn('EXTERNAL_INDEPENDENT_SECURITY_REVIEW',result['missing'])
        self.assertIn('EXTERNAL_OWNER_RELEASE_ACTIVATION',result['missing'])


SUCCESSOR=APP/'src/permansson_app/data/acceptance_policy.successor_numeric.v1.json'
PLATFORMS=['linux-cpython-3.12','linux-cpython-3.13']


def discovered(selectors):
    import unittest as ut
    sys.path.insert(0,str(APP/'tests'))
    try:
        found=[]
        def walk(node):
            if isinstance(node,ut.TestSuite):
                for child in node:
                    walk(child)
            else:
                found.append(node.id())
        for selector in selectors:
            walk(ut.TestLoader().loadTestsFromName(selector))
        return found
    finally:
        sys.path.remove(str(APP/'tests'))


class SuccessorPolicyTests(unittest.TestCase):
    def setUp(self):
        self.raw=json.loads(SUCCESSOR.read_text(encoding='utf-8'))
        self.policy=AcceptancePolicy.parse(self.raw)

    def test_scope_platforms_and_profile(self):
        self.assertEqual(self.policy.scope,'successor-finite-numeric.v1')
        self.assertEqual(set(self.policy.required),set(registry()['exact_profiles']))
        self.assertFalse(set(self.policy.required)&NATIVE)
        self.assertEqual(list(self.policy.platforms),PLATFORMS)
        self.assertEqual(self.policy.execution_profile,'numeric')
        self.assertIn('lean_status=NOT_EXECUTED',self.raw['description'])

    def test_release_authority_is_owner_engineering_without_an_independent_review_claim(self):
        authority=self.policy.release_authority
        self.assertEqual((authority.kind,authority.owner),('OWNER_ENGINEERING_POLICY','HMarcusWH'))
        self.assertIs(authority.independent_security_review,False)
        self.assertIn('application-release.yml',authority.activation)
        self.assertFalse(self.policy.require_security_review)
        self.assertTrue(self.policy.require_owner_activation)
        self.assertIn('no independent security review is claimed',self.raw['description'])

    def test_every_capability_names_exactly_its_real_test_methods(self):
        budget=set(discovered(['test_resources_budget','test_engine_resource_limits']))
        sys.path.insert(0,str(APP/'scripts'))
        try:
            import end_to_end
        finally:
            sys.path.remove(str(APP/'scripts'))
        # Real walkthrough rows (lp-check runs inside the lp-propose row).
        commands={row[0] for row in end_to_end.PROFILES}
        for cap,kinds in self.policy.required.items():
            with self.subTest(capability=cap):
                self.assertEqual(set(kinds),{'numeric_test','cross_platform','source_build','package'})
                methods=discovered(self.raw['method_sources'][cap])
                self.assertTrue(methods)
                self.assertFalse([m for m in methods if 'FailedTest' in m or 'LoadTest' in m])
                walkthrough={m for m in kinds['numeric_test'] if m.startswith('scripts/end_to_end.py:')}
                self.assertEqual(len(walkthrough),1)
                self.assertIn(next(iter(walkthrough)).split(':',1)[1],commands)
                self.assertEqual(set(kinds['numeric_test']),set(methods)|budget|walkthrough)
                self.assertEqual(kinds['package'],('wheel-and-sdist',))

    def evidence(self,cap,platform,kinds=None,status='PASS'):
        records=[]
        for kind,methods in (kinds or self.policy.required[cap]).items():
            records.append({'format':'Permansson.App.EvidenceRecord.v1','evidence_id':f'{kind}-{platform}',
                            'kind':kind,'subject_sha256':'c'*64,'source_commit':'a'*40,'source_tree':'b'*40,
                            'capability':cap,'execution_profile':'numeric','platform':platform,
                            'method_ids':list(methods),'status':status,
                            'artifact_sha256':'d'*64 if kind!='package' else 'e'*64,
                            'producer':'github-actions','reviewer':None})
        records.append(dict(records[-1],evidence_id=f'package2-{platform}',artifact_sha256='d'*64))
        return EvidenceSet.from_external_hashes(records,trusted_expected_digests={
            r['evidence_id']:record_digest(r) for r in records})

    def target_for(self,cap,platform,profile='numeric'):
        return AcceptanceTarget.parse({
            'source':{'repository':'HMarcusWH/PermanssonLean','commit':'a'*40,'tree':'b'*40,
                      'application':'successor.0.2','research':'research.0.2','paper':'0.1.8'},
            'subject_sha256':'c'*64,'wheel_sha256':'d'*64,'sdist_sha256':'e'*64,
            'capabilities':[cap],'platforms':[platform],'execution_profile':profile})

    def test_complete_evidence_covers_a_capability_but_authorizes_nothing(self):
        cap='finite.private_control_stage_saddle.numeric.v1'
        result=assess_acceptance(self.target_for(cap,PLATFORMS[1]),self.evidence(cap,PLATFORMS[1]),
                                 self.policy).to_dict()
        self.assertEqual(result['missing'],['EXTERNAL_OWNER_RELEASE_ACTIVATION'])
        self.assertEqual(result['failing'],[])
        self.assertTrue(result['covered'])
        self.assertIs(result['authorized_release'],False)
        # One missing method makes the capability incomplete.
        kinds=dict(self.policy.required[cap])
        kinds['numeric_test']=kinds['numeric_test'][1:]
        partial=assess_acceptance(self.target_for(cap,PLATFORMS[1]),self.evidence(cap,PLATFORMS[1],kinds),
                                  self.policy).to_dict()
        self.assertTrue(any(m.endswith(self.policy.required[cap]['numeric_test'][0]) for m in partial['missing']))

    def test_unselected_platform_profile_or_capability_is_never_covered(self):
        cap='finite.private_control_stage_saddle.numeric.v1'
        for target,expected in (
                (self.target_for(cap,'windows-cpython-3.13'),'platform-not-selected:windows-cpython-3.13'),
                (self.target_for(cap,'linux-cpython-3.11'),'platform-not-selected:linux-cpython-3.11'),
                (self.target_for(cap,PLATFORMS[0],'lean_replay'),'execution-profile-not-selected:lean_replay'),
                (self.target_for('c10.fixed_six_state.numeric.v1',PLATFORMS[0]),
                 'capability-not-declared:c10.fixed_six_state.numeric.v1')):
            with self.subTest(expected=expected):
                result=assess_acceptance(target,EvidenceSet.from_external_hashes([],trusted_expected_digests={}),
                                         self.policy).to_dict()
                self.assertIn(expected,result['missing'])
                self.assertIs(result['authorized_release'],False)

    def test_malformed_v2_policies_are_rejected(self):
        mutations={
            'no method sources':lambda p:p.pop('method_sources'),
            'sources for another set':lambda p:p['method_sources'].pop(next(iter(p['method_sources']))),
            'empty platforms':lambda p:p.update(platforms=[]),
            'duplicate platform':lambda p:p.update(platforms=PLATFORMS+PLATFORMS[:1]),
            'unknown profile':lambda p:p.update(execution_profile='certified'),
            'v1 tag with v2 fields':lambda p:p.update(format='Permansson.App.AcceptancePolicy.v1'),
            'review flag not a boolean':lambda p:p.update(security_review_required='false'),
            'owner activation dropped':lambda p:p.update(owner_activation_required=False),
            'independent review claimed':lambda p:p['release_authority'].update(independent_security_review=True),
            'review required under owner policy':lambda p:p.update(security_review_required=True),
            'unknown authority kind':lambda p:p['release_authority'].update(kind='INDEPENDENT_REVIEW'),
            'owner is not a login':lambda p:p['release_authority'].update(owner='HMarcusWH; anyone'),
            'activation not stated':lambda p:p['release_authority'].update(activation=''),
            'authority missing':lambda p:p.pop('release_authority'),
            'v2 tag with an authority':lambda p:p.update(format='Permansson.App.AcceptancePolicy.v2'),
        }
        for name,mutate in mutations.items():
            raw=json.loads(SUCCESSOR.read_text(encoding='utf-8'))
            mutate(raw)
            with self.subTest(name),self.assertRaises(Exception):
                AcceptancePolicy.parse(raw)


if __name__=='__main__':
    unittest.main()
