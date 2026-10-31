"""The packaged release policy selects only the native C10/C11 capabilities.

The 26 additive exact profiles are not release capabilities until an owner
authorizes a scope with an evidence matrix (ROADMAP, CON-03). An acceptance
target that names one is blocked as undeclared, and no assessment authorizes
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
from permansson_app.evidence import EvidenceSet

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


if __name__=='__main__':
    unittest.main()
