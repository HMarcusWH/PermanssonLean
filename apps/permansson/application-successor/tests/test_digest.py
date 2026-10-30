"""Domain-separated RFC 8785 semantic/execution digests (new versioned profile).

Oracles are independent of the digest wrapper: the official JCS test vectors
(cyberphone/json-canonicalization, vendored with provenance), the separate
restricted encoder in `identity`, and hand-written expected bytes.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys
import unittest
from unittest import mock

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
import rfc8785
from permansson_app import digest, identity
from permansson_app.errors import AppError
from permansson_app.identity import rational_text
from permansson_app.strict_json import strict_loads

OFFICIAL=APP/'tests/fixtures/rfc8785_official'
VECTORS=APP/'tests/fixtures/semantic_digest_vectors.json'


class OfficialVectorTests(unittest.TestCase):
    def test_vendored_vectors_match_recorded_provenance(self):
        provenance=json.loads((OFFICIAL/'PROVENANCE.json').read_text())
        self.assertEqual(provenance['license'],'Apache-2.0')
        self.assertRegex(provenance['commit'],r'^[0-9a-f]{40}$')
        files=sorted(p.relative_to(OFFICIAL).as_posix() for p in OFFICIAL.rglob('*.json')
                     if p.name!='PROVENANCE.json')
        self.assertEqual(files,sorted(provenance['sha256']))
        for name,expected in provenance['sha256'].items():
            self.assertEqual(sha256((OFFICIAL/name).read_bytes()).hexdigest(),expected,name)

    def test_pinned_library_reproduces_every_official_vector(self):
        names=sorted(p.stem for p in (OFFICIAL/'input').glob('*.json'))
        self.assertEqual(names,['arrays','french','structures','unicode','values','weird'])
        for name in names:
            with self.subTest(name=name):
                value=json.loads((OFFICIAL/'input'/f'{name}.json').read_bytes())
                self.assertEqual(rfc8785.dumps(value),(OFFICIAL/'output'/f'{name}.json').read_bytes())

    def test_restricted_profile_accepts_float_free_vectors_and_rejects_floats(self):
        for name in ('arrays','french','unicode','weird'):
            with self.subTest(name=name):
                value=json.loads((OFFICIAL/'input'/f'{name}.json').read_bytes())
                self.assertEqual(digest.canonical_semantics(value),
                                 (OFFICIAL/'output'/f'{name}.json').read_bytes())
        for name in ('structures','values'):
            with self.subTest(name=name),self.assertRaises(AppError):
                digest.canonical_semantics(json.loads((OFFICIAL/'input'/f'{name}.json').read_bytes()))


class ProfileTests(unittest.TestCase):
    def test_utf16_key_order_differs_from_code_point_order(self):
        value={'\ufb33':'dalet','\U0001F600':'grinning','\r':'cr','1':'one'}
        # UTF-16 code units: \r(000D) < 1(0031) < D83D(emoji) < FB33.
        expected='{"\\r":"cr","1":"one","\U0001F600":"grinning","\ufb33":"dalet"}'.encode('utf-8')
        self.assertEqual(digest.canonical_semantics(value),expected)
        self.assertNotEqual(json.dumps(value,sort_keys=True,ensure_ascii=False,
                                       separators=(',',':')).encode('utf-8'),expected)

    def test_escaping_and_literals(self):
        value={'s':'\u20ac$\u000f\nA\'B"\\/','l':[None,True,False],'n':[0,-7,9007199254740991]}
        expected=('{"l":[null,true,false],"n":[0,-7,9007199254740991],'
                  '"s":"\u20ac$\\u000f\\nA\'B\\"\\\\/"}').encode('utf-8')
        self.assertEqual(digest.canonical_semantics(value),expected)

    def test_raw_whitespace_changes_raw_hash_not_semantics(self):
        compact=b'{"mode":"retryable","alpha":["1/2","1/2"]}'
        spaced=b'{\n  "alpha" : [ "1/2", "1/2" ],\n  "mode": "retryable"\n}\n'
        self.assertNotEqual(sha256(compact).digest(),sha256(spaced).digest())
        self.assertEqual(digest.semantic_digest(strict_loads(compact)),
                         digest.semantic_digest(strict_loads(spaced)))

    def test_rationals_normalize_before_encoding_never_implicitly(self):
        self.assertEqual(rational_text(Fraction(2,4)),rational_text(Fraction(1,2)))
        normalized=digest.semantic_digest({'p':rational_text(Fraction(2,4))})
        self.assertEqual(normalized,digest.semantic_digest({'p':'1/2'}))
        self.assertNotEqual(digest.semantic_digest({'p':'2/4'}),normalized)

    def test_meaningful_semantic_changes_alter_digest(self):
        base={'mode':'retryable','alpha':['1/2','1/2'],'comparison':['a','b'],
              'information':'fully_observed','nature_order':['committed','rectangular']}
        reference=digest.semantic_digest(base)
        for key,value in (('mode','first_entry'),('alpha',['1/3','2/3']),('comparison',['b','a']),
                          ('information','one_step_observation'),('nature_order',['rectangular','committed'])):
            with self.subTest(key=key):
                self.assertNotEqual(digest.semantic_digest(dict(base,**{key:value})),reference)

    def test_rejections_are_structured_errors(self):
        for bad in (0.5,2**53,{'k':'\ud800'},{1:'x'},Fraction(1,2),{'s':{1,2}},float('nan')):
            with self.subTest(bad=bad),self.assertRaises(AppError):
                digest.semantic_digest(bad)

    def test_encoder_disagreement_never_issues_a_digest(self):
        with mock.patch.object(rfc8785,'dumps',return_value=b'{"x":1}'):
            with self.assertRaises(AppError) as raised:
                digest.semantic_digest({'x':2})
        self.assertEqual(raised.exception.code,'DIGEST_IMPLEMENTATION_DISAGREEMENT')

    def test_missing_canonicalizer_fails_without_substitution(self):
        with mock.patch.object(digest.importlib,'import_module',side_effect=ImportError('absent')):
            with self.assertRaises(AppError) as raised:
                digest.semantic_digest({'x':'1'})
        self.assertEqual(raised.exception.code,'DIGEST_DEPENDENCY_MISSING')

    def test_domain_separation(self):
        value={'x':'1/2'}
        canonical=digest.canonical_semantics(value)
        self.assertEqual(digest.semantic_digest(value),
                         sha256(b'PERMANSSON_APP_SEMANTICS_JCS_V1\x00'+canonical).hexdigest())
        self.assertNotEqual(digest.semantic_digest(value),sha256(canonical).hexdigest())

    def test_execution_digest_binds_every_identity(self):
        execution={'semantic_digest':digest.semantic_digest({'x':'1'}),'wrapper':'w1','registry':'r1',
                   'provider':'p1','runtime':'cpython-3.13','mode':'numeric','resource_profile':'default'}
        reference=digest.execution_digest(execution)
        self.assertEqual(reference,sha256(b'PERMANSSON_APP_EXECUTION_JCS_V1\x00'
                                          +digest.canonical_semantics(execution)).hexdigest())
        for key in sorted(execution):
            changed=dict(execution,**{key:'0'*64 if key=='semantic_digest' else 'other'})
            with self.subTest(key=key):
                self.assertNotEqual(digest.execution_digest(changed),reference)
        for bad in ({k:v for k,v in execution.items() if k!='mode'},dict(execution,extra='x'),
                    dict(execution,semantic_digest='ABC'),dict(execution,semantic_digest='0'*63)):
            with self.subTest(bad=bad),self.assertRaises(AppError):
                digest.execution_digest(bad)

    def test_historical_profile_is_untouched(self):
        self.assertEqual(identity.PROFILE,'Permansson.App.TypedRationalJCS.v1')
        self.assertNotEqual(digest.PROFILE,identity.PROFILE)
        self.assertEqual(identity.semantic_identity('k',{'x':'1/2'}),
                         {'profile':identity.PROFILE,'sha256':sha256(
                             b'{"kind":"k","payload":{"x":"1/2"},"profile":"Permansson.App.TypedRationalJCS.v1"}'
                         ).hexdigest()})


class PublishedVectorTests(unittest.TestCase):
    def test_published_semantic_vectors(self):
        data=json.loads(VECTORS.read_text(encoding='utf-8'))
        self.assertEqual(data['profile'],digest.PROFILE)
        self.assertGreaterEqual(len(data['accept']),5)
        for case in data['accept']:
            with self.subTest(case=case['name']):
                canonical=bytes.fromhex(case['canonical_utf8_hex'])
                self.assertEqual(identity.canonical_bytes(case['value']),canonical)
                self.assertEqual(rfc8785.dumps(case['value']),canonical)
                self.assertEqual(sha256(canonical).hexdigest(),case['canonical_sha256'])
                self.assertEqual(digest.semantic_digest(case['value']),case['semantic_digest'])
        for case in data['reject']:
            with self.subTest(case=case['name']),self.assertRaises(AppError):
                digest.semantic_digest(json.loads(case['json'],parse_constant=float)
                                       if 'json' in case else int(case['integer']))


if __name__=='__main__':
    unittest.main()
