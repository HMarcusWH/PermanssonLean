"""The documentation index and capability table stay in step with the code.

Every registered exact profile, its command and every Lean candidate family
appear in CAPABILITY_SCOPES.md, and every relative Markdown link in docs/
resolves to a file that exists.
"""
from __future__ import annotations
from pathlib import Path
import re
import sys
import unittest

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.capabilities import registry
from permansson_app.proof.lean_candidates import families

DOCS=APP/'docs'
REPO=APP.parents[2]

# Statements that were true of earlier rounds and are now false. They must not
# come back into any current document (QA-01, DOC-08).
STALE=('no lean bridge has been compiled','no new lean correspondence theorem',
       'without** a new application-to-lean','without a new application-to-lean',
       'no lean replay or certified','no current-source pinned-lean compilation',
       'pending: a genuine `permanssonresearch/applicationbridge/`','lean correspondence proof, independent',
       'no data-to-lean proof replay','finite lp correspondence to canonical lean theorems remains unsupported',
       'proof correspondence to canonical lean statements is still unimplemented',
       'no lean correspondence module','pinned lean replay have not been qualified',
       'lean correspondence for the other numeric profiles','numeric-only permansson c10/c11',
       'does **not** implement the 19-engine / 17-lean-bridge')


class DocsRegistryTests(unittest.TestCase):
    def test_capability_scopes_lists_every_profile_command_and_family(self):
        text=(DOCS/'CAPABILITY_SCOPES.md').read_text(encoding='utf-8')
        data=registry()
        for name,entry in data['exact_profiles'].items():
            with self.subTest(profile=name):
                row=next((line for line in text.splitlines() if line.startswith(f'| `{name}` |')),None)
                self.assertIsNotNone(row,name)
                self.assertIn(f"`{entry['cli']}`",row)
                self.assertIn(entry['checker'].replace('permansson_app.',''),row)
        for name in data['capabilities']:
            self.assertIn(f'`{name}`',text)
        for family in families():
            with self.subTest(family=family):
                self.assertIn(f'`{family}` ([doc]',text)

    def test_every_doc_is_indexed_and_relative_links_resolve(self):
        index=(DOCS/'README.md').read_text(encoding='utf-8')
        for doc in sorted(DOCS.glob('*.md')):
            if doc.name!='README.md':
                self.assertIn(f'({doc.name})',index,doc.name)
        for doc in sorted(DOCS.glob('*.md')):
            for target in re.findall(r'\]\(([^)#:]+\.md)\)',doc.read_text(encoding='utf-8')):
                with self.subTest(doc=doc.name,target=target):
                    self.assertTrue((doc.parent/target).is_file())

    def test_retracted_status_statements_do_not_return(self):
        for doc in [APP/'README.md',*sorted(DOCS.glob('*.md'))]:
            text=' '.join(doc.read_text(encoding='utf-8').lower().split())
            for phrase in STALE:
                with self.subTest(doc=doc.name,phrase=phrase):
                    self.assertNotIn(phrase,text)

    def test_every_profile_appears_in_the_acceptance_status(self):
        text=(DOCS/'ACCEPTANCE_STATUS.md').read_text(encoding='utf-8')
        for name in registry()['exact_profiles']:
            base=name.removesuffix('.numeric.v1').removesuffix('.v1')
            with self.subTest(profile=name):
                self.assertIn(f'`{base}`',text)

    @unittest.skipUnless((REPO/'PermanssonResearch/ApplicationBridge').is_dir(),'needs the repository checkout')
    def test_every_bridge_module_is_documented(self):
        corpus=' '.join(doc.read_text(encoding='utf-8') for doc in DOCS.glob('*.md'))
        for module in sorted((REPO/'PermanssonResearch/ApplicationBridge').glob('*.lean')):
            with self.subTest(module=module.stem):
                self.assertIn(f'`{module.stem}`',corpus)


if __name__=='__main__':
    unittest.main()
