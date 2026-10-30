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


if __name__=='__main__':
    unittest.main()
