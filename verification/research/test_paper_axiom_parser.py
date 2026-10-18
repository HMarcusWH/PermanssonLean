"""The verbose signature audit must preserve actual axiom identities."""
import unittest

from paper_closure_analytic_audit import ALLOW, axiom_names


class AxiomParserTests(unittest.TestCase):
    def test_universe_annotations_preserve_standard_constants(self):
        self.assertEqual(set(axiom_names(
            'propext, Classical.choice.{u}, Quot.sound.{u_1}')), ALLOW)

    def test_forbidden_polymorphic_axiom_still_rejected(self):
        found = set(axiom_names('Classical.choice.{u}, sorryAx.{u_1, u_2}'))
        self.assertEqual(found - ALLOW, {'sorryAx'})

    def test_unknown_identifier_is_not_normalized_to_allowed_prefix(self):
        found = set(axiom_names('Classical.choiceUnsafe.{u}, propext'))
        self.assertEqual(found - ALLOW, {'Classical.choiceUnsafe'})
