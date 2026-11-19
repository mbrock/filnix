#!/usr/bin/env python3
"""Test the source transformation and its treatment of section variables."""
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from rocq_interface import interface  # noqa: E402


class Interface(unittest.TestCase):
    def test_qed_outside_a_section_is_replaced(self):
        text, replaced, kept = interface(
            "Lemma a : True.\nProof. exact I. Qed.\nDefinition d := 1.\n"
        )
        self.assertEqual((replaced, kept), (1, 0))
        self.assertIn("Lemma a : True.", text)
        self.assertIn("Admitted.", text)
        self.assertNotIn("exact I", text)
        self.assertIn("Definition d := 1.", text)

    def test_defined_and_abort_are_kept(self):
        src = "Definition f : nat.\nProof. exact 0. Defined.\nGoal True.\nProof. Abort.\n"
        text, replaced, kept = interface(src)
        self.assertEqual((replaced, kept), (0, 2))
        self.assertIn("exact 0. Defined.", text)

    def test_section_proof_without_using_is_kept(self):
        src = (
            "Section S.\nVariable n : nat.\nHypothesis H : n = 0.\n"
            "Lemma a : True.\nProof. clear H. exact I. Qed.\n"
            "Lemma b : n = 0.\nProof using H. exact H. Qed.\nEnd S.\n"
            "Lemma c : True.\nProof. exact I. Qed.\n"
        )
        text, replaced, kept = interface(src)
        self.assertEqual((replaced, kept), (2, 1))
        self.assertIn("clear H. exact I. Qed.", text)
        # The clause stays, so the lemma keeps the same section variables.
        self.assertIn("Proof using H.\nAdmitted.", text)
        self.assertNotIn("exact H", text)

    def test_module_end_does_not_close_a_section(self):
        src = (
            "Section S.\nModule M.\nLemma a : True.\nProof. exact I. Qed.\nEnd M.\n"
            "Lemma b : True.\nProof. exact I. Qed.\nEnd S.\n"
        )
        self.assertEqual(interface(src)[1:], (0, 2))

    def test_module_with_body_opens_no_scope(self):
        src = "Module R : T := I.\nSection S.\nEnd S.\nLemma a : True.\nProof. exact I. Qed.\n"
        self.assertEqual(interface(src)[1:], (1, 0))

    def test_comments_strings_and_dots(self):
        src = (
            '(* a (* nested *) comment with Qed. *)\n'
            'Notation "x .. y" := (pair x y) (at level 10).\n'
            'Lemma a : True.\nProof. idtac "a. Qed. b". (* Qed. *) exact I.\n- idtac. Qed.\n'
            "Lemma b : True.\nProof. exact I. Qed.\n"
        )
        text, replaced, kept = interface(src)
        self.assertEqual((replaced, kept), (2, 0))
        self.assertNotIn("comment", text)
        self.assertIn('"x .. y"', text)
        self.assertEqual(text.count("Admitted."), 2)
        self.assertIn("Lemma b : True.", text)

    def test_comment_and_proof_edits_leave_the_interface(self):
        a = "(* one *)\nLemma a : True.\nProof. exact I. Qed.\nLemma b : True.\nProof. auto. Qed.\n"
        b = "(* two, longer *)\nLemma a : True.\nProof. constructor. Qed.\nLemma b : True.\nProof. auto. Qed.\n"
        self.assertEqual(interface(a)[0], interface(b)[0])

    def test_statement_edit_changes_the_interface(self):
        a = "Lemma a : True.\nProof. exact I. Qed.\n"
        b = "Lemma a : True /\\ True.\nProof. split; exact I. Qed.\n"
        self.assertNotEqual(interface(a)[0], interface(b)[0])

    def test_ellipsis_ends_a_sentence(self):
        src = "Lemma a : True.\nProof with auto. idtac... Qed.\nLemma b : True.\nProof. exact I. Qed.\n"
        self.assertEqual(interface(src)[1:], (2, 0))

    def test_proof_term_is_kept(self):
        src = "Lemma a : True.\nProof I.\nLemma b : True.\nProof. exact I. Qed.\n"
        text, replaced, kept = interface(src)
        self.assertEqual((replaced, kept), (1, 0))
        self.assertIn("Proof I.", text)


if __name__ == "__main__":
    unittest.main()
