"""Keep fatal Nix errors distinct from startup warnings and trace context."""

import unittest

from experiment.diagnostics import evaluation_summary


class DiagnosticTests(unittest.TestCase):
    def test_refusal_after_warning_and_trace(self):
        message = """GC Warning: Failed to expand heap by 4194304 KiB
error:
       … while evaluating attribute 'drv'
         at /nix/store/worker/planner.nix:14:3:
       (stack trace truncated; use '--show-trace' to show the full, detailed trace)

       error: Package ‘gnutls-3.8.9’ in /nix/store/source/pkgs/gnutls/default.nix:250 is marked as broken, refusing to evaluate.

       a) To temporarily allow broken packages, you can use an environment variable
"""
        self.assertEqual(
            evaluation_summary(message),
            "Package ‘gnutls-3.8.9’ is marked as broken, refusing to evaluate.",
        )

    def test_nested_errors_and_multiline_fatal_diagnostic(self):
        message = """error: evaluation aborted
       … while calling a function
       error: assertion failed:
         expected compiler == host compiler

       Extra trace context
"""
        self.assertEqual(
            evaluation_summary(message),
            "assertion failed:\n         expected compiler == host compiler",
        )

    def test_real_memory_failures_and_warning_only_are_not_hidden(self):
        warning = "GC Warning: Failed to expand heap by 4194304 KiB"
        self.assertEqual(evaluation_summary(warning), warning)
        self.assertEqual(
            evaluation_summary(warning + "\nerror: out of memory"), "out of memory"
        )
        self.assertEqual(evaluation_summary(None), "")
        self.assertEqual(evaluation_summary("x" * 1000), "x" * 500)

    def test_ansi_and_inline_error_text(self):
        self.assertEqual(
            evaluation_summary("\x1b[31merror:\x1b[0m message contains error: text"),
            "message contains error: text",
        )
