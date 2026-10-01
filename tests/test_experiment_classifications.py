"""Suggestions must not change build facts, leak between campaigns or outlive evidence."""

import io
from contextlib import closing
from pathlib import Path
import tempfile
import unittest
from unittest.mock import MagicMock, patch

from experiment import classifications as c, nix
from experiment.controller import Controller
from experiment.model import connect, encode, identity, import_campaign

A = "/nix/store/" + "a" * 32 + "-library.drv"
B = "/nix/store/" + "b" * 32 + "-program.drv"


class ClassificationTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.state = Path(self.tmp.name)
        self.db = connect(self.state)
        self.addCleanup(self.db.close)
        self.cid = import_campaign(
            self.db,
            "one",
            {"attrPaths": [["alpha"], ["alias"], ["beta"]]},
            "/nix/store/source",
            "abc",
            nix.DEFAULT_POLICY,
            "test",
        )
        self.other = import_campaign(
            self.db,
            "two",
            {"attrPaths": [["alpha"]]},
            "/nix/store/source",
            "abc",
            nix.DEFAULT_POLICY,
            "test",
        )
        for drv in (A, B):
            self.db.execute(
                "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,'{}')", (drv, drv)
            )
        self.db.execute(
            "UPDATE candidates SET drv=?,recipe='{}',state='queued' WHERE id IN (1,2,4)",
            (A,),
        )
        self.db.execute(
            "UPDATE candidates SET drv=?,recipe='{}',state='blocked' WHERE id=3", (B,)
        )
        self.db.execute("INSERT INTO edges VALUES(?,?,'[]')", (B, A))
        self.db.commit()
        self.controller = Controller(self.db, self.state)

    def item(self, candidate=1, kind="package", provider="jev"):
        row = next(r for r in c.candidates(self.db, self.cid) if r["id"] == candidate)
        evidence = {"target": row["label"], "fact": "a visible example"}
        probabilities = dict.fromkeys(c.DEFINITIONS[kind], 0.01)
        probabilities[next(iter(probabilities))] = 0.92
        return {
            "candidate": candidate,
            "kind": kind,
            "subject": row["label"],
            "provider": provider,
            "model": c.MODELS[provider],
            "question_version": c.QUESTION_VERSION,
            "source_hash": identity(c.source_fields(row, kind)),
            "evidence_hash": identity(evidence),
            "evidence": evidence,
            "probabilities": probabilities,
        }

    def save(self, item):
        return self.controller.dispatch(
            {"op": "classification-import", "campaign": self.cid, "item": item}
        )

    def test_providers_and_aliases_are_preserved_without_changing_facts(self):
        tables = (
            "campaigns",
            "candidates",
            "derivations",
            "edges",
            "roles",
            "attempts",
            "tests",
        )
        before = {
            t: [tuple(r) for r in self.db.execute("SELECT * FROM " + t)] for t in tables
        }
        for candidate, provider in ((1, "jev"), (1, "openai"), (2, "jev")):
            self.save(self.item(candidate, provider=provider))
        result = c.classification_index(self.db, self.cid)
        self.assertEqual({a["provider"] for a in result[1]}, {"jev", "openai"})
        self.assertEqual(len(result[2]), 1)
        self.assertEqual(result[1][0]["probabilities"]["Application"], 0.92)
        self.assertNotIn("evidence", result[1][0])
        self.assertEqual(
            c.annotations(self.db, self.cid, 1)[0]["evidence"],
            {"target": "alpha", "fact": "a visible example"},
        )
        self.assertEqual(c.classification_index(self.db, self.other), {})
        self.assertEqual(c.annotations(self.db, self.cid, 4), [])
        self.assertEqual(
            before,
            {
                t: [tuple(r) for r in self.db.execute("SELECT * FROM " + t)]
                for t in tables
            },
        )

    def test_recipe_race_discards_results_and_hides_previous_annotations(self):
        item = self.item()
        self.save(item)
        self.db.execute(
            "UPDATE candidates SET recipe=? WHERE id=1", (encode({"revision": "new"}),)
        )
        self.db.commit()
        self.assertEqual(self.save(item), "stale evidence discarded")
        self.assertEqual(c.annotations(self.db, self.cid, 1), [])
        with self.assertRaises(ValueError):
            c.persist(self.db, self.other, item)

    def test_diagnostic_freshness_is_attempt_specific(self):
        self.db.execute(
            "UPDATE derivations SET failure='failed',evidence_attempt='old' WHERE drv=?",
            (A,),
        )
        self.db.commit()
        item = self.item(kind="diagnostic")
        self.save(item)
        self.db.execute(
            "UPDATE derivations SET evidence_attempt='new' WHERE drv=?", (A,)
        )
        self.db.commit()
        self.assertEqual(c.annotations(self.db, self.cid, 1), [])
        self.assertEqual(self.save(item), "stale evidence discarded")

    def test_disconnected_annotation_client_does_not_stop_controller_after_commit(self):
        server, client = MagicMock(), MagicMock()
        server.__enter__.return_value = server
        server.accept.return_value = (client, None)
        client.recv.return_value = (
            encode(
                {
                    "op": "classification-import",
                    "campaign": self.cid,
                    "item": self.item(),
                }
            )
            + "\n"
        ).encode()
        client.sendall.side_effect = BrokenPipeError
        with (
            patch("experiment.controller.socket.socket", return_value=server),
            patch("experiment.controller.os.chmod"),
            patch.object(
                self.controller, "tick", side_effect=[None, RuntimeError("next tick")]
            ) as tick,
        ):
            with self.assertRaisesRegex(RuntimeError, "next tick"):
                self.controller.serve()
            self.assertEqual(tick.call_count, 2)
        self.assertEqual(len(c.annotations(self.db, self.cid, 1)), 1)

    def test_malformed_or_misattributed_results_are_rejected(self):
        for value in (True, float("nan"), float("inf"), -0.1, 1.01, "0.9"):
            item = self.item()
            item["probabilities"]["Application"] = value
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.save(item)
        for field, value in (
            ("evidence_hash", "wrong"),
            ("model", "different"),
            ("question_version", "old"),
        ):
            item = self.item()
            item[field] = value
            with self.assertRaises(ValueError):
                self.save(item)
        self.assertEqual(c.annotations(self.db, self.cid, 1), [])

    def test_pre_migration_reads_are_empty_then_schema_five_migrates(self):
        self.db.execute("DROP TABLE classifications")
        self.db.execute("PRAGMA user_version=5")
        self.db.commit()
        self.assertEqual(c.classification_index(self.db, self.cid), {})
        with closing(connect(self.state)) as migrated:
            self.assertEqual(migrated.execute("PRAGMA user_version").fetchone()[0], 6)
            self.assertEqual(c.classification_index(migrated, self.cid), {})

    def test_log_context_cannot_pick_up_another_derivation_or_unowned_text(self):
        self.db.execute(
            "INSERT INTO attempts(id,campaign,kind,targets,state,created,spec) VALUES('attempt',?,'build','[]','finished',1,'{}')",
            (self.cid,),
        )
        folder = self.state / "attempts" / "attempt"
        folder.mkdir(parents=True)
        entries = [
            {"action": "start", "id": i, "type": 105, "fields": [drv]}
            for i, drv in ((1, A), (2, B))
        ]
        entries += [
            {"action": "result", "id": i, "type": 101, "fields": [text]}
            for i, text in (
                (2, "fatal: WRONG dependency"),
                (1, "context target"),
                (1, "error: missing RIGHT tool"),
                (2, "WRONG tail"),
                (1, "target final line"),
            )
        ]
        (folder / "stderr.log").write_text(
            "error: UNOWNED global line\n"
            + "\n".join("@nix " + encode(e) for e in entries)
        )
        self.db.commit()
        excerpt = c.diagnostic_excerpt(self.db, self.state, A, "attempt")
        self.assertIn("missing RIGHT tool", excerpt["text"])
        self.assertIn("context target", excerpt["text"])
        self.assertIn("target final line", excerpt["text"])
        self.assertNotIn("WRONG", excerpt["text"])
        self.assertNotIn("UNOWNED", excerpt["text"])
        self.assertTrue(excerpt["scan_complete"])
        self.db.execute("UPDATE attempts SET state='running' WHERE id='attempt'")
        self.assertEqual(
            c.diagnostic_excerpt(self.db, self.state, A, "attempt")["text"], ""
        )

    def test_worker_budget_and_cached_replay_do_not_repeat_paid_calls(self):
        answer = (
            self.item()["probabilities"],
            {"input_tokens": 10},
            {"response": "example"},
        )
        with (
            patch.object(c, "ask", return_value=answer) as ask,
            patch.object(c, "submit", side_effect=ConnectionError),
        ):
            with self.assertRaises(ConnectionError):
                c.run(self.state, self.cid, limit=1, labels=["alpha"])
            self.assertEqual(ask.call_count, 1)

        def submit(state, campaign, item):
            return c.persist(self.db, campaign, item)

        with (
            patch.object(c, "ask", side_effect=AssertionError("paid call repeated")),
            patch.object(c, "submit", side_effect=submit),
        ):
            self.assertEqual(
                c.run(self.state, self.cid, limit=1, labels=["alpha"]), {"requests": 0}
            )
            self.assertEqual(
                c.run(self.state, self.cid, limit=1, labels=["alpha"]), {"requests": 0}
            )
        self.assertEqual(len(c.annotations(self.db, self.cid, 1)), 1)
        self.assertEqual((self.state / "classifications").stat().st_mode & 0o777, 0o700)

    def test_unknown_delivery_reservation_prevents_automatic_retry(self):
        with (
            patch.object(c, "ask", side_effect=TimeoutError) as ask,
            patch.object(c, "submit") as submit,
        ):
            self.assertEqual(c.run(self.state, self.cid, limit=1), {"requests": 1})
            self.assertEqual(c.run(self.state, self.cid, limit=1), {"requests": 1})
            self.assertEqual(ask.call_count, 2)  # Two distinct targets, not a retry.
            self.assertEqual(submit.call_count, 0)
        with self.assertRaises(ValueError):
            c.run(self.state, self.cid, limit=0)
        with self.assertRaises(ValueError):
            c.run(self.state, self.cid, labels=["absent"])

    def test_provider_contracts_validate_real_output_shapes(self):
        probabilities = self.item()["probabilities"]
        response = {
            "model": "jev-1.13.0",
            "answers": {
                k: {"type": "noul", "noul": p} for k, p in probabilities.items()
            },
            "usage": {"input_tokens": 12},
        }
        with (
            patch.dict("os.environ", {"TYPESAFE_API_KEY": "not-a-secret"}),
            patch(
                "urllib.request.urlopen",
                return_value=io.BytesIO(encode(response).encode()),
            ),
        ):
            self.assertEqual(c.ask("jev", "package", {})[0], probabilities)
        response = {
            "status": "completed",
            "model": "gpt-6-luna",
            "output": [
                {
                    "type": "message",
                    "phase": "commentary",
                    "content": [{"type": "output_text", "text": "An irrelevant draft"}],
                },
                {
                    "type": "message",
                    "phase": "final_answer",
                    "content": [{"type": "output_text", "text": encode(probabilities)}],
                },
            ],
        }
        with (
            patch.dict("os.environ", {"OPENAI_API_KEY": "not-a-secret"}),
            patch(
                "urllib.request.urlopen",
                return_value=io.BytesIO(encode(response).encode()),
            ),
        ):
            self.assertEqual(c.ask("openai", "package", {})[0], probabilities)
        response["output"] = response["output"][:1]
        with (
            patch.dict("os.environ", {"OPENAI_API_KEY": "not-a-secret"}),
            patch(
                "urllib.request.urlopen",
                return_value=io.BytesIO(encode(response).encode()),
            ),
        ):
            with self.assertRaises(ValueError):
                c.ask("openai", "package", {})

    def test_luna_refusal_incomplete_and_ambiguous_final_are_not_importable(self):
        message = {
            "type": "message",
            "phase": "final_answer",
            "content": [
                {"type": "output_text", "text": encode(self.item()["probabilities"])}
            ],
        }
        responses = (
            {
                "status": "incomplete",
                "model": "gpt-6-luna",
                "output": [message],
                "incomplete_details": {"reason": "max_output_tokens"},
            },
            {
                "status": "completed",
                "model": "gpt-6-luna",
                "output": [
                    {
                        "type": "message",
                        "phase": "final_answer",
                        "content": [{"type": "refusal", "refusal": "Not classified"}],
                    }
                ],
            },
            {
                "status": "completed",
                "model": "gpt-6-luna",
                "output": [message, message],
            },
        )
        for response in responses:
            with (
                self.subTest(response=response),
                patch.dict("os.environ", {"OPENAI_API_KEY": "not-a-secret"}),
                patch(
                    "urllib.request.urlopen",
                    return_value=io.BytesIO(encode(response).encode()),
                ),
            ):
                with self.assertRaises(ValueError):
                    c.ask("openai", "package", {})
        # Older Responses messages may legitimately omit phase.
        message.pop("phase")
        response = {"status": "completed", "model": "gpt-6-luna", "output": [message]}
        with (
            patch.dict("os.environ", {"OPENAI_API_KEY": "not-a-secret"}),
            patch(
                "urllib.request.urlopen",
                return_value=io.BytesIO(encode(response).encode()),
            ),
        ):
            self.assertEqual(c.ask("openai", "package", {})[0]["Application"], 0.92)
