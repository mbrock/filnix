"""HTML representation, isolation and byte-reader contracts."""

import unittest

import test_experiment as fixtures
from bs4 import BeautifulSoup
from starlette.testclient import TestClient
from test_experiment import A

from experiment import nix
from experiment.dashboard.app import create_app
from experiment.model import import_campaign


class DashboardTests(unittest.TestCase):
    sql = fixtures.ExperimentTests.sql
    attempt = fixtures.ExperimentTests.attempt
    folder = fixtures.ExperimentTests.folder
    graph = fixtures.ExperimentTests.graph
    log = fixtures.ExperimentTests.log
    tearDown = fixtures.ExperimentTests.tearDown

    def setUp(self):
        fixtures.ExperimentTests.setUp(self)
        self.client = TestClient(create_app(self.state))
        self.prefix = "/campaigns/" + self.cid

    def get(self, suffix, **kwargs):
        return self.client.get(self.prefix + suffix, **kwargs)

    def test_full_inventory_stable_html_and_conditional_get(self):
        response = self.get("/packages?state=all")
        self.assertEqual(response.status_code, 200)
        soup = BeautifulSoup(response.text, "html.parser")
        self.assertEqual(len(soup.select("#package-list tbody tr")), 3)
        self.assertNotIn("<script>bad</script>", response.text)
        self.assertIn("&lt;script&gt;bad&lt;/script&gt;", response.text)
        self.assertTrue(response.headers["etag"].startswith('W/"'))
        self.assertEqual(
            self.get("/packages?state=all", headers={"HX-Request": "true"}).content,
            response.content,
        )
        self.assertEqual(
            self.get(
                "/packages?state=all",
                headers={"If-None-Match": response.headers["etag"]},
            ).status_code,
            304,
        )
        self.assertNotIn("hx-request", response.headers.get("vary", "").lower())
        self.assertTrue(all("/assets/" in e["src"] for e in soup.select("script[src]")))
        self.assertFalse(soup.select("script:not([src])"))

    def test_bad_reading_options(self):
        for query in [
            "state=bogus",
            "size=13",
            "follow=2",
            "cursor=-1",
            "count=2001",
            "direction=oops",
        ]:
            endpoint = (
                "/log?"
                if query.split("=")[0] in ("cursor", "count", "direction")
                else "/packages?"
            )
            with self.subTest(query=query):
                self.assertEqual(self.get(endpoint + query).status_code, 400)

    def test_campaign_ownership_and_legacy_permalinks(self):
        self.graph()
        aid = self.attempt("build")
        other = import_campaign(
            self.db,
            "Other",
            {"attrPaths": [["other"]]},
            "/nix/store/source",
            "abc",
            nix.DEFAULT_POLICY,
            "test",
        )
        for suffix in ["/packages/1", "/batches/" + aid, "/batches/" + aid + "/log"]:
            self.assertEqual(
                self.client.get("/campaigns/" + other + suffix).status_code, 404
            )
        response = self.client.get(
            "/?campaign=" + self.cid + "&package=1", follow_redirects=False
        )
        self.assertEqual(response.status_code, 303)
        self.assertIn(self.prefix + "/packages/1", response.headers["location"])

    def test_log_escaping_offsets_retry_and_recovery(self):
        self.graph()
        aid = self.attempt("build")
        self.log(aid, dict(action="start", type=105, id=3, fields=[A]))
        self.log(
            aid,
            dict(
                action="result",
                type=101,
                id=3,
                fields=["first <script>alert(1)</script>"],
            ),
        )
        self.log(aid, dict(action="result", type=101, id=3, fields=["second"]))
        self.controller.ingest(
            self.sql("SELECT * FROM attempts WHERE id=?", (aid,)).fetchone()
        )
        endpoint = "/batches/" + aid + "/log"
        response = self.get(endpoint)
        self.assertEqual(response.status_code, 200)
        self.assertNotIn("<script>alert(1)</script>", response.text)
        soup = BeautifulSoup(response.text, "html.parser")
        self.assertGreater(len(soup.select("[data-offset]")), 0)
        cursor = soup.select_one("#log-cursor")
        self.assertIn("click", cursor["hx-trigger"])
        self.assertIn("every", cursor["hx-trigger"])
        self.assertEqual(cursor["hx-sync"], "this:drop")
        self.assertIn("ignoreTitle:true", cursor["hx-swap"])
        recovery = self.get(endpoint + "?direction=after&cursor=999999999")
        self.assertEqual(recovery.headers["hx-retarget"], "closest #log-reader")
        self.assertEqual(recovery.headers["cache-control"], "no-store")
        capped = self.get(endpoint + "?count=2000&part=chunk")
        self.assertEqual(capped.headers["hx-retarget"], "closest #log-reader")
        self.assertEqual(capped.headers["hx-reselect"], "#log-reader")
        self.assertIn("<html", capped.text)
        paused = BeautifulSoup(self.get(endpoint + "?follow=0").text, "html.parser")
        self.assertEqual(paused.select_one("#log-cursor")["hx-trigger"], "click")

    def test_finished_logs_stop_and_csv_is_complete(self):
        self.graph()
        aid = self.attempt("build")
        self.sql(
            "UPDATE attempts SET state='finished',finished=created,result=? WHERE id=?",
            ('{"reason":"completed"}', aid),
        )
        self.sql("UPDATE candidates SET state='available'")
        self.db.commit()
        soup = BeautifulSoup(self.get("/batches/" + aid + "/log").text, "html.parser")
        self.assertIsNone(soup.select_one("#log-cursor"))
        self.assertIsNotNone(soup.select_one("[data-log-end]"))
        self.assertEqual(len(self.get("/packages.csv?state=all").text.splitlines()), 4)
        summary = BeautifulSoup(self.get("/summary").text, "html.parser")
        self.assertEqual(summary.select_one("#summary")["hx-trigger"], "none")

    def test_completed_event_stream_and_owned_html_links(self):
        self.graph()
        self.sql("UPDATE candidates SET state='available'")
        self.db.commit()
        response = self.get("/events")
        self.assertEqual(response.status_code, 200)
        self.assertIn("event: campaign-changed", response.text)
        self.assertIn("event: campaign-complete", response.text)
        self.assertEqual(response.headers["cache-control"], "no-store")
        for page in ["/packages?state=all", "/dependencies", "/batches"]:
            soup = BeautifulSoup(self.get(page).text, "html.parser")
            for link in soup.select("a[href]"):
                url = link["href"]
                if url.startswith(self.prefix) and "/events" not in url:
                    with self.subTest(url=url):
                        self.assertEqual(self.client.get(url).status_code, 200)


if __name__ == "__main__":
    unittest.main()
