"""HTML representation, isolation and byte-reader contracts."""

import time
import unittest
import uuid
from urllib.parse import parse_qs, urlsplit
from unittest.mock import patch

import test_experiment as fixtures
from bs4 import BeautifulSoup
from starlette.testclient import TestClient
from test_experiment import A, B

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

    @patch("experiment.dashboard.data.stamp", return_value=1800000000)
    def test_full_inventory_stable_html_and_conditional_get(self, _clock):
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

    def test_blockers_rank_failures_by_blocked_packages(self):
        self.graph()
        self.sql("UPDATE derivations SET failure='compile-or-link' WHERE drv=?", (A,))
        self.sql("UPDATE candidates SET state='failed' WHERE id=1")
        self.sql("UPDATE candidates SET state='blocked' WHERE id IN (2,3)")
        self.db.commit()
        page = BeautifulSoup(self.get("/blockers").text, "html.parser")
        rows = page.select("#blocker-list tbody tr")
        self.assertEqual(len(rows), 1)
        cells = [td.text.strip() for td in rows[0].select(":scope > td")]
        self.assertEqual(cells[1:], ["2", "2"])
        self.assertIn("Compilation or linking failed", cells[0])
        self.assertIn("2 packages", page.select_one("#blockers p").text)
        focus = rows[0].select_one("a")
        self.assertEqual(parse_qs(urlsplit(focus["href"]).query)["focus"], [A])
        summary = BeautifulSoup(self.get("/summary").text, "html.parser")
        self.assertIn("blocks 2", summary.select_one("#top-blockers").text)
        self.assertIn("only cause of 2", summary.select_one("#top-blockers").text)

    def test_blocker_ranking_refreshes_in_the_background(self):
        from experiment import blockers

        self.graph()
        self.sql("UPDATE candidates SET state='blocked' WHERE id IN (2,3)")
        self.db.commit()
        with patch.object(blockers, "SYNCHRONOUS", False), patch.object(
            blockers, "TTL", 0
        ):
            self.assertEqual(blockers.ranking(self.db, self.cid)["rows"], [])
            self.sql("UPDATE derivations SET failure='build' WHERE drv=?", (A,))
            self.db.commit()
            # A stale read returns the previous result and starts a refresh.
            self.assertEqual(blockers.ranking(self.db, self.cid)["rows"], [])
            for _ in range(200):
                if self.cid not in blockers._refreshing:
                    break
                time.sleep(0.01)
            rows = blockers._cache[self.cid][1]["rows"]
            self.assertEqual([(r["drv"], r["blocks"]) for r in rows], [(A, 2)])
            self.assertIn(B, blockers._cache[self.cid][1]["bad"])

    def test_cold_blocker_ranking_is_shared_by_concurrent_readers(self):
        from concurrent.futures import ThreadPoolExecutor
        import threading
        from experiment import blockers

        ready = threading.Barrier(8)
        result = {"rows": []}

        def compute(db, cid):
            time.sleep(0.1)
            return result

        def read():
            ready.wait(timeout=5)
            return blockers.ranking(None, self.cid)

        with patch.object(blockers, "SYNCHRONOUS", False), patch.object(
            blockers, "compute", side_effect=compute
        ) as walk:
            with ThreadPoolExecutor(max_workers=8) as pool:
                values = list(pool.map(lambda _: read(), range(8)))
            self.assertEqual(walk.call_count, 1)
            self.assertTrue(all(value is result for value in values))

    def test_placement_spec_is_parsed_once_across_readers_and_cache_is_bounded(self):
        import json
        import threading
        from concurrent.futures import ThreadPoolExecutor
        from experiment.dashboard import data

        self.graph()
        aid = self.attempt("build")
        self.sql("UPDATE attempts SET state='finished' WHERE id=?", (aid,))
        legacy = self.attempt("build")
        self.sql(
            "UPDATE attempts SET spec=? WHERE id=?",
            (
                json.dumps(dict(build_location="remote", admission_available=[A] * 10000)),
                aid,
            ),
        )
        self.db.commit()
        ready, queries = threading.Barrier(8), []

        def read(_):
            with data.read(self.state) as db:
                db.set_trace_callback(queries.append)
                ready.wait(timeout=5)
                return data.build_location(db, aid)

        with patch.object(data, "_locations", {str(i): "local" for i in range(128)}):
            with ThreadPoolExecutor(max_workers=8) as pool:
                values = list(pool.map(read, range(8)))
            self.assertEqual(values, ["remote"] * 8)
            self.assertEqual(sum("json_extract(spec" in q for q in queries), 1)
            self.assertEqual(len(data._locations), 128)
            self.assertNotIn("0", data._locations)
            self.db.set_trace_callback(queries.append)
            self.assertEqual(data.build_location(self.db, legacy), "mixed")
            self.assertEqual(len(data._locations), 128)
            data.summary(self.db, self.cid)
            data.summary(self.db, self.cid)
            self.assertEqual(sum("json_extract(spec" in q for q in queries), 2)

    def test_blocked_package_links_failure_owner_and_unfiltered_plan(self):
        self.graph()
        plan = self.attempt("plan")
        other = import_campaign(
            self.db,
            "Earlier campaign",
            {"attrPaths": [["other"]]},
            "/source",
            "old",
            nix.DEFAULT_POLICY,
            "test",
        )
        aid = str(uuid.uuid4())
        self.sql(
            "INSERT INTO attempts(id,campaign,kind,state,targets,created,spec) VALUES(?,?,'build','finished','[]',1,'{}')",
            (aid, other),
        )
        self.sql(
            "INSERT INTO activities(attempt,activity,drv,kind,phase,stopped) VALUES(?,'3',?,'build','checkPhase',1)",
            (aid, A),
        )
        self.sql(
            "UPDATE derivations SET failure='check',evidence_attempt=? WHERE drv=?",
            (aid, A),
        )
        self.sql("UPDATE candidates SET state='blocked' WHERE id=2")
        # Give the blocked consumer its own planning batch, but no build activity.
        self.sql(
            "UPDATE attempts SET targets=? WHERE id=?",
            ('[{"id":2,"attr":["b"]}]', plan),
        )
        self.db.commit()
        page = BeautifulSoup(self.get("/packages/2").text, "html.parser")
        self.assertIn("not queued for a build", page.text)
        self.assertIn("From Earlier campaign", page.text)
        self.assertIn("Tests failed", page.text)
        self.assertNotIn("Build log", page.text)
        planning = next(a for a in page.select("a") if a.text == "Planning log")
        self.assertNotIn("drv", parse_qs(urlsplit(planning["href"]).query))
        failure = next(a for a in page.select("a") if a.text == "Failure log")
        self.assertIn("/campaigns/" + other + "/batches/" + aid, failure["href"])
        self.assertEqual(parse_qs(urlsplit(failure["href"]).query)["drv"], [A])
        self.assertEqual(self.client.get(failure["href"]).status_code, 200)
        graph = BeautifulSoup(
            self.get("/dependencies", params={"focus": A}).text, "html.parser"
        )
        self.assertIn("From Earlier campaign", graph.select_one("#focus-node").text)
        self.assertIn(
            other,
            next(a for a in graph.select("#focus-node a") if a.text == "Failure log")[
                "href"
            ],
        )

    def test_failure_before_builder_starts_uses_batch_diagnostic(self):
        self.graph()
        aid = self.attempt("build")
        self.sql("UPDATE candidates SET state='failed' WHERE id=1")
        self.sql(
            "UPDATE derivations SET failure='build',evidence_attempt=? WHERE drv=?",
            (aid, A),
        )
        self.db.commit()
        page = BeautifulSoup(self.get("/packages/1").text, "html.parser")
        link = next(a for a in page.select("a") if a.text == "Batch diagnostic")
        self.assertNotIn("drv", parse_qs(urlsplit(link["href"]).query))
        # Old bookmarked filtered planning/build URLs also explain their emptiness.
        page = BeautifulSoup(
            self.get("/batches/" + aid + "/log", params={"drv": B}).text, "html.parser"
        )
        self.assertIn(
            "No build output was recorded", page.select_one("#log-empty").text
        )
        self.assertEqual(page.select_one("option[selected]")["value"], B)

    def test_scoped_log_search_reaches_older_failure_in_bounded_steps(self):
        from experiment.dashboard import data
        from experiment.dashboard.resources import View
        from experiment.logs import PAGE

        self.graph()
        aid = self.attempt("build")
        self.log(aid, dict(action="start", type=105, id=3, fields=[A]))
        self.log(
            aid,
            dict(
                action="result",
                type=101,
                id=3,
                fields=["fatal: actual compiler diagnostic"],
            ),
        )
        self.sql(
            "INSERT INTO activities(attempt,activity,drv,kind,stopped) VALUES(?,'3',?,'build',1)",
            (aid, A),
        )
        with (self.folder(aid) / "stderr.log").open("ab") as f:
            f.write((b"unrelated later build output " + b"x" * 100 + b"\n") * 40000)
        self.sql(
            "UPDATE attempts SET state='finished',finished=created WHERE id=?", (aid,)
        )
        self.db.commit()
        v = View(drv=A)
        result = data.log(self.db, self.state, self.cid, aid, v)
        self.assertTrue(result["searching"])
        self.assertLessEqual(result["size"] - result["start"], 9 * PAGE)
        page = BeautifulSoup(
            self.get("/batches/" + aid + "/log", params={"drv": A}).text, "html.parser"
        )
        self.assertIn("Looking for this build's earlier output", page.text)
        self.assertIsNotNone(page.select_one("#log-search"))
        self.assertIsNone(page.select_one("#log-cursor"))
        for _ in range(5):
            if not result["searching"]:
                break
            previous = result["start"]
            result = data.log(self.db, self.state, self.cid, aid, v, "before", previous)
            self.assertLess(result["start"], previous)
        self.assertFalse(result["searching"])
        self.assertTrue(
            any("actual compiler diagnostic" in e["text"] for e in result["entries"])
        )

    def test_retry_clear_shows_queued_with_previous_log(self):
        self.graph()
        aid = self.attempt("build")
        self.sql("UPDATE attempts SET state='finished' WHERE id=?", (aid,))
        self.sql("UPDATE candidates SET state='queued' WHERE id=1")
        self.sql(
            "UPDATE derivations SET evidence_attempt=?,failure=NULL WHERE drv=?",
            (aid, A),
        )
        self.db.commit()
        page = BeautifulSoup(
            self.get("/dependencies", params={"focus": A}).text, "html.parser"
        )
        self.assertEqual(
            page.select_one("#focus-node [data-status]")["data-status"], "queued"
        )
        self.assertNotIn(
            "explicit retry is required", page.select_one("#focus-node").text
        )
        self.assertEqual(
            self.client.get(
                "/api/derivation", params={"drv": A, "campaign": self.cid}
            ).status_code,
            200,
        )

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

    def test_live_activity_and_held_inventory_contracts(self):
        self.graph()
        aid = self.attempt("build")
        first = BeautifulSoup(self.get("").text, "html.parser")
        self.assertIn("every 5s", first.select_one("#activity-feed")["hx-trigger"])
        held = BeautifulSoup(self.get("?watch=0").text, "html.parser")
        self.assertEqual(held.select_one("#activity-feed")["hx-trigger"], "none")
        self.assertNotEqual(held.select_one("#summary")["hx-trigger"], "none")
        self.sql("UPDATE candidates SET state='failed' WHERE id=1")
        self.sql("UPDATE candidates SET state='evaluation-error' WHERE id=2")
        self.db.commit()
        for state, count in [("failed", 1), ("evaluation-error", 1), ("failures", 2)]:
            page = BeautifulSoup(
                self.get("/packages?state=" + state).text, "html.parser"
            )
            self.assertEqual(len(page.select("#package-list tbody tr")), count)
            self.assertIsNone(page.select_one("#package-list").get("hx-trigger"))
            self.assertIsNone(page.select_one("#updates").find_parent("details"))
        feed = BeautifulSoup(self.get("/activity").text, "html.parser")
        self.assertIsNotNone(feed.select_one('[data-batch="' + aid + '"]'))

    def test_monitor_connects_activity_to_root_with_observed_time_not_request_time(
        self,
    ):
        self.graph()
        aid = self.controller.build_targets(self.controller.campaign(self.cid), [B])
        self.sql(
            "INSERT INTO activities(attempt,activity,drv,kind,phase) VALUES(?,'1',?,'build','checkPhase')",
            (aid, A),
        )
        self.sql("INSERT INTO build_times VALUES(?,'1',100,NULL)", (aid,))
        self.sql("UPDATE attempts SET created=10 WHERE id=?", (aid,))
        self.db.commit()
        with patch("experiment.dashboard.data.stamp", return_value=143):
            page = BeautifulSoup(self.get("").text, "html.parser")
        card = page.find(id="active-" + aid)
        root = card.find(attrs={"data-drv": B})
        dependency = card.find(attrs={"data-drv": A})
        self.assertEqual(root["data-state"], "waiting")
        self.assertEqual(dependency["data-state"], "building")
        self.assertEqual(dependency.find_parent("ul").previous_sibling, root)
        self.assertIn("check", dependency.text)
        self.assertIn("43s", dependency.text)
        self.assertIn("request 2m 13s", card.text)
        self.assertIn(
            A, parse_qs(urlsplit(dependency.find_all("a")[-1]["href"]).query)["drv"]
        )
        self.assertIsNone(page.select_one("#request-history").get("open"))

    def test_monitor_stopped_activity_is_not_success_and_cycles_do_not_repeat_it(self):
        self.graph()
        aid = self.controller.build_targets(self.controller.campaign(self.cid), [B])
        self.sql("INSERT INTO edges VALUES(?,?,?)", (A, B, '["out"]'))
        self.sql(
            "INSERT INTO activities(attempt,activity,drv,kind,phase,stopped) VALUES(?,'1',?,'build','checkPhase',1)",
            (aid, A),
        )
        self.sql("INSERT INTO build_times VALUES(?,'1',100,117)", (aid,))
        self.sql("UPDATE derivations SET available=1 WHERE drv=?", (A,))
        self.db.commit()
        page = BeautifulSoup(self.get("").text, "html.parser")
        rows = page.select('#build-monitor [data-drv="' + A + '"]')
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["data-state"], "awaiting-result")
        self.assertIn("17s", rows[0].text)
        self.assertIn("Awaiting result", rows[0].text)
        self.assertNotIn("Built", rows[0].text)
        self.assertNotIn("Tested", rows[0].text)

    def test_monitor_budget_keeps_unconnected_activity_without_inventing_an_edge(self):
        from experiment.dashboard.data import build_forest

        self.graph()
        aid = self.attempt("build")
        # Two broad layers exceed the bounded reverse-edge query budget.
        drvs = [f"/nix/store/{i:032d}-wide.drv" for i in range(300)]
        for drv in drvs:
            self.sql(
                "INSERT INTO derivations(drv,name,outputs) VALUES(?,?,'{}')",
                (drv, "wide"),
            )
        for i, drv in enumerate(drvs):
            child = B if i < 32 else drvs[(i - 32) // 9]
            self.sql("INSERT INTO edges VALUES(?,?,?)", (drv, child, '["out"]'))
        self.sql(
            "INSERT INTO activities(attempt,activity,drv,kind) VALUES(?,'1',?,'build')",
            (aid, B),
        )
        queries = []
        self.db.set_trace_callback(queries.append)
        try:
            groups = build_forest(
                self.db,
                [dict(id=aid, kind="build", targets=[dict(drv=A, label="root")])],
                set(drvs) | {A, B},
                1000,
            )
        finally:
            self.db.set_trace_callback(None)
        self.assertEqual(groups[0]["tree"], {})
        self.assertEqual([n["drv"] for n in groups[0]["detached"]], [B])
        self.assertTrue(groups[0]["partial"])
        self.assertEqual(sum("SELECT parent FROM edges" in q for q in queries), 256)

    def test_detail_refresh_and_campaign_scoped_test_evidence(self):
        self.graph()
        aid = self.attempt("build")
        page = BeautifulSoup(self.get("/packages/1").text, "html.parser")
        self.assertEqual(
            page.select_one("#package-detail")["hx-select"], "#package-detail"
        )
        self.assertIn("every 5s", page.select_one("#package-detail")["hx-trigger"])
        self.sql("UPDATE candidates SET state='available'")
        other = import_campaign(
            self.db,
            "Other",
            {"attrPaths": [["elsewhere"]]},
            "/source",
            "abc",
            nix.DEFAULT_POLICY,
            "test",
        )
        self.sql(
            "INSERT INTO attempts(id,campaign,kind,state,targets,created,spec) VALUES('outside',?,'build','finished','[]',1,'{}')",
            (other,),
        )
        for drv in (A, B):
            self.sql("INSERT INTO tests VALUES('outside',?,'checkPhase','{}')", (drv,))
        self.sql("INSERT INTO roles VALUES(?,?,?,'host')", (self.cid, B, A))
        self.db.commit()
        page = self.get("/packages/1").text
        self.assertNotIn("Tested consumers", page)
        self.assertNotIn("Test evidence", page)
        self.assertEqual(
            self.client.get("/api/snapshot?campaign=" + self.cid).json()["tested"], 0
        )
        self.sql("INSERT INTO tests VALUES(?,?,'checkPhase','{}')", (aid, B))
        self.db.commit()
        self.assertIn("Tested consumers", self.get("/packages/1").text)

    def test_parallel_timeline_and_stopped_activities(self):
        self.graph()
        aid = self.attempt("build")
        self.sql(
            "INSERT INTO attempts(id,campaign,kind,state,targets,created,spec) SELECT 'parallel',campaign,kind,state,targets,created,spec FROM attempts WHERE id=?",
            (aid,),
        )
        self.sql(
            "INSERT INTO activities(attempt,activity,drv,kind,phase,stopped) VALUES(?,'1',?,'build','buildPhase',1)",
            (aid, A),
        )
        self.db.commit()
        soup = BeautifulSoup(self.get("/activity").text, "html.parser")
        lanes = [
            soup.select_one('[data-batch="' + v + '"]')["data-lane"]
            for v in (aid, "parallel")
        ]
        self.assertNotEqual(*lanes)
        soup = BeautifulSoup(self.get("/batches/" + aid).text, "html.parser")
        self.assertIn("Awaiting result", soup.get_text())
        self.assertNotIn("Stopped", soup.get_text())
        self.assertNotIn("Tested", soup.get_text())
        self.assertIn("awaiting result", soup.select_one("#batch-build-summary").text)

    def test_batch_completion_and_results_are_distinct(self):
        self.graph()
        aid = self.attempt("build")
        self.sql(
            "INSERT INTO activities(attempt,activity,drv,kind,stopped) VALUES(?,'1',?,'build',1)",
            (aid, A),
        )
        from experiment.model import encode

        self.sql(
            "UPDATE attempts SET state='finished',finished=created+10,result=? WHERE id=?",
            (encode({"reason": "build-error", "build_outcomes": {A: "built"}}), aid),
        )
        self.db.commit()
        page = BeautifulSoup(self.get("/batches/" + aid).text, "html.parser")
        self.assertIn("Finished · errors", page.select_one("#batch-heading").text)
        self.assertEqual(page.select_one("#batch-status")["hx-trigger"], "none")
        self.assertEqual(
            page.select_one("[data-build-status]")["data-build-status"], "built"
        )
        self.assertIn("Built", page.select_one("[data-build-status]").text)
        self.assertNotIn("Stopped", page.text)
        self.assertNotIn("await confirmation", page.text)
        self.assertIn("Finished · errors", self.get("/batches").text)


if __name__ == "__main__":
    unittest.main()
