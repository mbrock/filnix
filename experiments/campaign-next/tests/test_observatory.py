"""Read-only browser regressions against a served, representative recording.

Requires a completed campaign with more than 50 sessions, a built session with
captured output and more than 500 static inputs, and one failed session with
SGR-decorated Nix errors. No builds or database writes are issued.
Run with: uv run --with playwright python tests/test_observatory.py URL
Use --screenshots DIRECTORY to retain review captures.
"""

import argparse
import json
from pathlib import Path

from playwright.sync_api import sync_playwright


def scroll(page, selector, delta):
    rect = page.locator(selector).bounding_box()
    page.mouse.move(rect["x"] + 30, rect["y"] + rect["height"] / 2)
    page.mouse.wheel(0, delta)
    page.wait_for_timeout(250)


def position(page, selector):
    return page.locator(selector).evaluate("e => [e.scrollLeft, e.scrollTop]")


def refresh(page):
    with page.expect_response(lambda r: "/state?" in r.url):
        page.evaluate("htmx.trigger(document.querySelector('#state'), 'refresh')")
    page.wait_for_timeout(150)


def geometry(page):
    return page.evaluate("""() => Object.fromEntries(
      ['.sidebar','#session-results','.main','#state','#graph-scroll','.log-panel','#log-scroll'].map(s=>{
        const e=document.querySelector(s), r=e.getBoundingClientRect();
        return [s,{top:r.top,bottom:r.bottom,height:r.height,client:e.clientHeight,scroll:e.scrollHeight}];
      }))""")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("url")
    parser.add_argument("--chromium", default="/snap/bin/chromium")
    parser.add_argument("--screenshots", type=Path)
    args = parser.parse_args()
    base = args.url.rstrip("/") + "/"
    report = {}
    if args.screenshots:
        args.screenshots.mkdir(parents=True, exist_ok=True)

    with sync_playwright() as p:
        browser = p.chromium.launch(
            executable_path=args.chromium, args=["--no-sandbox"]
        )
        context = browser.new_context(
            viewport={"width": 1440, "height": 900}, device_scale_factor=2
        )
        page = context.new_page()
        errors = []
        page.on("pageerror", lambda e: errors.append(str(e)))
        data_requests = []
        page.on(
            "request",
            lambda r: (
                data_requests.append(r.url)
                if any(
                    "/" + path + "?" in r.url or r.url.endswith("/" + path)
                    for path in ("state", "sessions", "logs", "overview")
                )
                else None
            ),
        )
        page.goto(base)
        assert page.locator(".campaign-table tbody tr").count() == 50
        assert page.locator("#state, #log-rows, #graph-scroll").count() == 0
        assert "ffmpeg" not in page.title()
        report["overview_dom"] = page.evaluate("document.querySelectorAll('*').length")
        assert report["overview_dom"] < 1000
        cdp = context.new_cdp_session(page)
        cdp.send("Performance.enable")
        before = dict(
            (m["name"], m["value"])
            for m in cdp.send("Performance.getMetrics")["metrics"]
        )
        data_requests.clear()
        page.wait_for_timeout(6500)
        after = dict(
            (m["name"], m["value"])
            for m in cdp.send("Performance.getMetrics")["metrics"]
        )
        assert not data_requests, data_requests
        report["overview_idle_task_ms"] = 1000 * (
            after["TaskDuration"] - before["TaskDuration"]
        )
        if args.screenshots:
            page.screenshot(path=str(args.screenshots / "observatory-overview.png"))
        state = page.evaluate("fetch('./api/state').then(r=>r.json())")
        assert len(state["sessions"]) > 50, "Use a representative campaign"
        scroll(page, "#session-results", 700)
        assert position(page, "#session-results")[1] > 100
        assert page.locator(".campaign-table th").first.evaluate(
            "e=>Math.abs(e.getBoundingClientRect().top-document.querySelector('#session-results').getBoundingClientRect().top) < 1"
        )
        page.locator("#session-results").focus()
        page.locator("#session-results").press("End")
        page.get_by_role("button", name="Show next 50", exact=True).click()
        page.wait_for_function(
            "document.querySelector('.rail-count').dataset.after === '50'"
        )
        assert page.locator(".campaign-table tbody tr").count() == min(
            len(state["sessions"]) - 50, 50
        )
        assert position(page, "#session-results")[1] == 0
        page.locator("#session-results").press("End")
        page.get_by_role("button", name="Previous 50", exact=True).click()
        page.wait_for_function(
            "document.querySelector('.rail-count').dataset.after === '0'"
        )
        failed = next(s for s in state["sessions"] if s["outcome"] == "failed")
        page.locator('[data-filter="failed"]').click()
        page.wait_for_function(
            "document.querySelectorAll('.campaign-table tbody tr').length === 1"
        )
        assert (
            page.locator(".campaign-table tbody").inner_text().find(failed["name"]) >= 0
        )
        if args.screenshots:
            page.screenshot(
                path=str(args.screenshots / "observatory-overview-failed.png")
            )
        page.locator("#session-find").fill("no-such-package")
        page.wait_for_function(
            "document.querySelectorAll('.campaign-table tbody tr').length === 0"
        )
        assert page.locator(".empty").text_content() == "No sessions · failed"
        if args.screenshots:
            page.screenshot(
                path=str(args.screenshots / "observatory-overview-empty.png")
            )
        page.goto(base + "?run=" + failed["run"])
        red = (
            page.locator("#log-rows pre")
            .filter(has_text="Cannot build")
            .locator("span")
            .filter(has_text="error:")
            .first
        )
        assert red.evaluate("e=>getComputedStyle(e).color") == "rgb(150, 46, 41)"
        assert red.evaluate("e=>getComputedStyle(e).fontWeight") == "700"
        page.evaluate(
            "window.originalLog = document.querySelector('#log-rows').firstElementChild"
        )
        data_requests.clear()
        page.wait_for_timeout(6500)
        assert not data_requests, data_requests
        assert page.evaluate(
            "window.originalLog === document.querySelector('#log-rows').firstElementChild"
        )
        assert "�[31;1m" not in page.locator("#log-rows").text_content()
        page.locator("#log-find").fill("error: Cannot")
        assert page.locator("#find-count").text_content().startswith("1 matches")
        assert (
            red.locator("mark").evaluate("e=>getComputedStyle(e).color")
            == "rgb(150, 46, 41)"
        )
        page.locator("#log-find").fill("")
        assert page.locator("#log-rows mark").count() == 0
        assert red.evaluate("e=>getComputedStyle(e).color") == "rgb(150, 46, 41)"
        page.get_by_role("button", name="End", exact=True).click()
        page.wait_for_timeout(250)
        if args.screenshots:
            page.screenshot(path=str(args.screenshots / "observatory-sgr.png"))
        built = next(s for s in state["sessions"] if s["outcome"] == "built")
        for width, height in [
            (1440, 900),
            (1440, 600),
            (1440, 360),
            (2560, 1440),
            (1024, 600),
            (801, 600),
        ]:
            page.set_viewport_size({"width": width, "height": height})
            page.goto(base + "?run=" + built["run"])
            page.wait_for_timeout(200)
            g = geometry(page)
            assert page.evaluate(
                "document.scrollingElement.scrollHeight <= innerHeight + 1"
            )
            assert page.evaluate("document.scrollingElement.scrollWidth <= innerWidth")
            assert g["#session-results"]["scroll"] > g["#session-results"]["client"]
            assert g["#graph-scroll"]["height"] >= 30, g
            assert g["#log-scroll"]["height"] >= 60, g
            assert g[".log-panel"]["bottom"] <= height, g
            scroll(page, "#session-results", 500)
            assert position(page, "#session-results")[1] > 100
            assert page.evaluate("document.scrollingElement.scrollTop") == 0
            scroll(page, "#log-scroll", -300)
            page.wait_for_function(
                "document.querySelector('#log-follow').textContent === 'Follow'"
            )
            assert page.locator(".log-row").count() >= 200
            report[f"{width}x{height}"] = g

        # Narrow enough that long graph rows actually overflow horizontally.
        page.set_viewport_size({"width": 1024, "height": 900})
        page.goto(base + "?run=" + built["run"])
        page.locator("[data-static] summary").click()
        page.wait_for_function(
            "document.querySelectorAll('#static-rows .graph-node').length === 500"
        )
        scroll(page, "#graph-scroll", 500)
        page.locator("#graph-scroll").evaluate("e => {e.scrollLeft=160; e.focus()}")
        graph = position(page, "#graph-scroll")
        assert graph[1] > 100 and graph[0] > 0
        page.locator("#graph-scroll").press("PageDown")
        page.wait_for_timeout(250)
        assert position(page, "#graph-scroll")[1] > graph[1]
        graph = position(page, "#graph-scroll")
        scroll(page, "#session-results", 500)
        rail = position(page, "#session-results")
        page.locator(".campaign-line").evaluate("e=>e.scrollLeft=160")
        page.locator(".drv-fact dd").evaluate("e=>e.scrollLeft=100")
        campaign = position(page, ".campaign-line")
        drv = position(page, ".drv-fact dd")
        # Pause must not rebuild state; an actual refresh retains its panes.
        with page.expect_response(lambda r: "/logs?" in r.url):
            page.get_by_role("button", name="Follow", exact=True).click()
        page.wait_for_timeout(150)
        page.get_by_role("button", name="Pause", exact=True).click()
        assert position(page, "#graph-scroll") == graph
        activity = page.locator(".log-activity").first
        activity_x = activity.bounding_box()["x"]
        scroll(page, "#log-scroll", -300)
        page.locator("#log-scroll").evaluate("e=>e.scrollLeft=160")
        output = position(page, "#log-scroll")
        assert output[0] > 0
        assert abs(activity.bounding_box()["x"] - activity_x) < 1
        refresh(page)
        assert position(page, "#graph-scroll") == graph
        assert position(page, "#log-scroll") == output
        assert position(page, "#session-results") == rail
        assert position(page, ".campaign-line") == campaign
        assert position(page, ".drv-fact dd") == drv
        assert page.locator("[data-static]").evaluate("e=>e.open")
        page.locator("#session-results").focus()
        page.locator("#session-results").press("End")
        page.wait_for_timeout(250)
        # Delay a real page-zero response until after the operator selects page
        # 50. Independent polling/button requests used to swap out of order.
        page.evaluate("""() => {
          const original = window.fetch;
          window.staleRailReleased = false;
          window.fetch = async (...args) => {
            const response = await original(...args);
            const u = new URL(args[0], location.href);
            if (u.pathname.endsWith('/sessions') && u.searchParams.get('after') === '0') {
              await new Promise(r=>setTimeout(r,1200));
              window.staleRailReleased = true;
            }
            return response;
          };
          htmx.trigger(document.querySelector('#rail-controls'), 'change');
        }""")
        page.get_by_role("button", name="Show next 50", exact=True).click()
        page.wait_for_function(
            "document.querySelector('.rail-count').dataset.after === '50'"
        )
        page.wait_for_function("window.staleRailReleased")
        page.wait_for_timeout(3500)
        assert page.locator(".rail-count").get_attribute("data-after") == "50"

        node = page.locator("#static-rows .graph-node[id]").nth(40)
        fragment = node.get_attribute("id")
        page.goto(base + "?run=" + built["run"] + "#" + fragment)
        page.wait_for_function(
            "document.querySelector('#selected-node').textContent.startsWith('Selected · ')"
        )
        scroll(page, "#graph-scroll", 300)
        graph = position(page, "#graph-scroll")
        page.locator("#graph-scroll").focus()
        refresh(page)
        assert position(page, "#graph-scroll") == graph, (
            "Poll must not re-jump the URL fragment"
        )
        assert page.locator("#graph-scroll").evaluate("e=>e===document.activeElement")

        page.set_viewport_size({"width": 1440, "height": 360})
        page.locator(".native-result summary").click()
        scroll(page, ".session-summary", 80)
        summary = position(page, ".session-summary")
        assert summary[1] > 0
        refresh(page)
        assert page.locator(".native-result").evaluate("e=>e.open")
        assert position(page, ".session-summary") == summary
        assert geometry(page)["#log-scroll"]["height"] >= 60
        if args.screenshots:
            page.screenshot(path=str(args.screenshots / "observatory-scroll-short.png"))

        page.set_viewport_size({"width": 1440, "height": 900})
        for outcome in ["built", "failed", "timed-out"]:
            session = next(
                (s for s in state["sessions"] if s["outcome"] == outcome), None
            )
            if not session:
                continue
            page.goto(base + "?run=" + session["run"])
            page.wait_for_timeout(300)
            assert page.locator(".summary-head .status").text_content() == outcome
            assert geometry(page)[".log-panel"]["bottom"] <= 900
            if args.screenshots:
                page.screenshot(
                    path=str(args.screenshots / f"observatory-scroll-{outcome}.png")
                )
        mobile = browser.new_context(
            viewport={"width": 390, "height": 844},
            device_scale_factor=2,
            is_mobile=True,
            has_touch=True,
        )
        phone = mobile.new_page()
        phone.on("pageerror", lambda e: errors.append(str(e)))
        phone.goto(base)
        assert phone.evaluate("matchMedia('(pointer: coarse)').matches")
        assert phone.evaluate("document.scrollingElement.scrollWidth <= innerWidth")
        assert phone.locator(".campaign-table tbody tr").count() == 50
        if args.screenshots:
            phone.screenshot(
                path=str(args.screenshots / "observatory-overview-mobile.png")
            )
        phone.locator(".campaign-line").evaluate("e=>e.scrollLeft=300")
        assert position(phone, ".campaign-line")[0] > 100
        phone.goto(base + "?run=" + built["run"])
        assert phone.evaluate("matchMedia('(pointer: coarse)').matches")
        assert phone.evaluate("document.scrollingElement.scrollWidth <= innerWidth")
        assert geometry(phone)["#session-results"]["height"] >= 100
        # Touch-pan through CDP; wheel is not evidence of touch scrolling.
        rect = phone.locator("#session-results").bounding_box()
        cdp = mobile.new_cdp_session(phone)
        for kind, y in [
            ("touchStart", rect["y"] + 140),
            ("touchMove", rect["y"] + 40),
            ("touchEnd", 0),
        ]:
            cdp.send(
                "Input.dispatchTouchEvent",
                {
                    "type": kind,
                    "touchPoints": [] if kind == "touchEnd" else [{"x": 100, "y": y}],
                },
            )
            phone.wait_for_timeout(100)
        assert position(phone, "#session-results")[1] > 30
        phone.locator("#log-scroll").scroll_into_view_if_needed()
        assert geometry(phone)["#log-scroll"]["height"] >= 200
        if args.screenshots:
            phone.screenshot(
                path=str(args.screenshots / "observatory-scroll-mobile.png"),
                full_page=True,
            )
        assert not errors, errors
        report["errors"] = errors
        if args.screenshots:
            (args.screenshots / "observatory-scroll-check.json").write_text(
                json.dumps(report, indent=2)
            )
        print(json.dumps(report, indent=2))
        browser.close()


if __name__ == "__main__":
    main()
