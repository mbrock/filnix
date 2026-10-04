"""Read-only Chromium checks against a representative, completed recording.

Requires >50 sessions, a built session with output and >500 static inputs,
and a failed session with SGR-decorated Nix errors. No builds are requested.
Run: uv run --with playwright python tests/test_observatory.py URL
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
      ['#state','#inspection-scroll','.log-panel','#log-scroll'].map(s=>{
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
    report, errors, data_requests = {}, [], []
    if args.screenshots:
        args.screenshots.mkdir(parents=True, exist_ok=True)

    def capture(page, name):
        if args.screenshots:
            page.evaluate(
                "new Promise(r=>requestAnimationFrame(()=>requestAnimationFrame(r)))"
            )
            page.screenshot(path=str(args.screenshots / (name + ".png")))

    with sync_playwright() as p:
        browser = p.chromium.launch(
            executable_path=args.chromium, args=["--no-sandbox"]
        )
        context = browser.new_context(
            viewport={"width": 1440, "height": 900}, device_scale_factor=2
        )
        context.grant_permissions(["clipboard-read", "clipboard-write"])
        page = context.new_page()
        page.on("pageerror", lambda e: errors.append(str(e)))
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
        assert page.locator("#state, #log-rows, .sidebar").count() == 0
        assert page.locator(".campaign-table th").all_text_contents() == [
            "Package",
            "State",
            "Events",
            "Output lines",
            "Phase / result",
        ]
        assert "ffmpeg" not in page.title()
        report["overview_dom"] = page.evaluate("document.querySelectorAll('*').length")
        assert report["overview_dom"] < 1000
        data_requests.clear()
        page.wait_for_timeout(6500)
        assert not data_requests, data_requests
        capture(page, "observatory-index")
        state = page.evaluate("fetch('./api/state').then(r=>r.json())")
        assert len(state["sessions"]) > 50
        built = next(s for s in state["sessions"] if s["outcome"] == "built")
        failed = next(s for s in state["sessions"] if s["outcome"] == "failed")
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
        # A delayed page-zero response must not override a newer page intent.
        page.evaluate("""() => {
          const original = window.fetch;
          window.staleReleased = false;
          window.fetch = async (...args) => {
            const response = await original(...args);
            const u = new URL(args[0], location.href);
            if (u.pathname.endsWith('/sessions') && u.searchParams.get('after') === '0') {
              await new Promise(r=>setTimeout(r,1200)); window.staleReleased = true;
            }
            return response;
          };
          const form = document.querySelector('#rail-controls');
          document.querySelector('#rail-after').value = '0';
          htmx.trigger(form, 'change');
        }""")
        page.locator("#rail-after").evaluate("e=>e.value='50'")
        page.wait_for_function("window.staleReleased")
        assert page.locator(".rail-count").get_attribute("data-after") == "50"
        page.locator('[data-filter="failed"]').click()
        page.wait_for_function(
            "document.querySelectorAll('.campaign-table tbody tr').length === 1"
        )
        assert failed["name"] in page.locator(".campaign-table tbody").inner_text()
        assert page.locator(".session-observation").text_content() == "DependencyFailed"
        capture(page, "observatory-index-failed")
        page.locator("#session-find").fill("no-such-package")
        page.wait_for_function(
            "document.querySelectorAll('.campaign-table tbody tr').length === 0"
        )
        assert page.locator(".empty").text_content() == "No sessions · failed"
        capture(page, "observatory-index-empty")
        page.goto(base + "?run=" + failed["run"] + "&filter=failed")
        assert page.locator(".campaign-table, .sidebar, .campaign-line").count() == 0
        assert "filter=failed" in page.locator("#sessions-back").get_attribute("href")
        assert "1 dependency failed" in page.locator(".failure").text_content()
        page.locator(".output-paths summary").click()
        assert "reported" in page.locator(".output-paths summary").text_content()
        assert "/nix/store/" in page.locator(".output-paths pre").text_content()
        page.locator(".output-paths summary").click()
        page.locator(".reported-errors summary").click()
        assert "flac" in page.locator(".reported-errors").text_content()
        page.locator(".reported-errors summary").click()
        page.get_by_role("button", name="Copy drv", exact=True).click()
        assert page.evaluate("navigator.clipboard.readText()") == failed["drv"]
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
            "window.originalLog=document.querySelector('#log-rows').firstElementChild"
        )
        data_requests.clear()
        page.wait_for_timeout(6500)
        assert not data_requests, data_requests
        assert page.evaluate(
            "window.originalLog===document.querySelector('#log-rows').firstElementChild"
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
        with page.expect_response(lambda r: "/logs?" in r.url):
            page.get_by_role("button", name="End", exact=True).click()
        page.wait_for_function(
            "(() => {const e=document.querySelector('#log-scroll'); return e.scrollHeight-e.scrollTop-e.clientHeight<=1})()"
        )
        capture(page, "observatory-inspector-failed")

        for width, height in [
            (1440, 900),
            (1440, 360),
            (2560, 1440),
            (1024, 600),
            (801, 600),
        ]:
            page.set_viewport_size({"width": width, "height": height})
            page.goto(base + "?run=" + built["run"])
            g = geometry(page)
            assert page.evaluate(
                "document.scrollingElement.scrollHeight <= innerHeight + 1"
            )
            assert page.evaluate("document.scrollingElement.scrollWidth <= innerWidth")
            assert g["#inspection-scroll"]["height"] >= 60, g
            assert g["#inspection-scroll"]["bottom"] <= g["#state"]["bottom"] + 1, g
            assert g["#log-scroll"]["height"] >= 150, g
            assert g[".log-panel"]["bottom"] <= height, g
            assert page.locator("#static-rows .graph-node").count() == 0
            assert page.locator(".log-row").count() == 200
            assert page.locator(".log-row pre").evaluate_all(
                "es=>es.every(e=>e.scrollWidth<=e.clientWidth+1)"
            )
            assert page.locator(".log-activity").evaluate_all(
                "es=>es.every(e=>e.scrollWidth<=e.clientWidth+1)"
            )
            # Metadata widths and message starts do not depend on their text.
            starts = page.locator(".log-row pre").evaluate_all(
                "es=>es.slice(0,20).map(e=>e.getBoundingClientRect().left)"
            )
            assert max(starts) - min(starts) < 1
            scroll(page, "#inspection-scroll", 200)
            if g["#inspection-scroll"]["scroll"] > g["#inspection-scroll"]["client"]:
                assert position(page, "#inspection-scroll")[1] > 0
            assert page.evaluate("document.scrollingElement.scrollTop") == 0
            scroll(page, "#log-scroll", -300)
            assert page.locator("#log-follow").text_content() == "Follow"
            report[f"{width}x{height}"] = g

        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(base + "?run=" + built["run"])
        report["detail_dom"] = page.evaluate("document.querySelectorAll('*').length")
        assert report["detail_dom"] < 2000
        assert page.locator(".phase-ledger tbody tr").count() > 0
        capture(page, "observatory-inspector-built")
        phase = page.locator(".phase-ledger button").first
        activity = phase.get_attribute("data-phase-activity")
        with page.expect_response(lambda r: "/logs?" in r.url):
            phase.click()
        page.wait_for_function(
            "document.querySelector('#log-cursor').dataset.activity === '"
            + activity
            + "'"
        )
        assert "activity=" + activity in page.url
        assert page.locator("#log-follow").text_content() == "Follow"
        page.get_by_role("link", name="All output", exact=True).click()
        assert "activity=" not in page.url
        with page.expect_response(lambda r: "/logs?" in r.url):
            page.get_by_role("button", name="Follow", exact=True).click()
        page.get_by_role("button", name="Pause", exact=True).click()
        page.locator("#log-wrap").uncheck()
        assert page.locator(".log-row pre").evaluate_all(
            "es=>es.some(e=>e.scrollWidth>e.clientWidth)"
        )
        page.locator("#log-wrap").check()
        assert page.locator(".log-row pre").evaluate_all(
            "es=>es.every(e=>e.scrollWidth<=e.clientWidth+1)"
        )
        page.locator("[data-static] summary").click()
        page.wait_for_function(
            "document.querySelectorAll('#static-rows .graph-node').length === 500"
        )
        assert page.locator(".graph-truncated").count() == 1
        inspector = position(page, "#inspection-scroll")
        scroll(page, "#inspection-scroll", 200)
        assert position(page, "#inspection-scroll")[1] > inspector[1]
        inspector = position(page, "#inspection-scroll")
        page.locator("#inspection-scroll").focus()
        refresh(page)
        assert position(page, "#inspection-scroll") == inspector
        assert page.locator("[data-static]").evaluate("e=>e.open")
        assert page.locator("#inspection-scroll").evaluate(
            "e=>e===document.activeElement"
        )
        page.locator("#inspection-scroll").press("End")
        page.get_by_role("button", name="Show next 500", exact=True).click()
        page.wait_for_function(
            "document.querySelector('#static-rows .snapshot').textContent.includes('500–1000')"
        )
        assert page.locator("#static-rows .graph-node").count() == 500
        node = page.locator("#static-rows .graph-node[id]").nth(40)
        fragment, name = node.get_attribute("id"), node.get_attribute("data-name")
        page.goto(base + "?run=" + built["run"] + "#" + fragment)
        page.wait_for_function(
            "document.querySelector('#selected-node').textContent.startsWith('Selected · ')"
        )
        assert page.locator("#selected-node").text_content() == "Selected · " + name
        assert built["name"] in page.title()
        inspector = position(page, "#inspection-scroll")
        refresh(page)
        assert position(page, "#inspection-scroll") == inspector
        page.goto(base + "?run=" + built["run"])
        page.locator(".native-result summary").click()
        refresh(page)
        assert page.locator(".native-result").evaluate("e=>e.open")
        timeout = next(s for s in state["sessions"] if s["outcome"] == "timed-out")
        page.goto(base + "?run=" + timeout["run"])
        assert page.locator(".summary-head .status").text_content() == "timed-out"
        assert page.locator(".failure").text_content() == "root time limit reached"
        capture(page, "observatory-inspector-timeout")

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
        assert phone.locator("#state, .log-panel").count() == 0
        assert phone.locator(".campaign-line button").evaluate_all(
            "es=>es.every(e=>e.getBoundingClientRect().right<=innerWidth)"
        )
        capture(phone, "observatory-index-mobile")
        # A real touch-pan through CDP, not desktop wheel emulation.
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
        phone.goto(base + "?run=" + built["run"])
        assert phone.locator(".campaign-table, .sidebar").count() == 0
        assert (
            phone.locator("#inspection-toggle").get_attribute("aria-expanded")
            == "false"
        )
        assert geometry(phone)["#log-scroll"]["height"] > 500
        assert phone.locator(".log-row pre").evaluate_all(
            "es=>es.every(e=>e.scrollWidth<=e.clientWidth+1)"
        )
        capture(phone, "observatory-inspector-mobile")
        phone.locator("#inspection-toggle").tap()
        assert geometry(phone)["#log-scroll"]["height"] > 300
        assert phone.evaluate("document.scrollingElement.scrollWidth <= innerWidth")
        capture(phone, "observatory-inspector-mobile-open")
        refresh(phone)
        assert (
            phone.locator("#inspection-toggle").get_attribute("aria-expanded") == "true"
        )
        phone.locator("#inspection-toggle").tap()
        refresh(phone)
        assert (
            phone.locator("#inspection-toggle").get_attribute("aria-expanded")
            == "false"
        )
        phone.goto(base + "?run=" + failed["run"])
        assert "failed" in phone.locator("#state .summary-head").text_content()
        assert phone.locator(".failure").is_visible()
        phone.wait_for_function(
            "(() => {const e=document.querySelector('#log-scroll'); return e.scrollHeight-e.scrollTop-e.clientHeight<=1})()"
        )
        capture(phone, "observatory-inspector-mobile-failed")
        assert not errors, errors
        report["errors"] = errors
        if args.screenshots:
            (args.screenshots / "observatory-instrument-check.json").write_text(
                json.dumps(report, indent=2)
            )
        print(json.dumps(report, indent=2))
        browser.close()


if __name__ == "__main__":
    main()
