"""Read-only Chromium checks against a representative, completed recording.

Requires >50 sessions, a built session with >500 output rows and >500 static
inputs, a failed session with SGR-decorated Nix errors, and a timed-out one.
No builds are requested.
Run: uv run --with playwright python tests/test_observatory.py URL
"""

import argparse
import json
from pathlib import Path

from playwright.sync_api import sync_playwright


def page_scroll(page):
    return page.evaluate("document.scrollingElement.scrollTop")


def refresh(page):
    with page.expect_response(lambda r: "/state?" in r.url):
        page.evaluate("htmx.trigger(document.querySelector('#state'), 'refresh')")
    page.wait_for_timeout(150)


def no_horizontal_overflow(page):
    return page.evaluate("document.scrollingElement.scrollWidth <= innerWidth")


def wrapped(page):
    return page.locator(".log-row pre").evaluate_all(
        "es=>es.every(e=>e.scrollWidth<=e.clientWidth+1)"
    )


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

    def capture(page, name, full=False):
        if args.screenshots:
            page.evaluate(
                "new Promise(r=>requestAnimationFrame(()=>requestAnimationFrame(r)))"
            )
            page.screenshot(path=str(args.screenshots / (name + ".png")), full_page=full)

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

        # Index: one page scroll, problems first, success without commentary.
        page.goto(base)
        state = page.evaluate("fetch('./api/state').then(r=>r.json())")
        roots = len(state["cohort"]["roots"])
        built = next(s for s in state["sessions"] if s["outcome"] == "built" and s["output_lines"] > 600)
        failed = next(s for s in state["sessions"] if s["outcome"] == "failed")
        timeout = next(s for s in state["sessions"] if s["outcome"] == "timed-out")
        assert page.locator(".campaign-table tbody tr").count() == min(roots, 100)
        assert page.locator("#state, #log-rows, .attention").count() == 0
        assert page.locator(".campaign-table th").all_text_contents() == [
            "Package", "Version", "Status", "Duration", "Detail",
        ]
        statuses = page.locator(".campaign-table tbody tr").evaluate_all(
            "es=>es.map(e=>e.dataset.status)"
        )
        problems = [s for s in statuses if s not in ("built", "already-valid", "unattempted")]
        assert statuses[: len(problems)] == problems, statuses
        assert page.locator(
            'tr[data-status="built"] .session-observation, tr[data-status="already-valid"] .session-observation'
        ).evaluate_all("es=>es.every(e=>e.textContent==='')")
        assert page.evaluate("document.scrollingElement.scrollHeight > innerHeight")
        assert no_horizontal_overflow(page)
        assert "ffmpeg" not in page.title()
        report["overview_dom"] = page.evaluate("document.querySelectorAll('*').length")
        assert report["overview_dom"] < 1500
        data_requests.clear()
        page.wait_for_timeout(6500)
        assert not data_requests, data_requests
        capture(page, "observatory-index")
        page.mouse.wheel(0, 900)
        page.wait_for_timeout(250)
        assert page_scroll(page) > 100
        page.locator('[data-filter="failed"]').click()
        page.wait_for_function(
            "document.querySelectorAll('.campaign-table tbody tr').length === 1"
        )
        assert (
            page.locator(".campaign-table tbody .pkg-cell").get_attribute("title")
            == failed["name"]
        )
        assert "timed out" in page.locator(".session-observation").text_content()
        page.locator("#session-find").fill("no-such-package")
        page.wait_for_function(
            "document.querySelectorAll('.campaign-table tbody tr').length === 0"
        )
        assert page.locator(".empty").text_content() == "No sessions · failed"

        # Failed session: the cause chain leads into the log.
        page.goto(base + "?run=" + failed["run"] + "&filter=failed")
        assert page.locator(".campaign-table, .campaign-line, #inspection-toggle").count() == 0
        assert "filter=failed" in page.locator("#sessions-back").get_attribute("href")
        assert "1 dependency failed" in page.locator(".failure").text_content()
        assert page.locator(".failure .cause.origin").count() == 1
        assert page.locator(".phase-ledger th, .snapshot").count() == 0
        page.locator(".output-paths summary").click()
        assert "reported" in page.locator(".output-paths summary").text_content()
        assert "/nix/store/" in page.locator(".output-paths pre").text_content()
        page.locator(".reported-errors summary").click()
        assert "flac" in page.locator(".reported-errors").text_content()
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
        assert "�[31;1m" not in page.locator("#log-rows").text_content()
        # Sources label only where they change; times are a clock.
        labelled = page.locator(".log-row:not(.same) .log-source").count()
        assert 0 < labelled < page.locator(".log-row").count() / 10
        assert all(
            ":" in t and "." not in t
            for t in page.locator(".log-row time").all_text_contents()[:20]
        )
        page.evaluate("window.originalLog=document.querySelector('#log-rows').firstElementChild")
        data_requests.clear()
        page.wait_for_timeout(6500)
        assert not data_requests, data_requests
        assert page.evaluate(
            "window.originalLog===document.querySelector('#log-rows').firstElementChild"
        )
        page.locator("#log-find").fill("error: Cannot")
        assert page.locator("#find-count").text_content().startswith("1 matches")
        assert (
            red.locator("mark").evaluate("e=>getComputedStyle(e).color")
            == "rgb(150, 46, 41)"
        )
        page.locator("#log-find").fill("")
        assert page.locator("#log-rows mark").count() == 0
        with page.expect_response(lambda r: "/logs?" in r.url):
            page.locator(".failure .cause.origin button").click()
        page.wait_for_function(
            "document.querySelector('#log-rows').textContent.includes('timed out after')"
        )
        with page.expect_response(lambda r: "/logs?" in r.url):
            page.get_by_role("button", name="End", exact=True).click()
        page.wait_for_function(
            "(() => {const e=document.scrollingElement; return e.scrollHeight-e.scrollTop-innerHeight<=1})()"
        )
        capture(page, "observatory-inspector-failed")

        # Built session: full history is reachable; the page is the scroller.
        for width, height in [(1440, 900), (2560, 1440), (1024, 600), (801, 600)]:
            page.set_viewport_size({"width": width, "height": height})
            page.goto(base + "?run=" + built["run"])
            assert no_horizontal_overflow(page)
            assert page.locator(".log-row").count() == 500
            assert wrapped(page)
            assert page.locator("#state").evaluate(
                "e=>getComputedStyle(e).position"
            ) == "sticky"
            # The console header stays in view while reading.
            page.mouse.wheel(0, 3000)
            page.wait_for_timeout(250)
            top = page.locator(".log-panel > .panel-head").bounding_box()["y"]
            assert abs(top) < 1, top
            report[f"{width}x{height}"] = page_scroll(page)

        page.set_viewport_size({"width": 1440, "height": 900})
        page.goto(base + "?run=" + built["run"])
        report["detail_dom"] = page.evaluate("document.querySelectorAll('*').length")
        assert report["detail_dom"] < 5000
        assert page.locator(".phase-ledger tbody tr").count() > 0
        assert page.locator("#log-earlier").is_visible()
        anchor = page.locator(".log-row").first
        anchor.scroll_into_view_if_needed()
        seq, y = anchor.get_attribute("data-seq"), anchor.bounding_box()["y"]
        with page.expect_response(lambda r: "before=" in r.url):
            page.locator("#log-earlier").click()
        page.wait_for_function("document.querySelectorAll('.log-row').length > 500")
        moved = page.locator(f'.log-row[data-seq="{seq}"]').bounding_box()["y"]
        assert abs(moved - y) < 2, (y, moved)
        report["earlier_rows"] = page.locator(".log-row").count()
        capture(page, "observatory-inspector-built")
        phase = page.locator(".phase-ledger button").first
        activity = phase.get_attribute("data-phase-activity")
        with page.expect_response(lambda r: "/logs?" in r.url):
            phase.click()
        page.wait_for_function(
            "document.querySelector('#log-cursor').dataset.activity === '" + activity + "'"
        )
        assert "activity=" + activity in page.url
        page.goto(page.url)
        assert page.locator(".log-scope").is_visible()
        page.get_by_role("link", name="Show all output", exact=True).click()
        assert "activity=" not in page.url
        assert page.locator(".log-scope").count() == 0
        with page.expect_response(lambda r: "/logs?" in r.url):
            page.get_by_role("button", name="Follow", exact=True).click()
        page.get_by_role("button", name="Pause", exact=True).click()
        page.locator("#log-wrap").uncheck()
        assert page.locator(".log-row pre").evaluate_all(
            "es=>es.some(e=>e.scrollWidth>e.clientWidth)"
        )
        page.locator("#log-wrap").check()
        assert wrapped(page)
        page.locator("[data-static] summary").click()
        page.wait_for_function(
            "document.querySelectorAll('#static-rows .graph-node').length === 500"
        )
        assert page.locator(".graph-truncated").count() == 1
        refresh(page)
        assert page.locator("[data-static]").evaluate("e=>e.open")
        page.get_by_role("button", name="Show next 500", exact=True).click()
        page.wait_for_function(
            "document.querySelector('#static-rows .snapshot').textContent.includes('500–1000')"
        )
        node = page.locator("#static-rows .graph-node[id]").nth(40)
        fragment, name = node.get_attribute("id"), node.get_attribute("data-name")
        page.goto(base + "?run=" + built["run"] + "#" + fragment)
        page.wait_for_function(
            "document.querySelector('#selected-node').textContent.startsWith('Selected · ')"
        )
        assert page.locator("#selected-node").text_content() == "Selected · " + name
        assert built["name"] in page.title()
        page.goto(base + "?run=" + built["run"])
        page.locator(".native-result summary").click()
        refresh(page)
        assert page.locator(".native-result").evaluate("e=>e.open")
        page.goto(base + "?run=" + timeout["run"])
        assert (
            page.locator(".summary-head .status").get_attribute("data-status")
            == "timed-out"
        )
        assert (
            page.locator(".failure > .cause-what").text_content()
            == "root time limit reached"
        )
        capture(page, "observatory-inspector-timeout")

        # Phone: compact rows, details in the flow, no hidden inspector.
        mobile = browser.new_context(
            viewport={"width": 390, "height": 844},
            device_scale_factor=2,
            is_mobile=True,
            has_touch=True,
        )
        phone = mobile.new_page()
        phone.on("pageerror", lambda e: errors.append(str(e)))
        phone.goto(base)
        assert no_horizontal_overflow(phone)
        assert phone.locator(".campaign-table tbody tr").count() == min(roots, 100)
        heights = phone.locator('.campaign-table tr[data-status="already-valid"]').evaluate_all(
            "es=>es.map(e=>e.getBoundingClientRect().height)"
        )
        assert max(heights) < 40, heights
        assert phone.locator(".campaign-line button").evaluate_all(
            "es=>es.every(e=>e.getBoundingClientRect().right<=innerWidth)"
        )
        capture(phone, "observatory-index-mobile", full=True)
        phone.goto(base + "?run=" + built["run"])
        assert phone.locator(".phase-ledger").is_visible()
        assert no_horizontal_overflow(phone)
        assert wrapped(phone)
        capture(phone, "observatory-inspector-mobile")
        phone.goto(base + "?run=" + failed["run"])
        assert phone.locator(".failure").is_visible()
        assert no_horizontal_overflow(phone)
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
