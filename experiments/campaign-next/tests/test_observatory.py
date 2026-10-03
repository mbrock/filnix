"""Read-only browser regressions against a served, representative recording.

Requires a campaign with at least 50 sessions, a built session with captured
output and more than 500 static inputs. No builds or database writes are issued.
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
        page.goto(base)
        state = page.evaluate("fetch('./api/state').then(r=>r.json())")
        assert len(state["sessions"]) >= 50, "Use a representative campaign"
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
        # Pause clones state; polling replaces it. Neither may reset its panes.
        page.get_by_role("button", name="Pause", exact=True).click()
        assert position(page, "#graph-scroll") == graph
        activity = page.locator(".log-activity").first
        activity_x = activity.bounding_box()["x"]
        scroll(page, "#log-scroll", -300)
        page.locator("#log-scroll").evaluate("e=>e.scrollLeft=160")
        output = position(page, "#log-scroll")
        assert output[0] > 0
        assert abs(activity.bounding_box()["x"] - activity_x) < 1
        page.wait_for_timeout(3500)
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
        page.wait_for_timeout(3500)
        assert position(page, "#graph-scroll") == graph, (
            "Poll must not re-jump the URL fragment"
        )
        assert page.locator("#graph-scroll").evaluate("e=>e===document.activeElement")

        page.set_viewport_size({"width": 1440, "height": 360})
        page.locator(".native-result summary").click()
        scroll(page, ".session-summary", 80)
        summary = position(page, ".session-summary")
        assert summary[1] > 0
        page.wait_for_timeout(2500)
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
