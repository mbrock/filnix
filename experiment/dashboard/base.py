"""Shared typography, navigation and small HTML components."""

from contextlib import contextmanager
from datetime import datetime, timezone
from functools import cache
from hashlib import sha256
from pathlib import Path

from tagflow import htmx as hx
from tagflow import tag, text

from .. import VERSION
from .resources import ACTIVITY, BATCHES, EVENTS, GRAPH, LIVE_LOG, PACKAGES, View

FOCUS = [
    "focus-visible:outline-2",
    "focus-visible:outline-offset-2",
    "focus-visible:outline-sky-700",
]
LINK = [FOCUS, "text-sky-800", "hover:underline", "underline-offset-2"]
MUTED = ["text-stone-500"]
BUTTON = [
    FOCUS,
    "inline-flex",
    "items-center",
    "border",
    "border-stone-300",
    "rounded-sm",
    "px-2",
    "py-1",
    "hover:bg-stone-100",
]
FIELD = [
    FOCUS,
    "min-w-0",
    "border",
    "border-stone-300",
    "rounded-sm",
    "bg-white",
    "px-2",
    "py-1",
    "text-base",
    "sm:text-sm",
]
ROW = ["border-b", "border-stone-200"]
CELL = ["px-2", "py-1.5", "align-top"]
HEADING = ["font-semibold", "text-left"]
STATES = {
    "ready": ("Ready", ["text-stone-500"]),
    "built": ("Built", ["text-stone-400"]),
    "awaiting-result": ("Awaiting result", MUTED),
    "build-result-unknown": ("Result not recorded", MUTED),
    "starting": ("Starting", ["text-sky-800"]),
    "finished": ("Finished", ["text-emerald-800"]),
    "finished-errors": ("Finished · errors", ["text-red-800"]),
    "cancelled": ("Cancelled", ["text-amber-800"]),
    "interrupted": ("Interrupted", ["text-amber-800"]),
    "timed-out": ("Timed out", ["text-amber-800"]),
    "resource-limit": ("Resource limit", ["text-amber-800"]),
    "result-unknown": ("Finished · outcome unknown", MUTED),
    "available": ("Built", ["text-stone-400"]),
    "tested": ("Tested", ["text-emerald-800", "font-medium"]),
    "failed": ("Failed", ["text-red-800"]),
    "error": ("With errors", ["text-red-800"]),
    "evaluation-error": ("Eval error", ["text-red-800"]),
    "blocked": ("Blocked", ["text-amber-800"]),
    "inconclusive": ("Inconclusive", ["text-amber-800"]),
    "excluded": ("Excluded", MUTED),
    "running": ("Running", ["text-sky-800"]),
    "building": ("Building", ["text-sky-800"]),
    "active": ("Running", ["text-sky-800"]),
    "complete": ("Completed", ["text-emerald-800"]),
    "queued": ("Queued", MUTED),
    "unplanned": ("Not tried", MUTED),
}


def status(value, checked=False):
    value = "tested" if checked and value == "available" else value
    label, classes = STATES.get(value, (value.capitalize(), MUTED))
    with tag.span(classes, data_status=value):
        text(label)


@contextmanager
def link(url, classes=LINK, navigate=True, **attrs):
    with tag.a(classes, href=url, **attrs):
        if navigate:
            hx.navigate(url, region="#workspace", indicator="#loading")
        yield


def build_name(value):
    return (value or "").replace("-x86_64-unknown-linux-gnufilc0", "")


def duration(seconds):
    if seconds is None:
        return "—"
    seconds = max(0, int(seconds))
    if seconds >= 3600:
        return f"{seconds // 3600}h {seconds % 3600 // 60:02d}m"
    return f"{seconds // 60}m {seconds % 60:02d}s" if seconds >= 60 else f"{seconds}s"


def timestamp(value, date=True):
    if value is None:
        text("—")
        return
    instant = datetime.fromtimestamp(value, timezone.utc)
    with tag.time(
        datetime=instant.isoformat(), title=instant.strftime("%Y-%m-%d %H:%M:%S UTC")
    ):
        text(instant.strftime("%d %b %H:%M" if date else "%H:%M:%S"))


def bytes_(value):
    return (
        f"{value / 1024**2:.1f} MiB" if value >= 1024**2 else f"{value / 1024:.0f} KiB"
    )


@cache
def asset(name):
    p = Path(__file__).parent / "static" / name
    return "/assets/" + name + "?v=" + sha256(p.read_bytes()).hexdigest()[:12]


def shell(title, campaign, campaigns, view, section, content):
    cid = campaign["id"]
    with tag.html(lang="en"):
        with tag.head():
            tag.meta(charset="utf-8")
            tag.meta(name="viewport", content="width=device-width, initial-scale=1")
            tag.meta(
                name="htmx-config",
                content='{"noSwap":[204,304,"4xx","5xx"],"allowEval":false,"allowScriptTags":false}',
            )
            with tag.title():
                text(f"{title} · filnix")
            tag.link(rel="icon", href=asset("favicon.svg"), type="image/svg+xml")
            tag.link(rel="stylesheet", href=asset("dashboard.css"))
            for name in ("htmx-4.0.0.min.js", "hx-sse-4.0.0.min.js", "reader.js"):
                tag.script(src=asset(name), defer=True)
        with tag.body(
            [
                "bg-[#f7f7f2]",
                "text-stone-900",
                "font-sans",
                "text-sm",
                "leading-5",
                "antialiased",
                "[text-size-adjust:100%]",
                "[-webkit-text-size-adjust:100%]",
            ]
        ):
            with tag.div(id="workspace", data_campaign=cid, data_view=section):
                # Navigating to another page/campaign intentionally replaces this
                # connection. Every automatically refreshed region is below it.
                if view.transport == "sse":
                    with tag.div(id="campaign-events", hx_swap="none"):
                        hx.connect(EVENTS.url(cid=cid), close_on="campaign-complete")
                with tag.header(["border-b", "border-stone-300"]):
                    with tag.div(["max-w-[96rem]", "mx-auto", "px-3", "sm:px-5"]):
                        with tag.div(["flex", "items-center", "gap-3", "py-2"]):
                            with link(
                                ACTIVITY.url(view, cid=cid),
                                [
                                    FOCUS,
                                    "font-bold",
                                    "text-lg",
                                    "tracking-tight",
                                    "shrink-0",
                                ],
                            ):
                                text("filnix")
                                with tag.span("text-orange-700"):
                                    text(".")
                            with tag.details(
                                ["min-w-0", "flex-1", "relative"], id="campaign-menu"
                            ):
                                with tag.summary([FOCUS, "cursor-pointer", "truncate"]):
                                    text(campaign["name"])
                                with tag.div(
                                    [
                                        "absolute",
                                        "z-40",
                                        "left-0",
                                        "top-full",
                                        "mt-1",
                                        "w-72",
                                        "max-w-[80vw]",
                                        "border",
                                        "border-stone-300",
                                        "bg-white",
                                        "shadow-sm",
                                        "p-2",
                                    ]
                                ):
                                    for c in campaigns:
                                        with link(
                                            ACTIVITY.url(
                                                View(transport=view.transport),
                                                cid=c["id"],
                                            ),
                                            [LINK, "block", "py-1"],
                                        ):
                                            text(c["name"])
                                            if c["mode"] == "running":
                                                text(" · running")
                                    with tag.p([MUTED, "mt-2", "text-xs"]):
                                        text("Source " + campaign["revision"][:12])
                            with tag.span([MUTED, "hidden", "sm:inline"]):
                                text(campaign["mode"])
                            with link(
                                LIVE_LOG.url(view, cid=cid), [BUTTON, "shrink-0"]
                            ):
                                text("Live log")
                        with tag.nav(
                            [
                                "flex",
                                "gap-3",
                                "sm:gap-4",
                                "overflow-x-auto",
                                "whitespace-nowrap",
                                "relative",
                            ],
                            aria_label="Campaign",
                        ):
                            for key, label, resource in [
                                ("activity", "Activity", ACTIVITY),
                                ("packages", "Packages", PACKAGES),
                                ("batches", "Batches", BATCHES),
                                ("dependencies", "Dependencies", GRAPH),
                            ]:
                                v = View(transport=view.transport)
                                classes = [
                                    FOCUS,
                                    "py-1.5",
                                    "border-b-2",
                                    ["border-stone-900", "font-medium"]
                                    if key == section
                                    else ["border-transparent", MUTED],
                                ]
                                with link(
                                    resource.url(v, cid=cid),
                                    classes,
                                    aria_current="page" if key == section else None,
                                ):
                                    text(label)
                            with tag.span(
                                [
                                    "htmx-indicator",
                                    "absolute",
                                    "right-0",
                                    "bg-[#f7f7f2]",
                                    "px-2",
                                    "pointer-events-none",
                                    MUTED,
                                ],
                                id="loading",
                                role="status",
                            ):
                                text("Loading…")
                with tag.p(
                    ["text-amber-800", "px-3", "sm:px-5", "py-1", "text-xs"],
                    id="connection-status",
                    role="status",
                    hidden=True,
                ):
                    text(
                        "Could not load new data. Automatic updates will retry; you can also reload."
                    )
                with tag.main(
                    ["max-w-[96rem]", "mx-auto", "px-3", "sm:px-5", "py-3"],
                    id="content",
                ):
                    content()
                with tag.footer(
                    [
                        "max-w-[96rem]",
                        "mx-auto",
                        "px-3",
                        "sm:px-5",
                        "py-3",
                        "flex",
                        "gap-3",
                        MUTED,
                        "text-xs",
                    ]
                ):
                    text("filnix " + VERSION + " · UTC")
                    with tag.a(LINK, href="https://github.com/mbrock/filnix"):
                        text("Source")
                    with tag.a(
                        LINK,
                        href="https://github.com/lessrest/tagflow/tree/aa07b0d7eec0b72a5dbc6a8d0ee1098c68b74d09",
                    ):
                        text("Tagflow")


def select(name, choices, current, label):
    with tag.label(["inline-flex", "items-center", "gap-2"]):
        with tag.span("sr-only"):
            text(label)
        with tag.select(FIELD, name=name, aria_label=label):
            for value, title in choices:
                with tag.option(value=value, selected=value == current):
                    text(title)


def empty(message):
    with tag.p([MUTED, "py-6"]):
        text(message)
