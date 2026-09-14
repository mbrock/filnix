"""Bounded HTML cursor readers. Raw byte offsets remain the source of truth."""

import re

from tagflow import attr, tag, text
from tagflow import htmx as hx

from .base import (
    BUTTON,
    FIELD,
    FOCUS,
    LINK,
    MUTED,
    build_name,
    bytes_,
    link,
    select,
    timestamp,
)
from .resources import BATCH, LIVE_LOG, LOG, LOG_STATUS

LIMIT = 2000
SIZES = {12: "text-xs", 14: "text-sm", 16: "text-base"}


def marked(value, query):
    at = 0
    for found in re.finditer(re.escape(query), value, re.IGNORECASE) if query else []:
        text(value[at : found.start()])
        with tag.mark(["bg-amber-200", "text-stone-900"]):
            text(found[0])
        at = found.end()
    text(value[at:])


def entries(result, view):
    names = {s["drv"]: s["name"] for s in result["sources"]}
    previous = None
    for entry in result["entries"]:
        source = names.get(entry["drv"]) or (
            entry["drv"].rsplit("/", 1)[-1][33:-4] if entry["drv"] else "nix"
        )
        with tag.div(
            [
                "sm:grid",
                "sm:grid-cols-[11rem_1fr]",
                "gap-x-3",
                "px-2",
                "py-0.5",
                "min-w-0",
            ],
            id="line-" + str(entry["offset"]),
            data_offset=entry["offset"],
        ):
            if not view.drv:
                with tag.span(
                    [
                        "text-emerald-200/50",
                        "truncate",
                        "select-none",
                        ["hidden", "sm:block"] if previous == source else "block",
                    ],
                    title=source,
                ):
                    text(build_name(source))
            with tag.pre(
                [
                    "m-0",
                    "font-mono",
                    "[font-size:inherit]",
                    "leading-[inherit]",
                    "min-w-0",
                    "sm:col-span-2" if view.drv else [],
                    ["whitespace-pre-wrap", "break-words"]
                    if view.wrap
                    else ["whitespace-pre", "w-max"],
                    "text-rose-200"
                    if entry["kind"] == "error"
                    else "text-emerald-200"
                    if entry["kind"] == "phase"
                    else "text-stone-200",
                ]
            ):
                marked(entry["text"], view.q)
        previous = source


def cursor(result, cid, view, count, live=False):
    aid = result["attempt"]["id"]
    if result["finished"] and not result["more"]:
        with tag.p(["px-2", "py-2", "text-stone-400"], data_log_end="true"):
            text("End of log")
            if live:
                with tag.a(
                    ["ml-3", "text-emerald-200"],
                    href=LIVE_LOG.url(view, cid=cid),
                    id="next-batch",
                ):
                    hx.refresh(
                        LIVE_LOG.url(view, cid=cid, part="reader"),
                        trigger="every 3s",
                        done=not view.follow,
                    )
                    attr("hx-target", "closest #log-reader")
                    attr("hx-select", "#log-reader")
                    attr("hx-swap", "outerHTML ignoreTitle:true")
                    text("Follow next batch")
        return
    url = LOG.url(
        view,
        cid=cid,
        aid=aid,
        direction="after",
        cursor=result["end"],
        count=count,
        part="chunk",
        live=int(live),
    )
    with tag.a(
        ["block", "px-2", "py-2", "text-emerald-200", "hover:underline"],
        href=url,
        id="log-cursor",
        data_cursor=result["end"],
    ):
        hx.read_cursor(
            url,
            select="#log-chunk > *",
            every=("100ms" if result["more"] else "2s") if view.follow else None,
        )
        text(
            "More output…"
            if result["more"]
            else "Waiting for output…"
            if view.follow
            else "Load newer output"
        )


def chunk(result, cid, view, count, live=False):
    with tag.div(id="log-chunk"):
        entries(result, view)
        if result["skipped"]:
            with tag.p(["px-2", "text-amber-200"]):
                text("A record exceeds the display limit; the raw log contains it.")
        cursor(result, cid, view, count, live)


def reader(result, campaign, view, *, live=False, chunk_only=False, count=0):
    cid, aid = campaign["id"], result["attempt"]["id"]
    if chunk_only:
        chunk(result, cid, view, count, live)
        return
    with tag.section(
        id="log-reader",
        data_follow=view.follow,
        data_live=int(live),
        data_attempt=aid,
        data_end=result["end"],
    ):
        tools(result, campaign, view, live=live)
        with tag.div(
            [
                "h-[calc(100dvh-15rem)]",
                "min-h-80",
                "overflow-auto",
                "bg-[#15251f]",
                "border",
                "border-stone-700",
                "font-mono",
                SIZES[view.size],
                "leading-5",
                "[overflow-anchor:none]",
            ],
            id="log-scroll",
            tabindex=0,
            aria_label="Build output",
        ):
            if result.get("searching"):
                with tag.p(["px-2", "py-2", "text-stone-200"]):
                    text("Looking for this build's earlier output… ")
                    text(bytes_(result["size"] - result["start"]) + " searched")
                url = LOG.url(
                    view, cid=cid, aid=aid, direction="before", cursor=result["start"]
                )
                with tag.a(
                    ["block", "px-2", "py-2", "text-emerald-200"],
                    href=url,
                    id="log-search",
                ):
                    hx.refresh(url, trigger="load delay:100ms, every 2s")
                    attr("hx-swap", "outerHTML ignoreTitle:true")
                    attr("hx-target", "closest #log-reader")
                    attr("hx-select", "#log-reader")
                    attr("hx-sync", "this:drop")
                    text("Continue searching earlier output")
            else:
                if not result["entries"]:
                    with tag.p(["px-2", "py-2", "text-stone-200"], id="log-empty"):
                        if view.drv and not any(
                            s["drv"] == view.drv for s in result["sources"]
                        ):
                            text(
                                "No build output was recorded for this package in this batch. "
                            )
                        elif not result["captured"]:
                            text("This batch has no captured diagnostic output. ")
                        else:
                            text("No output in this window. ")
                        with link(
                            LOG.url(view.with_(drv=""), cid=cid, aid=aid),
                            "text-emerald-200",
                        ):
                            text("Show all batch output")
                chunk(result, cid, view, count, live)


def tools(result, campaign, view, *, live=False):
    cid, aid = campaign["id"], result["attempt"]["id"]
    with tag.div(id="log-tools"):
        hx.refresh(
            LOG_STATUS.url(
                view, cid=cid, aid=aid, live=int(live), cursor=result["start"]
            ),
            trigger="every 3s",
            done=result["finished"] or not view.follow,
        )
        with tag.div(["flex", "items-center", "justify-between", "gap-2", "mb-2"]):
            with link(BATCH.url(view, cid=cid, aid=aid), LINK):
                text(
                    ("Build" if result["attempt"]["kind"] == "build" else "Plan")
                    + " · "
                    + aid[:8]
                )
            with tag.span([MUTED, "text-xs"]):
                if result["finished"]:
                    text("Finished · ")
                else:
                    text("Running · ")
                timestamp(result["attempt"]["created"])
        with tag.div(["flex", "flex-wrap", "items-center", "gap-2", "mb-2"]):
            with tag.form(
                ["flex", "gap-1", "min-w-0", "flex-1"],
                method="get",
                action=LOG.url(cid=cid, aid=aid),
            ):
                hx.navigate(
                    LOG.url(cid=cid, aid=aid), region="#workspace", indicator="#loading"
                )
                sources = {s["drv"]: s["name"] for s in result["sources"] if s["drv"]}
                with tag.select(
                    [FIELD, "w-full"], name="drv", aria_label="Build output source"
                ):
                    with tag.option(value="", selected=not view.drv):
                        text(
                            f"All batch output ({len(sources)} builds)"
                            if result["attempt"]["kind"] == "build"
                            else "Planning output"
                        )
                    if view.drv and view.drv not in sources:
                        with tag.option(value=view.drv, selected=True):
                            text(
                                build_name(view.drv.rsplit("/", 1)[-1][33:-4])
                                + " · no build output"
                            )
                    for drv, name in sources.items():
                        with tag.option(value=drv, selected=drv == view.drv):
                            text(build_name(name or drv.rsplit("/", 1)[-1][33:-4]))
                for key in ("follow", "wrap", "size", "transport"):
                    tag.input(type="hidden", name=key, value=getattr(view, key))
                with tag.button(BUTTON, type="submit"):
                    text("Show")
            toggle = LOG.url(
                view.with_(follow=0 if view.follow else 1),
                cid=cid,
                aid=aid,
                direction="before" if view.follow else "tail",
                cursor=result["end"] if view.follow else None,
                live=int(live),
            )
            with tag.a(
                [BUTTON, "text-emerald-800" if view.follow else []],
                href=toggle,
                id="log-toggle",
            ):
                hx.preview(toggle, region="#log-reader")
                attr("hx-replace-url", "true")
                text("Pause" if view.follow else "Resume")
            with tag.details("relative"):
                with tag.summary(
                    [FOCUS, "cursor-pointer", "px-2", "py-1"], aria_label="Log options"
                ):
                    text("•••")
                with tag.div(
                    [
                        "absolute",
                        "right-0",
                        "z-20",
                        "w-64",
                        "border",
                        "border-stone-300",
                        "bg-white",
                        "p-2",
                        "shadow-sm",
                    ]
                ):
                    with tag.form(
                        "space-y-2", method="get", action=LOG.url(cid=cid, aid=aid)
                    ):
                        hx.navigate(
                            LOG.url(cid=cid, aid=aid),
                            region="#workspace",
                            indicator="#loading",
                        )
                        tag.input(
                            FIELD,
                            type="search",
                            name="q",
                            value=view.q,
                            placeholder="Find in this window",
                            aria_label="Find in this log window",
                        )
                        select(
                            "size",
                            [(12, "12 px"), (14, "14 px"), (16, "16 px")],
                            view.size,
                            "Log font size",
                        )
                        select(
                            "wrap",
                            [(1, "Wrap lines"), (0, "Keep long lines")],
                            view.wrap,
                            "Line wrapping",
                        )
                        for key in ("drv", "transport"):
                            tag.input(type="hidden", name=key, value=getattr(view, key))
                        tag.input(type="hidden", name="follow", value=0)
                        tag.input(type="hidden", name="direction", value="before")
                        tag.input(type="hidden", name="cursor", value=result["end"])
                        with tag.button(BUTTON, type="submit"):
                            text("Apply")
                    with tag.a(
                        [LINK, "block", "mt-2"], href="/api/log/download?attempt=" + aid
                    ):
                        text("Download raw log ↓")
        with tag.div(["flex", "justify-between", "gap-2", MUTED, "text-xs", "mb-1"]):
            if result["before"]:
                with link(
                    LOG.url(
                        view.with_(follow=0),
                        cid=cid,
                        aid=aid,
                        direction="before",
                        cursor=result["start"],
                    ),
                    LINK,
                ):
                    text("← Earlier output")
            else:
                with tag.span():
                    text("Start of log")
            with tag.span():
                text(bytes_(result["captured"]) + " captured")
