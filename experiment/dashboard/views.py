"""Campaign, package, batch and dependency representations."""

from tagflow import attr, tag, text
from tagflow import htmx as hx

from .base import (
    BUTTON,
    CELL,
    FIELD,
    FOCUS,
    HEADING,
    LINK,
    MUTED,
    ROW,
    build_name,
    duration,
    empty,
    link,
    select,
    status,
    timestamp,
)
from .resources import (
    ACTIVITY,
    ACTIVITY_FEED,
    BATCH,
    BATCH_STATUS,
    BATCHES,
    BLOCKERS,
    CSV,
    GRAPH,
    GRAPH_REGION,
    LOG,
    PACKAGE,
    PACKAGES,
    SUMMARY,
    UPDATES,
)


def summary(value, view):
    c, counts = value["campaign"], value["counts"]
    cid = c["id"]
    with tag.section(
        id="summary", aria_label="Campaign progress", data_revision=value["revision"]
    ):
        hx.refresh(SUMMARY.url(view, cid=cid), trigger=view.trigger, done=value["done"])
        if c["mode"] == "running" and (
            c["heartbeat"] is None or value["now"] - c["heartbeat"] >= 30
        ):
            with tag.p(["text-amber-800", "mb-2"], role="status"):
                text("Controller has stopped reporting. Last update: ")
                timestamp(c["heartbeat"])
        if c["hold"]:
            with tag.p(["text-amber-800", "mb-2"], role="status"):
                text(c["hold"])
        with tag.div(["grid", "grid-cols-4", "gap-3", "pb-2"]):
            for state, label, number in [
                ("available", "Built", counts.get("available", 0)),
                ("tested", "Tested", value["tested"]),
                ("failed", "Failed", counts.get("failed", 0)),
                ("blocked", "Blocked", counts.get("blocked", 0)),
            ]:
                with link(
                    PACKAGES.url(view.with_(state=state), cid=cid), [FOCUS, "block"]
                ):
                    with tag.div(
                        ["text-xl", "tabular-nums", "leading-6", "font-medium"]
                    ):
                        text(f"{number:,}")
                    status(state)
        evaluated = value["total"] - counts.get("unplanned", 0)
        with tag.div(
            ["flex", "flex-wrap", "gap-x-4", "gap-y-1", MUTED, "text-xs", "pb-2"]
        ):
            with tag.span():
                text(f"{evaluated:,} / {value['total']:,} evaluated")
            with link(
                PACKAGES.url(view.with_(state="evaluation-error"), cid=cid),
                [FOCUS, "hover:underline"],
            ):
                text(f"{counts.get('evaluation-error', 0):,} eval errors")
            with tag.span():
                text(f"{counts.get('queued', 0):,} queued")
            if value["done"]:
                text("Queue complete")
            elif c["mode"] != "running":
                text(c["mode"].capitalize())
        with tag.svg(
            ["w-full", "h-1.5", "mb-2"],
            viewBox="0 0 1000 4",
            preserveAspectRatio="none",
            role="img",
            aria_label=f"{evaluated} of {value['total']} evaluated",
        ):
            tag.rect(x=0, y=0, width=1000, height=4, fill="#e7e5e4")
            at = 0
            for key, color in [
                ("available", "#306b50"),
                ("blocked", "#ac965b"),
                ("failed", "#b76a46"),
                ("evaluation-error", "#b76a46"),
                ("running", "#346a90"),
                ("queued", "#98a9b3"),
            ]:
                width = counts.get(key, 0) / max(value["total"], 1) * 1000
                tag.rect(x=at, y=0, width=width, height=4, fill=color)
                at += width
        build_monitor(value, view)
        if value["blockers"]:
            top_blockers(value["blockers"], cid, view)


def monitor_node(node, cid, aid, view):
    with tag.div(
        ["flex", "flex-wrap", "items-baseline", "gap-x-3", "min-w-0", "py-0.5"],
        data_drv=node["drv"],
        data_state=node["state"],
    ):
        symbols = {
            "building": "●",
            "awaiting-result": "◇",
            "available": "✓",
            "failed": "!",
            "excluded": "−",
        }
        with tag.span([MUTED, "w-3", "shrink-0"], aria_hidden="true"):
            text(symbols.get(node["state"], "○"))
        with link(
            GRAPH.url(view.with_(focus=node["drv"], page=0), cid=cid),
            [
                FOCUS,
                "min-w-0",
                "flex-1",
                "basis-1/2",
                "sm:basis-auto",
                "truncate",
                "font-medium",
            ],
            title=build_name(node["name"]),
        ):
            text(build_name(node["name"]))
        with tag.span(
            ["text-xs", "shrink-0", "sm:w-36", "sm:text-right"],
            data_status=node["state"],
        ):
            if node["state"] == "building":
                with tag.span("text-sky-800"):
                    text((node["phase"] or "building").removesuffix("Phase"))
            elif node["state"] == "waiting":
                with tag.span(MUTED):
                    text("waiting / resolving")
            else:
                status(node["state"])
        if node["elapsed"] is not None:
            with tag.span(
                [
                    MUTED,
                    "text-xs",
                    "tabular-nums",
                    "shrink-0",
                    "sm:w-16",
                    "sm:text-right",
                ],
                title="Observed build activity time",
            ):
                text(duration(node["elapsed"]))
        with link(
            LOG.url(view.with_(drv=node["drv"]), cid=cid, aid=aid),
            [LINK, "text-xs", "shrink-0"],
        ):
            text("log")


def monitor_tree(tree, nodes, cid, aid, view):
    with tag.ul(["border-l", "border-stone-300", "ml-1.5", "pl-3"]):
        for drv, children in tree.items():
            with tag.li():
                monitor_node(nodes[drv], cid, aid, view)
                if children:
                    monitor_tree(children, nodes, cid, aid, view)


def build_monitor(value, view):
    cid = value["campaign"]["id"]
    with tag.section(
        ["mb-3"], id="build-monitor", aria_label="Live build dependency forest"
    ):
        with tag.div(["flex", "justify-between", "gap-2", "items-baseline", "mb-1"]):
            with tag.h1(HEADING):
                text("Build monitor")
            with link(GRAPH.url(view, cid=cid), [LINK, "text-xs"]):
                text("Explore dependencies →")
        for group in value["monitor"]:
            a, tree = group["request"], group["tree"]
            single = len(a["targets"]) == 1
            with tag.div(
                [ROW, "py-1"], id="active-" + a["id"], data_roots=len(a["targets"])
            ):
                with tag.div(
                    ["flex", "items-baseline", "gap-2", "min-w-0", "text-xs", MUTED]
                ):
                    with link(
                        BATCH.url(view, cid=cid, aid=a["id"]),
                        [LINK, "truncate", "min-w-0"],
                    ):
                        text(f"{len(a['targets'])} root{'s' if not single else ''}")
                        if not single:
                            text(
                                " · "
                                + ", ".join(t["label"] for t in a["targets"][:3])
                                + "…"
                            )
                    with tag.span(
                        "shrink-0",
                        title="Request placement, not measured builder utilization",
                    ):
                        text(a["location"] + " request")
                    with tag.span(
                        ["ml-auto", "tabular-nums", "shrink-0"],
                        title="Time since request admission, not build time",
                    ):
                        text("request " + duration(value["now"] - a["created"]))
                    with link(LOG.url(view, cid=cid, aid=a["id"]), [LINK, "shrink-0"]):
                        text("log")
                if single:
                    drv = a["targets"][0]["drv"]
                    monitor_node(group["nodes"][drv], cid, a["id"], view)
                    if tree.get(drv):
                        monitor_tree(tree[drv], group["nodes"], cid, a["id"], view)
                elif tree:
                    monitor_tree(tree, group["nodes"], cid, a["id"], view)
                if group["detached"]:
                    with tag.div([MUTED, "text-xs", "mt-1"]):
                        text(
                            "Other observed activity · dependency path outside this view"
                        )
                    for node in group["detached"]:
                        monitor_node(node, cid, a["id"], view)
                if group["settling"]:
                    with tag.details(id="settling-" + a["id"]):
                        with tag.summary([FOCUS, MUTED, "text-xs", "cursor-pointer"]):
                            text(
                                f"{len(group['settling'])} recent stopped activities · awaiting results"
                            )
                        for node in group["settling"]:
                            monitor_node(node, cid, a["id"], view)
                if not single and group["hidden_roots"]:
                    with tag.details(id="pending-" + a["id"]):
                        with tag.summary([FOCUS, MUTED, "text-xs", "cursor-pointer"]):
                            text(f"{len(group['hidden_roots'])} other requested roots")
                        with tag.div(
                            ["flex", "flex-wrap", "gap-x-3", "text-xs", "py-1"]
                        ):
                            for node in group["hidden_roots"]:
                                with link(
                                    GRAPH.url(
                                        view.with_(focus=node["drv"], page=0), cid=cid
                                    )
                                ):
                                    text(build_name(node["name"]))
        planners = [a for a in value["active"] if a["kind"] == "plan"]
        for a in planners:
            with tag.div(
                [ROW, "flex", "gap-3", "py-1", "text-xs", MUTED], id="active-" + a["id"]
            ):
                with link(BATCH.url(view, cid=cid, aid=a["id"]), LINK):
                    text(f"Planning · {len(a['targets'])} roots")
                with tag.span(["truncate", "min-w-0", "flex-1"]):
                    text(", ".join(t["label"] for t in a["targets"][:3]))
                with link(
                    LOG.url(view, cid=cid, aid=a["id"]),
                    [LINK, "shrink-0", "tabular-nums"],
                ):
                    text(duration(value["now"] - a["created"]))
        if not value["monitor"]:
            with tag.p([MUTED, "py-2"]):
                text(
                    "No active build requests. "
                    + ("Planning the next roots." if planners else "The queue is idle.")
                )
        with tag.p([MUTED, "text-xs", "mt-1"]):
            text(
                "Partial dependency view · shared dependencies shown once per request · stopped ≠ succeeded"
            )


def top_blockers(rows, cid, view):
    with tag.section(["mb-3"], id="top-blockers", aria_label="Top blockers"):
        with tag.div(["flex", "justify-between", "gap-2"]):
            with tag.h2(HEADING):
                text("Top blockers")
            with link(BLOCKERS.url(view.with_(page=0), cid=cid)):
                text("All blockers →")
        for row in rows:
            with tag.div([ROW, "flex", "gap-2", "justify-between", "py-1", "min-w-0"]):
                with tag.span(["min-w-0", "truncate"]):
                    with link(
                        GRAPH.url(view.with_(focus=row["drv"], page=0), cid=cid),
                        [FOCUS, "font-medium"],
                    ):
                        text(blocker_name(row))
                    with tag.span([MUTED, "ml-2"]):
                        text(failure_label(row["failure"]))
                with tag.span(["shrink-0", "tabular-nums", "text-amber-800"]):
                    text(f"blocks {row['blocks']:,}")
                    if row["only"]:
                        with tag.span(MUTED):
                            text(f" · only cause of {row['only']:,}")


def timeline(rows, cid, view, now):
    rows = [r for r in rows if r["duration"] is not None]
    if not rows:
        return
    start = min(r["created"] for r in rows)
    end = max((r["finished"] or now) for r in rows)
    span = max(end - start, 1)
    with tag.div(
        ["grid", "grid-cols-[3rem_1fr]", "gap-x-2", "gap-y-1", "items-center", "my-3"],
        id="timeline",
        data_sampled=now,
    ):
        for kind, label in [("build", "Build"), ("plan", "Plan")]:
            lanes, positions = [], []
            for row in sorted(
                (r for r in rows if r["kind"] == kind),
                key=lambda r: (r["created"], r["id"]),
            ):
                lane = next(
                    (i for i, until in enumerate(lanes) if until <= row["created"]),
                    len(lanes),
                )
                finish = row["finished"] or now
                if lane == len(lanes):
                    lanes.append(finish)
                else:
                    lanes[lane] = finish
                positions.append((row, lane, finish))
            with tag.div([MUTED, "text-xs"]):
                text(label)
            with tag.svg(
                ["w-full"],
                height=max(12, len(lanes) * 9),
                viewBox=f"0 0 1000 {max(12, len(lanes) * 9)}",
                preserveAspectRatio="none",
                role="img",
                aria_label=label + " timeline",
            ):
                for lane in range(max(1, len(lanes))):
                    tag.rect(x=0, y=lane * 9, width=1000, height=7, fill="#e7e5e4")
                for row, lane, finish in positions:
                    x = (row["created"] - start) / span * 1000
                    width = max(0.5, (finish - row["created"]) / span * 1000)
                    color = {
                        "error": "#b76a46",
                        "active": "#346a90",
                        "complete": "#638b70",
                    }.get(row["outcome"], "#a8a29e")
                    with tag.a(
                        href=BATCH.url(view, cid=cid, aid=row["id"]),
                        data_batch=row["id"],
                        data_lane=lane,
                    ):
                        with tag.rect(
                            x=round(x, 2),
                            y=lane * 9,
                            width=round(width, 2),
                            height=7,
                            fill=color,
                        ):
                            with tag.title():
                                text(
                                    ", ".join(row["roots"][:4])
                                    + " · "
                                    + duration(row["duration"])
                                )
        with tag.div():
            pass
        with tag.div(["flex", "justify-between", MUTED, "text-xs"]):
            timestamp(start)
            timestamp(end)


def updates(cid, view, seen, current, target, done=False):
    with tag.span(id="updates", data_revision=current):
        hx.refresh(
            UPDATES.url(
                view,
                cid=cid,
                seen=seen,
                target=target,
                state=view.state,
                kind=view.kind,
                outcome=view.outcome,
                sort=view.sort,
                q=view.q,
            ),
            trigger=view.trigger,
            done=done,
        )
        resource = (
            PACKAGES
            if target == "packages"
            else BATCHES
            if target == "batches"
            else ACTIVITY
        )
        with link(resource.url(view, cid=cid), LINK):
            text("Updates · refresh" if current > seen else "Refresh")


def batch_rows(rows, cid, view):
    with tag.table(["w-full", "table-fixed", "border-collapse"]):
        with tag.thead(["border-b", "border-stone-400"]):
            with tag.tr():
                with tag.th([CELL, HEADING], scope="col"):
                    text("Batch")
                with tag.th(
                    [CELL, "text-right", "font-medium", "w-20", "sm:w-24"], scope="col"
                ):
                    text("Result")
                with tag.th(
                    [CELL, "text-right", "font-medium", "w-16", "sm:w-20"], scope="col"
                ):
                    text("Time")
        with tag.tbody():
            for r in rows:
                with tag.tr(ROW, id="batch-" + r["id"]):
                    with tag.td(CELL):
                        with link(
                            BATCH.url(view, cid=cid, aid=r["id"]),
                            [FOCUS, "line-clamp-2", "break-words"],
                        ):
                            text(", ".join(r["roots"]) or r["id"][:8])
                        with tag.div(
                            [MUTED, "text-xs", "flex", "flex-wrap", "gap-x-2"]
                        ):
                            text("Build" if r["kind"] == "build" else "Plan")
                            timestamp(r["created"])
                            if r["tested"]:
                                text(f"{r['tested']} tested")
                    with tag.td([CELL, "text-right"]):
                        with link(LOG.url(view, cid=cid, aid=r["id"]), FOCUS):
                            status(r["status"])
                    with tag.td(
                        [CELL, "text-right", "tabular-nums", "whitespace-nowrap"]
                    ):
                        text(duration(r["duration"]))


def activity(value, ledger, view):
    summary(value, view)
    activity_feed(ledger, value["campaign"], view)


def activity_feed(ledger, campaign, view):
    cid = campaign["id"]
    with tag.section(
        id="activity-feed", data_sampled=ledger["now"], data_watch=view.watch
    ):
        hx.refresh(
            ACTIVITY_FEED.url(view, cid=cid),
            trigger=view.trigger,
            done=ledger["done"] or not view.watch,
        )
        with tag.div(["flex", "justify-between", "items-center", "gap-2", "mb-1"]):
            with tag.h2(HEADING):
                text("Recent build requests")
            with tag.div(["flex", "gap-2", "items-center", MUTED, "text-xs"]):
                with tag.span():
                    text(
                        "Complete · "
                        if ledger["done"]
                        else "Live · "
                        if view.watch
                        else "Paused · "
                    )
                    timestamp(ledger["now"], date=False)
                if not ledger["done"]:
                    url = ACTIVITY.url(
                        view.with_(watch=0 if view.watch else 1), cid=cid
                    )
                    with tag.a(LINK, href=url, id="activity-toggle"):
                        hx.preview(url, region="#activity-feed")
                        attr("hx-replace-url", "true")
                        text("Pause" if view.watch else "Follow")
        recent = [
            r
            for r in ledger["rows"]
            if r["kind"] == "build" and r["state"] == "finished"
        ][:8]
        if recent:
            with tag.div(["grid", "md:grid-cols-2", "gap-x-5"], id="recent-builds"):
                for row in recent:
                    with tag.div(
                        [ROW, "flex", "gap-3", "py-1", "items-baseline", "min-w-0"]
                    ):
                        with link(
                            BATCH.url(view, cid=cid, aid=row["id"]),
                            [LINK, "truncate", "min-w-0", "flex-1"],
                        ):
                            text(", ".join(build_name(r) for r in row["roots"]))
                        with tag.span(["text-xs", "shrink-0"]):
                            status(row["status"])
                        with link(
                            LOG.url(view, cid=cid, aid=row["id"]),
                            [LINK, "text-xs", "tabular-nums", "shrink-0"],
                        ):
                            text(duration(row["duration"]))
        else:
            with tag.p([MUTED, "py-1"]):
                text("No finished build requests yet.")
        with tag.details(["mt-2", "mb-3"], id="request-history"):
            with tag.summary([FOCUS, MUTED, "cursor-pointer", "text-xs"]):
                text(
                    f"Request history · latest {min(40, len(ledger['rows'])):,} of {ledger['total']:,} requests"
                )
            timeline(ledger["rows"][:40], cid, view, ledger["now"])
            batch_rows(ledger["rows"][:40], cid, view)
            with link(BATCHES.url(view, cid=cid), [LINK, "inline-block", "mt-2"]):
                text("Full request ledger →")


def snapshot_notice(result, cid, view, target):
    with tag.div(["flex", "justify-between", "gap-2", MUTED, "text-xs", "mb-2"]):
        with tag.span():
            text("Snapshot · ")
            timestamp(result.get("sampled", result.get("now")), date=False)
        revision = result.get("revision", result.get("cursor"))
        updates(cid, view, revision, revision, target, result["done"])


def packages(result, campaign, view):
    cid = campaign["id"]
    with tag.div(["flex", "items-center", "justify-between", "gap-2", "mb-2"]):
        with tag.form(
            ["flex", "gap-2", "items-center"],
            action=PACKAGES.url(cid=cid),
            method="get",
        ):
            hx.navigate(
                PACKAGES.url(cid=cid), region="#workspace", indicator="#loading"
            )
            select(
                "state",
                [
                    ("available", "Built"),
                    ("tested", "Tested"),
                    ("failed", "Build failures"),
                    ("failures", "All failures"),
                    ("evaluation-error", "Evaluation errors"),
                    ("blocked", "Blocked"),
                    ("tried", "All tried"),
                    ("all", "Entire inventory"),
                ],
                view.state,
                "Package results",
            )
            tag.input(type="hidden", name="transport", value=view.transport)
            with tag.button(BUTTON, type="submit"):
                text("Show")
        with tag.details("relative"):
            with tag.summary(
                [FOCUS, "cursor-pointer", "px-2", "py-1"], aria_label="Package options"
            ):
                text("•••")
            with tag.div(
                [
                    "absolute",
                    "right-0",
                    "z-20",
                    "bg-white",
                    "border",
                    "border-stone-300",
                    "p-2",
                    "whitespace-nowrap",
                ]
            ):
                with tag.div():
                    with link(CSV.url(view, cid=cid), LINK, navigate=False):
                        text("CSV ↓")
        with tag.span([MUTED, "tabular-nums"]):
            text(f"{len(result['rows']):,}")
    snapshot_notice(result, cid, view, "packages")
    if not result["rows"]:
        empty("No packages in this result set yet.")
        return
    with tag.table(
        ["w-full", "table-fixed", "border-collapse"],
        id="package-list",
        data_count=len(result["rows"]),
    ):
        with tag.thead(
            ["sticky", "top-0", "bg-[#f7f7f2]", "border-b", "border-stone-400", "z-10"]
        ):
            with tag.tr():
                with tag.th([CELL, HEADING], scope="col"):
                    text("Package")
                with tag.th(
                    [CELL, "text-right", "font-medium", "w-20", "sm:w-24"], scope="col"
                ):
                    text("Result")
        with tag.tbody():
            for row in result["rows"]:
                with tag.tr(ROW, id="package-" + str(row["id"])):
                    with tag.td(CELL):
                        with link(
                            PACKAGE.url(view, cid=cid, pid=row["id"]),
                            [FOCUS, "font-medium", "break-words"],
                        ):
                            text(row["label"])
                        with tag.span([MUTED, "ml-2", "break-words"]):
                            text(row["version"])
                        if row["description"]:
                            with tag.div(["text-stone-600", "break-words"]):
                                text(row["description"])
                    with tag.td([CELL, "text-right"]):
                        with tag.span(title=row["reason"] or None):
                            status(row["state"], bool(row["checks"]))


def batches(result, campaign, view):
    cid = campaign["id"]
    with tag.div(["flex", "justify-between", "gap-2", "mb-2"]):
        with tag.h1(HEADING):
            text(f"{len(result['rows']):,} batches")

    with tag.form(
        ["flex", "flex-wrap", "gap-2", "mb-3"],
        method="get",
        action=BATCHES.url(cid=cid),
    ):
        hx.navigate(BATCHES.url(cid=cid), region="#workspace", indicator="#loading")
        tag.input(
            [FIELD, "w-full", "sm:w-64"],
            type="search",
            name="q",
            value=view.q,
            placeholder="Batch or package",
            aria_label="Find a batch or package",
        )
        select(
            "kind",
            [("", "Builds + plans"), ("build", "Builds"), ("plan", "Plans")],
            view.kind,
            "Job type",
        )
        select(
            "outcome",
            [
                ("", "All results"),
                ("error", "Finished with errors"),
                ("active", "Running"),
                ("complete", "Finished normally"),
            ],
            view.outcome,
            "Batch results",
        )
        select(
            "sort",
            [
                ("recent", "Latest first"),
                ("longest", "Longest first"),
                ("oldest", "Oldest first"),
            ],
            view.sort,
            "Batch order",
        )
        tag.input(type="hidden", name="transport", value=view.transport)
        with tag.button(BUTTON, type="submit"):
            text("Apply")
    snapshot_notice(result, cid, view, "batches")
    timeline(result["rows"], cid, view, result["now"])
    if result["rows"]:
        batch_rows(result["rows"], cid, view)
    else:
        empty("No batches match these filters.")


def batch_status(result, campaign, view, now):
    cid, aid = campaign["id"], result["id"]
    with tag.section(id="batch-status"):
        hx.refresh(
            BATCH_STATUS.url(view, cid=cid, aid=aid),
            trigger=view.trigger,
            done=result["state"] == "finished",
        )
        with tag.div(
            [
                "flex",
                "gap-x-3",
                "gap-y-1",
                "items-center",
                "flex-wrap",
                "mb-2",
                "sticky",
                "top-0",
                "z-10",
                "bg-[#f7f7f2]",
                "border-b",
                "border-stone-300",
                "py-2",
            ],
            id="batch-heading",
        ):
            with tag.h1(HEADING):
                text(
                    ("Build" if result["kind"] == "build" else "Plan") + " · " + aid[:8]
                )
            status(result["status"])
            with tag.span("tabular-nums"):
                text(
                    duration(
                        (result["finished"] - result["created"])
                        if result["finished"] is not None
                        else (now - result["created"])
                        if result["state"] != "finished"
                        else None
                    )
                )
            with link(LOG.url(view, cid=cid, aid=aid), BUTTON):
                text("Batch log")
            if result["state"] != "finished":
                with tag.span(MUTED):
                    text(f"{result['activity_counts'].get('building', 0)} building")
        with tag.p([MUTED, "mb-3"]):
            text("Started ")
            timestamp(result["created"])
            if result["finished"] is not None:
                text(" · Finished ")
                timestamp(result["finished"])
        if result["error"]:
            with tag.pre(
                [
                    "whitespace-pre-wrap",
                    "break-words",
                    "text-red-800",
                    "mb-3",
                    "font-sans",
                ]
            ):
                text(result["error"])
        with tag.details("mb-3"):
            with tag.summary([FOCUS, HEADING, "cursor-pointer"]):
                text(f"Requested packages · {len(result['targets'])}")
            with tag.ul(["columns-1", "sm:columns-2", "lg:columns-3"]):
                for root in result["targets"]:
                    with tag.li(["break-inside-avoid", "py-0.5"]):
                        url = (
                            PACKAGE.url(view, cid=cid, pid=root["id"])
                            if "id" in root
                            else GRAPH.url(view.with_(focus=root["drv"]), cid=cid)
                        )
                        with link(url):
                            text(root["label"])
        if result["activities"]:
            with tag.h2([HEADING, "mb-1"]):
                text(f"Builds in this batch · {len(result['activities'])}")
            with tag.p([MUTED, "mb-2"], id="batch-build-summary"):
                text(
                    " · ".join(
                        f"{count} { {'building': 'building', 'awaiting-result': 'awaiting result', 'unknown': 'without a recorded result'}.get(key, key) }"
                        for key, count in result["activity_counts"].items()
                    )
                )
            if result["activity_counts"].get("awaiting-result"):
                with tag.p([MUTED, "mb-2"]):
                    text(
                        "Ended activities await confirmation when the whole batch finishes."
                    )
            if result["activity_counts"].get("unknown"):
                with tag.p([MUTED, "mb-2"]):
                    text(
                        "This batch has ended. Some individual results were not confirmed; their logs are still available."
                    )
            with tag.div(["grid", "sm:grid-cols-2", "gap-x-5"]):
                for a in result["activities"]:
                    with tag.div(
                        [ROW, "flex", "justify-between", "gap-2", "py-1", "min-w-0"],
                        data_build_status=a["status"],
                    ):
                        with link(
                            LOG.url(view.with_(drv=a["drv"]), cid=cid, aid=aid),
                            [LINK, "truncate"],
                        ):
                            text(build_name(a["name"]))
                        with tag.span("shrink-0", title=a["phase"] or None):
                            status(
                                "build-result-unknown"
                                if a["status"] == "unknown"
                                else a["status"]
                            )


def evidence_link(evidence, cid, view, label="Failure log"):
    if not evidence:
        with tag.span(MUTED):
            text("No captured batch for this evidence.")
        return
    with link(
        LOG.url(
            view.with_(drv=evidence["drv"]),
            cid=evidence["campaign"],
            aid=evidence["id"],
        ),
        LINK,
    ):
        text(
            label
            if evidence["drv"] or evidence["kind"] == "plan"
            else "Batch diagnostic"
        )
    with tag.span(MUTED):
        text(" · ")
        timestamp(evidence["finished"] or evidence["created"])
        text(
            " · This campaign"
            if evidence["campaign"] == cid
            else " · From " + evidence["campaign_name"]
        )


def failure_label(failure, evidence=None):
    phase = (evidence or {}).get("phase") or ""
    if "check" in phase.lower():
        return "Tests failed"
    return {
        "compile-or-link": "Compilation or linking failed",
        "configure": "Configuration failed",
        "check": "Tests failed",
        "build": "Build failed",
    }.get(failure, failure)


def package(result, campaign, view):
    with tag.section(id="package-detail", data_sampled=result["sampled"]):
        hx.refresh(
            PACKAGE.url(view, cid=campaign["id"], pid=result["id"]),
            trigger=view.trigger,
            done=result["done"],
        )
        attr("hx-select", "#package-detail")
        cid = campaign["id"]
        meta = (result.get("selection") or {}).get("metadata") or {}
        recipe = result.get("recipe") or {}
        with tag.div(["flex", "items-baseline", "gap-3", "flex-wrap", "mb-2"]):
            with tag.h1([HEADING, "break-all"]):
                text(result["label"])
            with tag.span(MUTED):
                text(recipe.get("version") or meta.get("version") or "")
            status(result["state"], bool(result["tests"]))
            if result["drv"]:
                with link(GRAPH.url(view.with_(focus=result["drv"]), cid=cid), LINK):
                    text("Dependencies →")
        with tag.p("mb-2"):
            text(meta.get("description") or "")
        if result["state"] in ("blocked", "failed", "queued", "unplanned"):
            with tag.p([MUTED, "mb-2"], id="package-scheduling"):
                text(
                    {
                        "blocked": "Blocked by failed dependencies; not queued for a build.",
                        "failed": "Build failed; an explicit retry is required.",
                        "queued": "Queued for a build; not running yet.",
                        "unplanned": "Waiting for evaluation.",
                    }[result["state"]]
                )
                if (
                    result["state"] in ("queued", "unplanned")
                    and campaign["mode"] != "running"
                ):
                    text(" Campaign paused.")
        if result["log"]:
            with tag.p("mb-2"):
                evidence_link(
                    result["log"],
                    cid,
                    view,
                    "Failure log"
                    if result["state"] == "failed"
                    else "Previous build log"
                    if result["state"] in ("queued", "blocked")
                    and result["log"]["state"] == "finished"
                    else "Build log",
                )
        elif result["state"] == "blocked":
            with tag.p([MUTED, "mb-2"]):
                text(
                    "No build output for this package in this campaign. Open a dependency's failure log below."
                )
        if result["plan"]:
            with tag.p("mb-2"):
                evidence_link(result["plan"], cid, view, "Planning log")
        if result["source_url"]:
            with link(result["source_url"], [LINK, "break-all"], navigate=False):
                text(result["selection"].get("sourceFile") or "Nixpkgs source")
        if result["error"]:
            with tag.pre(
                [
                    "font-sans",
                    "whitespace-pre-wrap",
                    "break-words",
                    "text-red-800",
                    "my-3",
                ]
            ):
                text(result.get("error_summary") or result["error"][:2000])
            with tag.details("mb-3"):
                with tag.summary([FOCUS, "cursor-pointer"]):
                    text("Full diagnostic")
                with tag.pre(
                    ["whitespace-pre-wrap", "break-all", "font-mono", "text-xs"]
                ):
                    text(result["error"])
        if result["blockers"]:
            with tag.h2([HEADING, "mt-4", "mb-1"]):
                text("Blocking dependencies")
            for blocker in result["blockers"]:
                with tag.div([ROW, "py-2"]):
                    with link(GRAPH.url(view.with_(focus=blocker["drv"]), cid=cid)):
                        text(build_name(blocker["drv"].rsplit("/", 1)[-1][33:-4]))
                    with tag.p(["text-red-800", "break-words"]):
                        text(
                            failure_label(blocker["failure"], blocker["evidence"])[
                                :1000
                            ]
                        )
                    with tag.p():
                        evidence_link(blocker["evidence"], cid, view)
                    if len(blocker["chain"]) > 2:
                        with tag.p([MUTED, "break-words"]):
                            text(
                                "Via "
                                + " → ".join(
                                    build_name(d.rsplit("/", 1)[-1][33:-4])
                                    for d in blocker["chain"][1:-1]
                                )
                            )
        if result["tests"]:
            with tag.h2([HEADING, "mt-4", "mb-1"]):
                text("Test evidence")
            with tag.ul():
                for evidence in result["tests"]:
                    with tag.li("py-0.5"):
                        with link(
                            LOG.url(
                                view.with_(drv=result["drv"]),
                                cid=cid,
                                aid=evidence["attempt"],
                            )
                        ):
                            text(evidence["phase"] + " · " + evidence["attempt"][:8])
        if result["downstream_tests"]:
            with tag.h2([HEADING, "mt-4", "mb-1"]):
                text("Tested consumers")
            with tag.div(["grid", "sm:grid-cols-2"]):
                for row in result["downstream_tests"]:
                    with link(
                        PACKAGE.url(view, cid=cid, pid=row["id"]), [LINK, "py-0.5"]
                    ):
                        text(row["label"])
        with tag.div(["grid", "sm:grid-cols-2", "gap-x-6", "mt-4"]):
            for title, rows in [
                ("Direct dependencies", result["dependencies"]),
                ("Selected dependents", result["dependents"]),
            ]:
                with tag.section():
                    with tag.h2([HEADING, "mb-1"]):
                        text(title)
                    if not rows:
                        empty("None recorded.")
                    for row in rows:
                        url = (
                            PACKAGE.url(view, cid=cid, pid=row["id"])
                            if "id" in row
                            else GRAPH.url(view.with_(focus=row["drv"]), cid=cid)
                        )
                        with link(url, [LINK, ROW, "block", "py-1", "break-words"]):
                            text(
                                row.get("label")
                                or build_name(row.get("name") or row["drv"])
                            )


def graph_node(node, cid, view, focus=False):
    with tag.div(
        [
            "border",
            "border-stone-300",
            "px-2",
            "py-1.5",
            "bg-white",
            "min-w-0",
            ["border-sky-700", "bg-sky-50"] if focus else [],
        ],
        id=("focus-node" if focus else None),
    ):
        if focus:
            with tag.h2(["font-medium", "break-words"]):
                text(build_name(node["name"]))
        else:
            with link(
                GRAPH.url(view.with_(focus=node["drv"], page=0), cid=cid),
                [LINK, "break-words"],
            ):
                text(build_name(node["name"]))
        with tag.div(["flex", "gap-2", "flex-wrap"]):
            with tag.span(
                title="Required outputs are available; inferred from a consumer reaching its build phase."
                if node.get("availability_evidence") == "consumer-phase"
                else "Required outputs were observed in the store."
                if node["state"] == "available"
                else None
            ):
                status("ready" if node["state"] == "available" else node["state"])
            with tag.span(MUTED):
                text((node["phase"] or "").removesuffix("Phase"))
            if node.get("evidence") and not focus:
                with link(
                    LOG.url(
                        view.with_(drv=node["evidence"]["drv"]),
                        cid=node["evidence"]["campaign"],
                        aid=node["evidence"]["id"],
                    ),
                    LINK,
                ):
                    text("Log")
        if focus and node["failure"]:
            with tag.p(["text-red-800", "break-words", "mt-1"]):
                text(
                    (
                        "Previous failure: "
                        if node["state"] in ("building", "settling", "queued")
                        else ""
                    )
                    + failure_label(node["failure"], node.get("evidence"))[:1000]
                )
        if focus:
            if node.get("evidence"):
                with tag.p("mt-1"):
                    evidence_link(
                        node["evidence"],
                        cid,
                        view,
                        "Failure log"
                        if node["state"] == "failed"
                        else "Previous build log"
                        if node["state"] in ("queued", "blocked")
                        and node["evidence"]["state"] == "finished"
                        else "Build log",
                    )
            if node["state"] == "failed":
                with tag.p([MUTED, "mt-1"]):
                    text("Not queued; an explicit retry is required.")
            elif node["state"] == "blocked":
                with tag.p([MUTED, "mt-1"]):
                    text("Waiting for failed dependencies; not queued for a build.")
            for alias in node["labels"]:
                with link(
                    PACKAGE.url(view, cid=cid, pid=alias["id"]), [LINK, "block", "mt-1"]
                ):
                    text(alias["label"])


def graph(result, campaign, view):
    cid = campaign["id"]
    with tag.section(id="dependency-region"):
        hx.refresh(
            GRAPH_REGION.url(view, cid=cid), trigger=view.trigger, done=result["done"]
        )
        with tag.div(["flex", "justify-between", "gap-2", "mb-3"]):
            with tag.h1(HEADING):
                text("Dependency graph")
            with link(GRAPH.url(view.with_(focus="", page=0), cid=cid)):
                text("Follow builds" if view.focus else "Following builds")
        if not result["focus"]:
            empty("The dependency graph appears after the first planning batch.")
            return
        with tag.div(["grid", "md:grid-cols-3", "gap-3", "items-start"]):
            with tag.section(["order-2", "md:order-1", "min-w-0"]):
                with tag.h2([HEADING, "mb-1"]):
                    text(f"Inputs · {result['totals']['inputs']}")
                with tag.div(["space-y-1"]):
                    for node in result["inputs"]:
                        graph_node(node, cid, view)
                if result["totals"]["hidden_available"]:
                    with link(
                        GRAPH.url(
                            view.with_(
                                focus=result["focus"]["drv"], available=1, page=0
                            ),
                            cid=cid,
                        ),
                        [LINK, "block", "mt-2"],
                    ):
                        text(
                            f"Show {result['totals']['hidden_available']} ready inputs"
                        )
                elif view.available:
                    with link(
                        GRAPH.url(view.with_(available=0, page=0), cid=cid),
                        [LINK, "block", "mt-2"],
                    ):
                        text("Hide ready inputs")
            with tag.section(["order-1", "md:order-2", "min-w-0"]):
                with tag.h2([HEADING, "mb-1"]):
                    text("Current package")
                graph_node(result["focus"], cid, view, True)
                with tag.p([MUTED, "mt-2"]):
                    text(f"{result['selected_dependents']:,} selected dependents")
            with tag.section(["order-3", "min-w-0"]):
                with tag.h2([HEADING, "mb-1"]):
                    text(f"Consumers · {result['totals']['consumers']}")
                with tag.div("space-y-1"):
                    for node in result["consumers"]:
                        graph_node(node, cid, view)
        with tag.div(["flex", "gap-4", "mt-3"]):
            if result["page"]:
                with link(
                    GRAPH.url(
                        view.with_(
                            focus=result["focus"]["drv"], page=result["page"] - 1
                        ),
                        cid=cid,
                    )
                ):
                    text("← Previous neighbors")
            if result["totals"]["more"]:
                with link(
                    GRAPH.url(
                        view.with_(
                            focus=result["focus"]["drv"], page=result["page"] + 1
                        ),
                        cid=cid,
                    )
                ):
                    text("More neighbors →")


def blocker_name(row):
    return build_name(row["name"] or row["drv"].rsplit("/", 1)[-1][33:-4])


def blockers(result, campaign, view):
    cid = campaign["id"]
    with tag.section(id="blockers"):
        with tag.div(["flex", "flex-wrap", "justify-between", "gap-2", "mb-1"]):
            with tag.h1(HEADING):
                text("Blockers")
            with tag.span([MUTED, "text-xs"]):
                text("Computed ")
                timestamp(result["computed"], date=False)
        with tag.p([MUTED, "mb-3"]):
            text(
                f"{result['total']:,} failed derivations block "
                f"{result['blocked']:,} packages; "
                f"{result['multiple']:,} of those have more than one failed "
                "dependency. “Only cause” counts packages that this failure "
                "alone blocks: fixing it would let them build or reach their "
                "own failures."
            )
        if not result["rows"]:
            empty("No failures block other packages.")
            return
        with tag.table(
            ["w-full", "table-fixed", "border-collapse"],
            id="blocker-list",
            data_count=len(result["rows"]),
        ):
            with tag.thead(
                ["sticky", "top-0", "bg-[#f7f7f2]", "border-b", "border-stone-400", "z-10"]
            ):
                with tag.tr():
                    with tag.th([CELL, HEADING], scope="col"):
                        text("Failure")
                    with tag.th(
                        [CELL, "text-right", "font-medium", "w-20", "sm:w-28"],
                        scope="col",
                    ):
                        text("Blocks")
                    with tag.th(
                        [CELL, "text-right", "font-medium", "w-20", "sm:w-28"],
                        scope="col",
                    ):
                        text("Only cause")
            with tag.tbody():
                for rank, row in enumerate(
                    result["rows"], result["page"] * result["size"] + 1
                ):
                    blocker_row(row, rank, result["most"], cid, view)
        with tag.div(["flex", "gap-4", "mt-3"]):
            if result["page"]:
                with link(BLOCKERS.url(view.with_(page=result["page"] - 1), cid=cid)):
                    text("← Previous")
            if (result["page"] + 1) * result["size"] < result["total"]:
                with link(BLOCKERS.url(view.with_(page=result["page"] + 1), cid=cid)):
                    text("More blockers →")


def blocker_row(row, rank, most, cid, view):
    with tag.tr(ROW, id="blocker-" + str(rank)):
        with tag.td([CELL, "min-w-0"]):
            with tag.div(["flex", "gap-2", "items-baseline", "min-w-0"]):
                with tag.span([MUTED, "tabular-nums", "shrink-0", "w-8"]):
                    text(f"{rank}.")
                with link(
                    GRAPH.url(view.with_(focus=row["drv"], page=0), cid=cid),
                    [FOCUS, "font-medium", "break-words", "min-w-0"],
                ):
                    text(blocker_name(row))
            with tag.div(["ml-10", "text-stone-600", "break-words"]):
                with tag.span("text-red-800"):
                    text(failure_label(row["failure"], row["evidence"]))
                text(" · ")
                evidence_link(row["evidence"], cid, view)
                if row["package"] is not None:
                    text(" · ")
                    with link(PACKAGE.url(view, cid=cid, pid=row["package"])):
                        text("Package")
            # Width relative to the largest blocker (no inline styles under the CSP).
            with tag.svg(
                ["block", "ml-10", "mt-1", "h-1.5", "w-[calc(100%-2.5rem)]"],
                viewBox="0 0 1000 4",
                preserveAspectRatio="none",
                aria_hidden="true",
            ):
                tag.rect(x=0, y=0, width=1000, height=4, fill="#e7e5e4")
                tag.rect(
                    x=0, y=0, width=round(row["blocks"] / max(most, 1) * 1000), height=4,
                    fill="#ac965b",
                )
            if row["examples"]:
                with tag.details(["ml-10", "mt-1"]):
                    with tag.summary([FOCUS, "cursor-pointer", MUTED]):
                        text("Blocked packages")
                    with tag.p(["break-words"]):
                        for index, example in enumerate(row["examples"]):
                            if index:
                                text(", ")
                            with link(
                                PACKAGE.url(view, cid=cid, pid=example["id"]),
                                LINK if example["only"] else [LINK, "text-stone-600"],
                            ):
                                text(example["label"])
                        if row["blocks"] > len(row["examples"]):
                            with tag.span(MUTED):
                                text(f" and {row['blocks'] - len(row['examples']):,} more")
        with tag.td([CELL, "text-right", "tabular-nums", "font-medium"]):
            text(f"{row['blocks']:,}")
        with tag.td([CELL, "text-right", "tabular-nums"]):
            text(f"{row['only']:,}" if row["only"] else "—")
