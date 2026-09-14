"""ASGI HTML resources; the controller and compatibility API remain independent."""

import csv
import io
import sqlite3
from pathlib import Path

import anyio
from starlette.applications import Starlette
from starlette.datastructures import MutableHeaders
from starlette.exceptions import HTTPException
from starlette.middleware.gzip import GZipMiddleware
from starlette.middleware.wsgi import WSGIMiddleware
from starlette.responses import RedirectResponse, Response, StreamingResponse
from starlette.routing import Mount, Route
from starlette.staticfiles import StaticFiles
from tagflow import htmx as hx
from tagflow import tag, text
from tagflow.responses import render_response

from .. import web
from ..model import stamp
from . import base, data, logview, views
from .resources import (
    ACTIVITY,
    ACTIVITY_FEED,
    BATCH,
    BATCH_STATUS,
    BATCHES,
    CSV,
    EVENTS,
    GRAPH,
    GRAPH_REGION,
    LIVE_LOG,
    LOG,
    LOG_STATUS,
    PACKAGE,
    PACKAGES,
    SUMMARY,
    UPDATES,
    View,
    integer,
    options,
)


def representation(request, component, *, page=False, headers=None, recovery=False):
    return render_response(
        request,
        component,
        doctype=page,
        headers=headers,
        cache_control="no-store" if recovery else "public, no-cache",
        conditional=not recovery,
    )


class ResponseHeaders:
    """Headers without buffering streaming responses or adding a task boundary."""

    def __init__(self, app):
        self.app = app

    async def __call__(self, scope, receive, send):
        async def send_headers(message):
            if message["type"] == "http.response.start":
                headers = MutableHeaders(scope=message)
                headers["X-Content-Type-Options"] = "nosniff"
                headers["Content-Security-Policy"] = (
                    "default-src 'self'; script-src 'self'; style-src 'self'; object-src 'none'; base-uri 'none'; frame-ancestors 'none'"
                )
                # Tagflow hashes exact HTML. Gzip can change the wire bytes, so
                # expose a weak validator valid across those content codings.
                if "etag" in headers:
                    headers["etag"] = "W/" + headers["etag"].removeprefix("W/")
                    if "accept-encoding" not in headers.get("vary", "").lower():
                        headers.add_vary_header("Accept-Encoding")
            await send(message)

        await self.app(scope, receive, send_headers)


def create_app(state):
    state = Path(state)

    def home(request):
        with data.read(state) as db:
            cid = request.query_params.get("campaign") or data.default_campaign(db)
            data.campaign(db, cid)
        p = request.query_params
        view = View(transport=p.get("transport", "sse"))
        if p.get("package"):
            url = PACKAGE.url(view, cid=cid, pid=integer(p["package"], 1))
        elif p.get("log"):
            url = LOG.url(
                view.with_(
                    drv=p.get("logDrv", ""),
                    follow=int(p.get("follow", "0") in ("1", "true")),
                ),
                cid=cid,
                aid=p["log"],
            )
        elif p.get("attempt"):
            url = BATCH.url(view, cid=cid, aid=p["attempt"])
        elif p.get("derivation") or p.get("focus"):
            url = GRAPH.url(
                view.with_(focus=p.get("derivation") or p["focus"]), cid=cid
            )
        else:
            url = ACTIVITY.url(view, cid=cid)
        return RedirectResponse(url, status_code=303)

    def page(request, section, prepare):
        view, cid = options(request), request.path_params["cid"]
        with data.read(state) as db:
            campaign, choices = data.campaign(db, cid), data.campaigns(db)
            title, content = prepare(db, cid, campaign, view)
        return representation(
            request,
            lambda: base.shell(title, campaign, choices, view, section, content),
            page=True,
        )

    def activity(request):
        def prepare(db, cid, c, v):
            summary, ledger = (
                data.summary(db, cid),
                data.ledger(db, cid, v.with_(sort="recent", kind="", outcome="", q="")),
            )
            return c["name"], lambda: views.activity(summary, ledger, v)

        return page(request, "activity", prepare)

    def activity_feed(request):
        view, cid = options(request), request.path_params["cid"]
        with data.read(state) as db:
            campaign = data.campaign(db, cid)
            ledger = data.ledger(
                db, cid, view.with_(sort="recent", kind="", outcome="", q="")
            )
        return representation(
            request, lambda: views.activity_feed(ledger, campaign, view)
        )

    def summary(request):
        view, cid = options(request), request.path_params["cid"]
        with data.read(state) as db:
            result = data.summary(db, cid)
        return representation(request, lambda: views.summary(result, view))

    def packages(request):
        def prepare(db, cid, c, v):
            result = data.packages(db, cid, v)
            return "Packages", lambda: views.packages(result, c, v)

        return page(request, "packages", prepare)

    def package(request):
        def prepare(db, cid, c, v):
            result = data.package(db, cid, request.path_params["pid"])
            return result["label"], lambda: views.package(result, c, v)

        return page(request, "packages", prepare)

    def batches(request):
        def prepare(db, cid, c, v):
            result = data.ledger(db, cid, v)
            return "Batches", lambda: views.batches(result, c, v)

        return page(request, "batches", prepare)

    def batch(request):
        def prepare(db, cid, c, v):
            result = data.batch(db, cid, request.path_params["aid"])
            now = stamp()
            return "Batch " + result["id"][:8], lambda: views.batch_status(
                result, c, v, now
            )

        return page(request, "batches", prepare)

    def batch_status(request):
        view, cid = options(request), request.path_params["cid"]
        with data.read(state) as db:
            c, result = (
                data.campaign(db, cid),
                data.batch(db, cid, request.path_params["aid"]),
            )
        return representation(
            request, lambda: views.batch_status(result, c, view, stamp())
        )

    def graph(request):
        def prepare(db, cid, c, v):
            result = data.live_graph(
                db, state, cid, v.focus or None, bool(v.available), v.page
            )
            result["done"] = data.finished(db, cid)
            return "Dependencies", lambda: views.graph(result, c, v)

        return page(request, "dependencies", prepare)

    def graph_region(request):
        view, cid = options(request), request.path_params["cid"]
        with data.read(state) as db:
            c = data.campaign(db, cid)
            result = data.live_graph(
                db, state, cid, view.focus or None, bool(view.available), view.page
            )
            result["done"] = data.finished(db, cid)
        return representation(request, lambda: views.graph(result, c, view))

    def updates(request):
        view, cid = options(request), request.path_params["cid"]
        seen = integer(request.query_params.get("seen", "0"))
        target = request.query_params.get("target", "activity")
        if target not in ("activity", "packages", "batches"):
            raise HTTPException(400, "Unknown update resource")
        with data.read(state) as db:
            data.campaign(db, cid)
            current = data.revision(db, cid)
            done = data.finished(db, cid)
        return representation(
            request, lambda: views.updates(cid, view, seen, current, target, done)
        )

    def log_response(request, *, live=False):
        view, cid = options(request), request.path_params["cid"]
        direction = request.query_params.get("direction", "tail")
        if direction not in ("tail", "after", "before"):
            raise HTTPException(400, "Unknown log direction")
        cursor = integer(request.query_params.get("cursor", "0"))
        count = integer(request.query_params.get("count", "0"), 0, logview.LIMIT)
        part = request.query_params.get("part", "")
        if part not in ("", "reader", "chunk"):
            raise HTTPException(400, "Unknown log representation")
        live = live or request.query_params.get("live") == "1"
        with data.read(state) as db:
            c, choices = data.campaign(db, cid), data.campaigns(db)
            latest = (
                data.latest_build(db, cid) if "aid" not in request.path_params else None
            )
            aid = request.path_params.get("aid") or (latest[0] if latest else None)
            if not aid:
                return representation(
                    request,
                    lambda: base.shell(
                        "Build log",
                        c,
                        choices,
                        view,
                        "activity",
                        lambda: base.empty("Waiting for the first batch."),
                    ),
                    page=True,
                )
            result = data.log(db, state, cid, aid, view, direction, cursor)
            if live:
                pending = db.execute(
                    "SELECT 1 FROM candidates WHERE campaign=? AND state IN ('unplanned','queued','running') LIMIT 1",
                    (cid,),
                ).fetchone()
                live = bool(pending or not result["finished"])
        recovery = result["reset"] or count + len(result["entries"]) > logview.LIMIT
        if recovery:
            count = 0
        if result["reset"]:
            with data.read(state) as db:
                result = data.log(db, state, cid, aid, view)
        if len(result["entries"]) > logview.LIMIT:
            result["entries"] = result["entries"][-logview.LIMIT :]
            result["start"] = result["entries"][0]["offset"]
            result["before"] = True
        content = lambda: logview.reader(
            result, c, view, live=live, count=count + len(result["entries"])
        )
        headers = hx.recover_reader(closest="#log-reader") if recovery else None
        return representation(
            request,
            lambda: base.shell(
                "Build output · " + aid[:8], c, choices, view, "batches", content
            ),
            page=True,
            headers=headers,
            recovery=recovery,
        )

    def log(request):
        return log_response(request)

    def live_log(request):
        return log_response(request, live=True)

    def log_status(request):
        view, cid = options(request), request.path_params["cid"]
        with data.read(state) as db:
            campaign = data.campaign(db, cid)
            result = data.log(
                db,
                state,
                cid,
                request.path_params["aid"],
                view,
                "status",
                integer(request.query_params.get("cursor", "0")),
            )
            result["end"] = result["size"]
        return representation(
            request,
            lambda: logview.tools(
                result, campaign, view, live=request.query_params.get("live") == "1"
            ),
        )

    def export(request):
        view, cid = options(request), request.path_params["cid"]
        with data.read(state) as db:
            data.campaign(db, cid)
            rows = data.packages(db, cid, view)["rows"]
        stream = io.StringIO()
        writer = csv.writer(stream)
        writer.writerow(
            ["package", "version", "description", "result", "source", "diagnostic"]
        )
        for row in rows:
            status = (
                "Tested"
                if row["checks"] and row["state"] == "available"
                else base.STATES.get(row["state"], (row["state"], []))[0]
            )
            values = [
                row["label"],
                row["version"],
                row["description"],
                status,
                row["source"],
                row["reason"],
            ]
            # Keep untrusted package metadata from becoming spreadsheet formulas.
            writer.writerow(
                [
                    "'" + str(v) if str(v).startswith(("=", "+", "-", "@")) else v
                    for v in values
                ]
            )
        return Response(
            stream.getvalue(),
            media_type="text/csv",
            headers={
                "Content-Disposition": 'attachment; filename="filnix-packages.csv"',
                "Cache-Control": "no-store",
            },
        )

    def notification_snapshot(cid):
        with data.read(state) as db:
            data.campaign(db, cid)
            current = data.revision(db, cid)
            waiting = db.execute(
                "SELECT 1 FROM candidates WHERE campaign=? AND state IN ('unplanned','queued','running') LIMIT 1",
                (cid,),
            ).fetchone()
            active = db.execute(
                "SELECT 1 FROM attempts WHERE campaign=? AND state!='finished' LIMIT 1",
                (cid,),
            ).fetchone()
        return current, not waiting and not active

    async def notifications(cid):
        previous, ticks = None, 0
        while True:
            current, done = await anyio.to_thread.run_sync(notification_snapshot, cid)
            if current != previous:
                yield f"id: {current}\nevent: campaign-changed\ndata: {current}\n\n"
                previous = current
            if done:
                yield "event: campaign-complete\ndata: complete\n\n"
                return
            if ticks % 10 == 0:
                yield ": heartbeat\n\n"
            ticks += 1
            await anyio.sleep(1)

    async def events(request):
        cid = request.path_params["cid"]
        await anyio.to_thread.run_sync(notification_snapshot, cid)
        return StreamingResponse(
            notifications(cid),
            media_type="text/event-stream",
            headers={"Cache-Control": "no-store", "X-Accel-Buffering": "no"},
        )

    def error_page(request, error):
        status = (
            error.status_code
            if isinstance(error, HTTPException)
            else 400
            if isinstance(error, ValueError)
            else 503
        )
        message = (
            error.detail
            if isinstance(error, HTTPException)
            else str(error)
            if isinstance(error, ValueError)
            else "Campaign data is temporarily unavailable. Please retry."
        )

        def content():
            with tag.html(lang="en"):
                with tag.head():
                    with tag.title():
                        text(f"{status} · filnix")
                with tag.body():
                    with tag.h1():
                        text(message)
                    with tag.a(href="/"):
                        text("Return to campaigns")

        return render_response(
            request,
            content,
            doctype=True,
            cache_control="no-store",
            conditional=False,
            status_code=status,
        )

    app = Starlette(
        routes=[
            Route("/", home),
            ACTIVITY.route(activity),
            ACTIVITY_FEED.route(activity_feed),
            SUMMARY.route(summary),
            EVENTS.route(events),
            PACKAGES.route(packages),
            PACKAGE.route(package),
            BATCHES.route(batches),
            BATCH.route(batch),
            BATCH_STATUS.route(batch_status),
            GRAPH.route(graph),
            GRAPH_REGION.route(graph_region),
            LOG.route(log),
            LOG_STATUS.route(log_status),
            LIVE_LOG.route(live_log),
            UPDATES.route(updates),
            CSV.route(export),
            Mount("/assets", StaticFiles(directory=Path(__file__).parent / "static")),
            Mount("/", WSGIMiddleware(web.application(state))),
        ],
        exception_handlers={
            HTTPException: error_page,
            ValueError: error_page,
            sqlite3.Error: error_page,
            OSError: error_page,
        },
    )
    app.add_middleware(GZipMiddleware, minimum_size=1024)

    app.add_middleware(ResponseHeaders)
    return app
