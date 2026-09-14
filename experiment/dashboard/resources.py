"""Canonical HTML resources and the reading options their URLs preserve."""

import re
from dataclasses import dataclass, replace
from urllib.parse import quote, urlencode

from starlette.exceptions import HTTPException
from starlette.routing import Route


@dataclass(frozen=True)
class View:
    watch: int = 1
    state: str = "available"
    q: str = ""
    kind: str = ""
    outcome: str = ""
    sort: str = "recent"
    focus: str = ""
    available: int = 0
    page: int = 0
    drv: str = ""
    follow: int = 1
    wrap: int = 1
    size: int = 12
    transport: str = "sse"

    @property
    def trigger(self):
        return (
            "campaign-changed from:body, every 5s"
            if self.transport == "sse"
            else "every 3s"
        )

    def with_(self, **values):
        return replace(self, **values)


@dataclass(frozen=True)
class Resource:
    path: str
    carries: tuple[str, ...] = ()

    def url(self, view=None, **params):
        path = re.sub(
            r"\{(\w+)(?::\w+)?\}",
            lambda m: quote(str(params.pop(m[1])), safe=""),
            self.path,
        )
        query = {key: getattr(view, key) for key in self.carries} if view else {}
        query.update(params)
        query = {k: v for k, v in query.items() if v is not None and v != ""}
        return path + ("?" + urlencode(query) if query else "")

    def route(self, endpoint):
        return Route(self.path, endpoint)


BASE = "/campaigns/{cid}"
ACTIVITY = Resource(BASE, ("watch", "transport"))
ACTIVITY_FEED = Resource(BASE + "/activity", ("watch", "transport"))
SUMMARY = Resource(BASE + "/summary", ("transport",))
EVENTS = Resource(BASE + "/events")
PACKAGES = Resource(BASE + "/packages", ("state", "transport"))
PACKAGE = Resource(BASE + "/packages/{pid:int}", ("transport",))
BATCHES = Resource(BASE + "/batches", ("q", "kind", "outcome", "sort", "transport"))
BATCH = Resource(BASE + "/batches/{aid}", ("transport",))
BATCH_STATUS = Resource(BASE + "/batches/{aid}/status", ("transport",))
GRAPH = Resource(BASE + "/dependencies", ("focus", "available", "page", "transport"))
GRAPH_REGION = Resource(
    BASE + "/dependencies/region", ("focus", "available", "page", "transport")
)
LOG = Resource(
    BASE + "/batches/{aid}/log", ("drv", "follow", "wrap", "size", "q", "transport")
)
LOG_STATUS = Resource(BASE + "/batches/{aid}/log/status", LOG.carries)
LIVE_LOG = Resource(BASE + "/log", ("drv", "follow", "wrap", "size", "q", "transport"))
UPDATES = Resource(BASE + "/updates", ("transport",))
CSV = Resource(BASE + "/packages.csv", ("state",))


def integer(value, minimum=0, maximum=10**12):
    try:
        result = int(value)
    except (TypeError, ValueError):
        raise HTTPException(400, "Expected an integer") from None
    if not minimum <= result <= maximum:
        raise HTTPException(400, "Number outside the supported range")
    return result


def options(request):
    p = request.query_params
    values = {
        key: p.get(key, getattr(View(), key)) for key in View.__dataclass_fields__
    }
    for key in ("follow", "wrap", "available", "watch"):
        values[key] = integer(values[key], 0, 1)
    values["page"] = integer(values["page"], 0, 1000000)
    values["size"] = integer(values["size"], 12, 16)
    choices = {
        "state": (
            "available",
            "tested",
            "failed",
            "failures",
            "blocked",
            "tried",
            "all",
            "evaluation-error",
        ),
        "kind": ("", "build", "plan"),
        "outcome": ("", "active", "error", "complete"),
        "sort": ("recent", "oldest", "longest"),
        "transport": ("sse", "poll"),
        "size": (12, 14, 16),
    }
    if any(values[key] not in allowed for key, allowed in choices.items()):
        raise HTTPException(400, "Invalid reading options")
    if (
        len(values["q"]) > 200
        or len(values["drv"]) > 1024
        or len(values["focus"]) > 1024
    ):
        raise HTTPException(400, "Reading option is too long")
    return View(**values)
