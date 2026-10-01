"""Rank failed derivations by the packages they keep from building.

The ranking walks the campaign's whole dependency graph (hundreds of
thousands of edges, a few seconds), so one result per campaign is kept and
refreshed in a background thread: requests get the previous result while a
newer one is computed. The same walk yields the campaign's derivations
(``scope``) and those that depend on a failure or exclusion (``bad``), which
the dependency view needs on every refresh.
"""

from collections import defaultdict
import sqlite3
import threading
import time

TTL = 60
# Tests change the database between reads and need every read to see it.
SYNCHRONOUS = False
_cache = {}
_refreshing = set()
_lock = threading.Lock()


def ranking(db, cid):
    hit = _cache.get(cid)
    if SYNCHRONOUS:
        result = compute(db, cid)
        _cache[cid] = (time.monotonic(), result)
        return result
    if hit is None:
        # A restart can receive many simultaneous live-page refreshes. Share
        # the first graph walk instead of multiplying its memory and CPU cost.
        with _lock:
            hit = _cache.get(cid)
            if hit is None:
                result = compute(db, cid)
                _cache[cid] = (time.monotonic(), result)
                return result
    if time.monotonic() - hit[0] >= TTL:
        with _lock:
            start = cid not in _refreshing
            _refreshing.add(cid)
        if start:
            path = db.execute("PRAGMA database_list").fetchone()[2]
            threading.Thread(target=_refresh, args=(path, cid), daemon=True).start()
    return hit[1]


def _refresh(path, cid):
    try:
        db = sqlite3.connect(f"file:{path}?mode=ro", uri=True, timeout=10)
        try:
            db.execute("PRAGMA query_only=ON")
            _cache[cid] = (time.monotonic(), compute(db, cid))
        finally:
            db.close()
    finally:
        with _lock:
            _refreshing.discard(cid)


def compute(db, cid):
    ids, names = {}, []

    def node(drv):
        i = ids.get(drv)
        if i is None:
            i = ids[drv] = len(names)
            names.append(drv)
        return i

    # Reverse edges of the graph reachable from this campaign's packages.
    parents = defaultdict(list)
    for parent, child in db.execute(
        """WITH RECURSIVE g(drv) AS (
          SELECT drv FROM candidates WHERE campaign=? AND drv IS NOT NULL
          UNION SELECT e.child FROM edges e JOIN g ON e.parent=g.drv)
        SELECT e.parent,e.child FROM g JOIN edges e ON e.parent=g.drv""",
        (cid,),
    ):
        parents[node(child)].append(node(parent))

    packages = defaultdict(list)
    for pid, drv, label, state in db.execute(
        "SELECT id,drv,label,state FROM candidates WHERE campaign=? AND drv IS NOT NULL",
        (cid,),
    ):
        packages[node(drv)].append((pid, label, state))

    failures, excluded = [], []
    for drv, name, failure, exclusion in db.execute(
        "SELECT drv,name,failure,exclusion FROM derivations "
        "WHERE failure IS NOT NULL OR exclusion IS NOT NULL"
    ):
        if drv in ids:
            # An out-of-scope failure is not a blocker to fix.
            if failure is not None and exclusion is None:
                failures.append((ids[drv], drv, name, failure))
            else:
                excluded.append(ids[drv])

    # Everything that depends on a failure or exclusion, including itself.
    bad = [i for i, *_ in failures] + excluded
    marked = set(bad)
    while bad:
        for p in parents.get(bad.pop(), ()):
            if p not in marked:
                marked.add(p)
                bad.append(p)

    # Each failure's blocked packages, and each blocked package's failures.
    blocked, causes = {}, defaultdict(list)
    for i, *_ in failures:
        seen, stack = {i}, [i]
        while stack:
            for p in parents.get(stack.pop(), ()):
                if p not in seen:
                    seen.add(p)
                    stack.append(p)
        seen.discard(i)
        hits = [
            pkg
            for n in seen
            for pkg in packages.get(n, ())
            if pkg[2] == "blocked"
        ]
        blocked[i] = hits
        for pid, _, _ in hits:
            causes[pid].append(i)

    only = defaultdict(set)
    for pid, cs in causes.items():
        if len(cs) == 1:
            only[cs[0]].add(pid)

    rows = []
    for i, drv, name, failure in failures:
        hits = blocked[i]
        if not hits:
            continue
        sole = only[i]
        # Examples: packages this failure alone blocks come first.
        examples = sorted(hits, key=lambda p: (p[0] not in sole, p[1]))
        own = packages.get(i)
        rows.append(
            dict(
                drv=drv,
                name=name,
                failure=failure,
                package=own[0][0] if own else None,
                blocks=len(hits),
                only=len(sole),
                examples=[dict(id=p[0], label=p[1], only=p[0] in sole) for p in examples[:8]],
            )
        )
    rows.sort(key=lambda r: (-r["blocks"], -r["only"], r["name"]))
    return dict(
        rows=rows,
        blocked=len(causes),
        multiple=sum(1 for cs in causes.values() if len(cs) > 1),
        computed=time.time(),
        scope=frozenset(ids),
        bad=frozenset(names[i] for i in marked),
    )
