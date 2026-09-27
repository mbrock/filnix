"""Rank failed derivations by the packages they keep from building."""

from collections import defaultdict
import time

# The ranking walks the campaign's whole dependency graph (hundreds of
# thousands of edges), so keep one result per campaign for a short while.
TTL = 60
_cache = {}


def ranking(db, cid):
    now = time.monotonic()
    hit = _cache.get(cid)
    if hit and now - hit[0] < TTL:
        return hit[1]
    result = compute(db, cid)
    _cache[cid] = (now, result)
    return result


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

    failures = [
        (ids[drv], drv, name, failure)
        for drv, name, failure in db.execute(
            "SELECT drv,name,failure FROM derivations WHERE failure IS NOT NULL"
        )
        if drv in ids
    ]

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
    )
