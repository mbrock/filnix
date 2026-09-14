"""Freeze build results with their batch, so later retries cannot rewrite history."""

import json

from .model import encode


def snapshot(db, aid):
    # Ownership is essential: today's availability alone says nothing about an
    # older batch. Test evidence is already immutable and scoped to its attempt.
    return {
        row["drv"]: (
            "tested"
            if row["checked"]
            else "built"
            if row["evidence_attempt"] == aid and row["available"]
            else "failed"
            if row["evidence_attempt"] == aid and row["failure"]
            else "unknown"
        )
        for row in db.execute(
            """SELECT DISTINCT a.drv,d.available,d.failure,d.evidence_attempt,
            EXISTS(SELECT 1 FROM tests t WHERE t.attempt=a.attempt AND t.drv=a.drv) AS checked
            FROM activities a LEFT JOIN derivations d ON d.drv=a.drv
            WHERE a.attempt=? AND a.kind='build' AND a.drv IS NOT NULL""",
            (aid,),
        )
    }


def backfill(db):
    """Controller-only migration using retained evidence; never re-run old builds."""
    rows = db.execute(
        """SELECT id,result FROM attempts WHERE kind='build' AND state='finished'
        AND result IS NOT NULL AND json_type(result,'$.build_outcomes') IS NULL"""
    ).fetchall()
    with db:
        for row in rows:
            result = json.loads(row["result"])
            result["build_outcomes"] = snapshot(db, row["id"])
            result["build_outcomes_source"] = "retained-evidence"
            db.execute(
                "UPDATE attempts SET result=? WHERE id=?", (encode(result), row["id"])
            )
