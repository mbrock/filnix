"""Locate the batch that owns evidence, independently of the viewing campaign."""


def attempt_evidence(db, aid, drv):
    row = db.execute(
        """SELECT a.id,a.campaign,c.name AS campaign_name,a.kind,a.state,
        a.created,a.finished FROM attempts a JOIN campaigns c ON c.id=a.campaign
        WHERE a.id=?""",
        (aid,),
    ).fetchone()
    if not row:
        return None
    result = dict(row)
    activity = db.execute(
        """SELECT phase FROM activities WHERE attempt=? AND drv=? AND kind='build'
        ORDER BY rowid DESC LIMIT 1""",
        (aid, drv),
    ).fetchone()
    # Planning diagnostics and failures before a builder started are batch output.
    result["drv"] = drv if activity else ""
    result["phase"] = activity["phase"] if activity else None
    return result


def failure_evidence(db, drv):
    row = db.execute(
        "SELECT evidence_attempt FROM derivations WHERE drv=?", (drv,)
    ).fetchone()
    return attempt_evidence(db, row[0], drv) if row and row[0] else None
