#!/usr/bin/env python3
"""Prepare tiny native fixtures, as a separate paused campaign. Controller must be stopped.

Usage: python tests/experiment-calibration.py STATE PINNED_NIXPKGS
This evaluates derivations and queues one small attempt, not the real inventory.
The production controller and attempt template perform the execution.
"""

import json
from pathlib import Path
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from experiment import nix
from experiment.controller import Controller
from experiment.model import connect, encode, import_campaign, writer_lock

state, pkgs = sys.argv[1:]
expr = f'let ps = import {pkgs} {{}}; fixtures = import {Path(__file__).with_suffix(".nix")} {{ pkgs = ps; nonce = "{int(time.time())}"; }}; in builtins.mapAttrs (_: p: {{ drv = p.drvPath; outputs = {{ out = p.outPath; }}; }}) fixtures'
recipes = nix.query(
    "eval",
    "--impure",
    "--json",
    "--option",
    "allow-import-from-derivation",
    "false",
    "--expr",
    expr,
)
with writer_lock(state), connect(state) as db:
    cid = import_campaign(
        db,
        "Runner calibration · native fixtures",
        {
            "purpose": "Synthetic native runner validation, outside the Fil-C inventory",
            "attrPaths": [[k] for k in recipes],
        },
        pkgs,
        "calibration-fixtures",
        nix.DEFAULT_POLICY,
        subprocess.check_output([nix.NIX, "--version"], text=True).strip(),
    )
    ctl = Controller(db, state)
    for k, r in recipes.items():
        nix.add_graph(db, nix.graph([r["drv"]]))
        db.execute(
            "UPDATE candidates SET drv=?,state='queued',recipe=? WHERE campaign=? AND label=?",
            (
                r["drv"],
                encode(
                    dict(
                        r,
                        name=k,
                        roles=[],
                        compiler=None,
                        expectedCompiler="native-calibration",
                        hostPlatform="x86_64-linux",
                        doCheck=True,
                        doInstallCheck=False,
                    )
                ),
                cid,
                k,
            ),
        )
        ctl.root(r["drv"])
    db.commit()
    targets = [recipes[k]["drv"] for k in ("good", "dependent", "sibling")]
    from experiment.model import closure

    drvs = sorted(set(d for t in targets for d in closure(db, t)))
    outputs = sorted(
        set(
            p
            for d in drvs
            for p in json.loads(
                db.execute(
                    "SELECT outputs FROM derivations WHERE drv=?", (d,)
                ).fetchone()[0]
            ).values()
            if p
        )
    )
    aid = ctl.intent(
        ctl.campaign(cid), "build", targets, derivations=drvs, output_paths=outputs
    )
    print(json.dumps(dict(campaign=cid, attempt=aid, recipes=recipes), indent=2))
