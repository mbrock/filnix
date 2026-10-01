"""Evidence-bound suggestions. Worker reads; only the controller persists results.

Neither classifications nor their probabilities participate in build admission.
"""

from collections import deque
from contextlib import closing
import json
import math
import os
from pathlib import Path
import socket
import time
import urllib.error
import urllib.request

from .logs import decode, ERROR
from .model import atomic_json, connect, encode, event, identity, stamp

QUESTION_VERSION = "facets-1"
MODELS = {"jev": "jev-1.13.0", "openai": "gpt-6-luna"}
DEFINITIONS = {
    "package": {
        "Application": "An end-user command, interactive application or service; a compiler or build generator alone does not count.",
        "Library": "A reusable programmatic API, module or toolkit; many graph consumers alone do not establish an API.",
        "Build tool": "The package itself builds, compiles, configures or generates software; merely using a build tool does not count.",
        "Language runtime": "A programming-language interpreter, virtual machine or development kit, not merely a binding.",
        "FFI or bindings": "Foreign-function interface, native language bindings or introspection bridge, not simply any C library.",
        "Graphics or desktop": "GUI toolkit, display integration, rendering or image processing is a purpose of the package itself.",
        "Audio or video": "Audio/video encoding, decoding, processing or streaming is a purpose of the package itself.",
        "Networking": "Network protocols, URL transfer or network I/O is functionality of the package itself.",
        "Cryptography or TLS": "Cryptographic primitives or secure transport is functionality of the package itself; this is not a security verdict.",
        "Data or compression": "Database, structured-data/file-format processing or compression is functionality of the package itself.",
        "Testing support": "Provides a test framework, debugging or testing assistance, not merely running its own tests.",
    },
    "diagnostic": {
        "Pointer safety diagnostic": "An explicit pointer/object/capability safety diagnostic is visible; a signal alone is insufficient.",
        "Unsupported assembly": "The terminal failure explicitly rejects inline or standalone assembly.",
        "Missing tool or module": "The terminal failure explicitly identifies a missing executable, import or dependency.",
        "Compiler selection": "The terminal failure requires a different compiler/toolchain selection.",
        "Cross-build configuration": "The terminal failure requests a host-tool path or cross-configure cache answer.",
        "Extension ABI or loader": "The terminal failure explicitly concerns an incompatible compiled extension or loader boundary.",
        "Test assertion": "A functional assertion or test expectation failed; not just a generic builder wrapper saying failed.",
        "Timeout": "A timeout is the terminal outcome; preserve earlier symptoms separately.",
        "Platform evaluation refusal": "Evaluation refuses a named package or dependency for the requested platform.",
        "Broken-package evaluation refusal": "Evaluation refuses a package or dependency explicitly marked broken.",
        "Mechanism unclear": "The provided terminal diagnostic is too incomplete or generic to identify a specific mechanism.",
    },
    "patch": {
        "Pointer representation": "Visible changes alter pointer/integer encodings, tags, alignment, allocation or capability-carrying operations; not proof of soundness.",
        "Dependency or tool correction": "Visible changes correct linking, declared dependencies, executable selection or build/host tool scope.",
        "Build or cross adaptation": "Visible changes adapt build/configure/detection behavior for compiler or platform compatibility.",
        "Feature restriction": "Visible changes disable a feature, optional implementation, assembly path or output; not necessarily tests.",
        "Test adaptation": "Visible changes modify test stimulus, expectations or infrastructure, distinct from skipping tests.",
        "Test coverage reduction": "Visible changes disable test phases, remove assertions or exclude test cases.",
        "Version workaround": "Visible changes pin versions, backport a fix or handle an API/version ceiling.",
        "Platform integration": "Visible changes integrate profiles, paths, desktop/display, CPU or system services.",
    },
}
SCOPE = (
    "Judge only the named target using supplied evidence. Labels may overlap. "
    "Neighbor properties are not target properties. Native/host inputs do not prove "
    "invocation, runtime linkage, optionality or source generation. Missing evidence "
    "is unknown. Distinguish visible effects from comments and referenced unseen code. "
    "Diagnose observed mechanisms, not unverified root causes, safety or repair success."
)


def source_fields(row, kind):
    if kind == "package":
        return {k: row[k] for k in ("selection", "recipe", "drv")}
    if kind == "diagnostic":
        return {k: row[k] for k in ("drv", "error", "failure", "evidence_attempt")}
    if kind == "patch":
        return {k: row[k] for k in ("recipe", "drv")}
    raise ValueError("unknown classification kind")


def candidates(db, campaign, candidate_id=None):
    return db.execute(
        """SELECT c.*,d.failure,d.evidence_attempt FROM candidates c
        LEFT JOIN derivations d ON d.drv=c.drv WHERE c.campaign=?
        AND (? IS NULL OR c.id=?) ORDER BY c.label""",
        (campaign, candidate_id, candidate_id),
    ).fetchall()


def classification_index(db, campaign, candidate_id=None):
    # Allows previewing the new read-only app before the controller migrates.
    if not db.execute(
        "SELECT 1 FROM sqlite_master WHERE name='classifications'"
    ).fetchone():
        return {}
    sources = {r["id"]: r for r in candidates(db, campaign, candidate_id)}
    result = {}
    # A large catalog needs probabilities/provenance, not thousands of full
    # source documents. Detail reads only this candidate's actual evidence.
    fields = "campaign,candidate,kind,subject,provider,model,question_version,source_hash,evidence_hash,probabilities,usage,created"
    if candidate_id is not None:
        fields += ",evidence"
    for row in db.execute(
        f"SELECT {fields} FROM classifications WHERE campaign=? AND (? IS NULL OR candidate=?) ORDER BY kind,subject,provider",
        (campaign, candidate_id, candidate_id),
    ):
        source = sources.get(row["candidate"])
        if (
            not source
            or identity(source_fields(source, row["kind"])) != row["source_hash"]
        ):
            continue
        item = dict(row)
        for field in ("probabilities", "usage", "evidence"):
            if field in item:
                item[field] = json.loads(item[field])
        item["probability_source"] = (
            "model probability"
            if item["provider"] == "jev"
            else "self-reported estimate"
        )
        result.setdefault(row["candidate"], []).append(item)
    return result


def annotations(db, campaign, candidate_id):
    return classification_index(db, campaign, candidate_id).get(candidate_id, [])


def persist(db, campaign, item):
    row = db.execute(
        """SELECT c.*,d.failure,d.evidence_attempt FROM candidates c
        LEFT JOIN derivations d ON d.drv=c.drv WHERE c.campaign=? AND c.id=?""",
        (campaign, item["candidate"]),
    ).fetchone()
    kind, provider = item["kind"], item["provider"]
    if not row or provider not in MODELS or kind not in DEFINITIONS:
        raise ValueError("classification target does not belong to campaign")
    if (
        item["question_version"] != QUESTION_VERSION
        or item["model"] != MODELS[provider]
    ):
        raise ValueError("unsupported classification model or rubric")
    if identity(source_fields(row, kind)) != item["source_hash"]:
        return "stale evidence discarded"
    if identity(item["evidence"]) != item["evidence_hash"]:
        raise ValueError("classification evidence hash mismatch")
    validate_probabilities(item["probabilities"], kind)
    if (
        len(encode(item)) > 60000
        or not isinstance(item["subject"], str)
        or len(item["subject"]) > 1024
    ):
        raise ValueError("classification exceeds evidence budget")
    fields = (
        "candidate",
        "kind",
        "subject",
        "provider",
        "model",
        "question_version",
        "source_hash",
        "evidence_hash",
    )
    with db:
        db.execute(
            """INSERT OR REPLACE INTO classifications
            (campaign,candidate,kind,subject,provider,model,question_version,source_hash,
             evidence_hash,evidence,probabilities,usage,created) VALUES(?,?,?,?,?,?,?,?,?,?,?,?,?)""",
            (
                campaign,
                *(item[k] for k in fields),
                encode(item["evidence"]),
                encode(item["probabilities"]),
                encode(item.get("usage", {})),
                stamp(),
            ),
        )
        event(
            db,
            campaign,
            "classified",
            {"candidate": row["id"], "kind": kind, "provider": provider},
        )
    return "classification saved"


def validate_probabilities(values, kind):
    if not isinstance(values, dict) or set(values) != set(DEFINITIONS[kind]):
        raise ValueError("classification labels do not match rubric")
    if any(
        type(p) not in (int, float) or not math.isfinite(p) or not 0 <= p <= 1
        for p in values.values()
    ):
        raise ValueError("invalid classification probability")


def diagnostic_excerpt(db, state, drv, aid):
    """Scan finished evidence for this exact derivation, never another build's tail."""
    attempt = db.execute("SELECT state FROM attempts WHERE id=?", (aid,)).fetchone()
    if not attempt or attempt[0] != "finished":
        return {"text": "", "notice": "No finished attempt diagnostic available"}
    activities = {
        str(r["activity"]): r["drv"]
        for r in db.execute(
            "SELECT activity,drv FROM activities WHERE attempt=?", (aid,)
        )
    }
    path = Path(state) / "attempts" / aid / "stderr.log"
    recent, findings, after = deque(maxlen=12), [], 0
    scanned, deadline, complete = 0, time.monotonic() + 20, True
    if not path.is_file():
        return {"text": "", "notice": "Retained log unavailable"}
    with path.open("rb") as f:
        while raw := f.readline(1024 * 1024):
            scanned += len(raw)
            if scanned > 256 * 1024 * 1024 or time.monotonic() > deadline:
                complete = False
                break
            entry = decode(raw, scanned - len(raw), activities)
            if not entry or entry["drv"] != drv:
                continue
            line = entry["text"][-2000:]
            recent.append(line)
            if ERROR.search(line):
                findings.extend(recent)
                after = 8
            elif after:
                findings.append(line)
                after -= 1
            # Keep bounded first diagnostic context and the exact build's tail.
            if len(findings) > 120:
                findings = findings[:120]
    return {
        "text": "\n".join(findings)[:12000]
        + "\n[scoped tail]\n"
        + "\n".join(recent)[-4000:],
        "scan_complete": complete,
        "scanned_bytes": scanned,
        "notice": "Bounded exact-derivation evidence; missing text is unknown",
        "attempt": aid,
        "drv": drv,
    }


def work(db, state, campaign, row, skip=()):
    selection, recipe = json.loads(row["selection"]), json.loads(row["recipe"] or "{}")
    package = {
        "target": row["label"],
        "drv": row["drv"],
        "inventory": selection,
        "evaluated_recipe": recipe,
        "notice": "Inventory and recipe can differ; absent recipe is unknown, not no dependencies.",
    }
    if row["drv"]:
        package["direct_inputs"] = [
            dict(r)
            for r in db.execute(
                """SELECT e.child AS drv,d.name,e.outputs,
            (SELECT group_concat(role) FROM roles WHERE campaign=? AND parent=e.parent AND child=e.child) AS roles
            FROM edges e JOIN derivations d ON d.drv=e.child WHERE e.parent=? ORDER BY d.name LIMIT 24""",
                (campaign, row["drv"]),
            )
        ]
        package["consumer_sample"] = [
            dict(r)
            for r in db.execute(
                """SELECT c.label FROM candidates c JOIN edges e ON e.parent=c.drv
            WHERE c.campaign=? AND e.child=? ORDER BY c.label LIMIT 12""",
                (campaign, row["drv"]),
            )
        ]
        package["graph_notice"] = (
            "Bounded build-input neighborhood observed at classification time, not runtime linkage or current blockers."
        )
    if ("package", row["label"]) not in skip:
        yield "package", row["label"], package
    diagnostic_subject = row["drv"] or row["label"]
    if (row["error"] or row["failure"]) and (
        "diagnostic",
        diagnostic_subject,
    ) not in skip:
        diagnostic = {
            "target": row["label"],
            "drv": row["drv"],
            "recorded_error": (row["error"] or row["failure"])[-16000:],
        }
        if row["failure"] and row["evidence_attempt"]:
            diagnostic["excerpt"] = diagnostic_excerpt(
                db, state, row["drv"], row["evidence_attempt"]
            )
        yield "diagnostic", diagnostic_subject, diagnostic
    for path in recipe.get("patches", []):
        if (
            not isinstance(path, str)
            or not path.startswith("/nix/store/")
            or ("patch", path) in skip
        ):
            continue
        file = Path(path)
        if file.is_file() and file.stat().st_size <= 16000:
            yield (
                "patch",
                path,
                {
                    "target": row["label"],
                    "path": path,
                    "content": file.read_text(errors="replace"),
                    "recipe_revision": recipe.get("revision"),
                    "notice": "Exact immutable recipe patch; classification is not applicability or safety verification.",
                },
            )


def ask(provider, kind, evidence):
    definitions = DEFINITIONS[kind]
    if provider == "jev":
        payload = {
            "model": MODELS[provider],
            "state": evidence,
            "questions": {
                label: {
                    "type": "noul",
                    "instructions": SCOPE + "\n" + definition,
                    "criteria": {
                        "true": "Supplied evidence supports this condition.",
                        "false": "Supplied evidence does not support this condition.",
                    },
                }
                for label, definition in definitions.items()
            },
        }
        endpoint, key_name = "https://api.typesafe.ai/v1/systemone", "TYPESAFE_API_KEY"
    else:
        schema = {
            "type": "object",
            "properties": {
                label: {"type": "number", "minimum": 0, "maximum": 1}
                for label in definitions
            },
            "required": list(definitions),
            "additionalProperties": False,
        }
        payload = {
            "model": MODELS[provider],
            "store": False,
            "reasoning": {"effort": "none"},
            "max_output_tokens": 4800,
            "input": [
                {
                    "role": "system",
                    "content": SCOPE
                    + "\nEmit exactly one final_answer JSON object. Do not emit intermediate commentary, draft JSON, repeated JSON, or prose."
                    + "\nReturn your probability estimates for each independently applicable label:\n"
                    + encode(definitions),
                },
                {"role": "user", "content": encode(evidence)},
            ],
            "text": {
                "format": {
                    "type": "json_schema",
                    "name": "classification",
                    "strict": True,
                    "schema": schema,
                }
            },
        }
        endpoint, key_name = "https://api.openai.com/v1/responses", "OPENAI_API_KEY"
    key = os.environ.get(key_name)
    if not key:
        raise ValueError(f"{key_name} is not configured")
    request = urllib.request.Request(
        endpoint,
        data=encode(payload).encode(),
        headers={"Authorization": "Bearer " + key, "Content-Type": "application/json"},
    )
    try:
        with urllib.request.urlopen(request, timeout=90) as response:
            raw = json.loads(response.read(256000))
    except urllib.error.HTTPError as error:
        raise ValueError(
            f"{provider} HTTP {error.code}; request not automatically retried"
        ) from None
    if provider == "jev":
        if raw.get("model") != MODELS[provider] or set(raw.get("answers", {})) != set(
            definitions
        ):
            raise ValueError("unexpected Jev model or answer schema")
        probabilities = {
            label: answer["noul"] for label, answer in raw["answers"].items()
        }
    else:
        if raw.get("status") != "completed":
            raise ValueError("OpenAI response did not complete")
        if raw.get("model") != MODELS[provider]:
            raise ValueError("unexpected OpenAI model")
        messages = [o for o in raw.get("output", []) if o.get("type") == "message"]
        final = [o for o in messages if o.get("phase") == "final_answer"]
        if not final:
            final = [o for o in messages if o.get("phase") is None]
        if len(final) != 1 or any(
            c.get("type") == "refusal" for c in final[0].get("content", [])
        ):
            raise ValueError("OpenAI response has no unique non-refused final answer")
        output = [
            c["text"]
            for o in final
            for c in o.get("content", [])
            if c.get("type") == "output_text"
        ]
        probabilities = json.loads("".join(output))
    validate_probabilities(probabilities, kind)
    return probabilities, raw.get("usage", {}), {"request": payload, "response": raw}


def submit(state, campaign, item):
    body = (
        encode({"op": "classification-import", "campaign": campaign, "item": item})
        + "\n"
    ).encode()
    if len(body) > 60000:
        raise ValueError("classification exceeds controller message budget")
    with socket.socket(socket.AF_UNIX) as client:
        # Busy campaign reconciliation can exceed the interactive CLI timeout.
        client.settimeout(300)
        client.connect(str(Path(state) / "control.sock"))
        client.sendall(body)
        response = json.loads(client.makefile().readline(65536))
    if "error" in response:
        raise ValueError(response["error"])
    return response["ok"]


def run(state, campaign, provider="jev", limit=100, labels=()):
    """Bounded batch; network never runs inside the controller or a DB transaction."""
    if provider not in MODELS or not 1 <= limit <= 1000:
        raise ValueError("invalid classifier provider or request budget")
    cache = Path(state) / "classifications"
    cache.mkdir(mode=0o700, exist_ok=True)
    with closing(connect(state, readonly=True)) as db:
        if not db.execute("SELECT 1 FROM campaigns WHERE id=?", (campaign,)).fetchone():
            raise ValueError("unknown campaign")
        rows = candidates(db, campaign)
        existing = classification_index(db, campaign)
    if labels:
        missing = set(labels) - {row["label"] for row in rows}
        if missing:
            raise ValueError("unknown package labels: " + ", ".join(sorted(missing)))
        rows = [row for row in rows if row["label"] in labels]
    count = 0
    for row in rows:
        skip = {
            (a["kind"], a["subject"])
            for a in existing.get(row["id"], [])
            if a["provider"] == provider
            and a["model"] == MODELS[provider]
            and a["question_version"] == QUESTION_VERSION
        }
        with closing(connect(state, readonly=True)) as db:
            for kind, subject, evidence in work(db, state, campaign, row, skip):
                source_hash = identity(source_fields(row, kind))
                if len(encode(evidence).encode()) > 48000:
                    print(
                        "Classification evidence exceeds budget:",
                        row["label"],
                        kind,
                        flush=True,
                    )
                    continue
                # The key includes rubric and exact evidence, never credentials.
                digest = identity(
                    {
                        "provider": provider,
                        "model": MODELS[provider],
                        "question_version": QUESTION_VERSION,
                        "kind": kind,
                        "evidence": evidence,
                    }
                )
                file = cache / (digest + ".json")
                if file.exists():
                    result = json.loads(file.read_text())
                    if result.get("error"):
                        continue  # Explicitly clear failed/unknown reservations to retry.
                else:
                    if count >= limit:
                        return {"requests": count}
                    try:
                        with file.open("x") as reservation:
                            reservation.write(
                                encode({"error": "reserved; delivery unknown"})
                            )
                            reservation.flush()
                            os.fsync(reservation.fileno())
                    except FileExistsError:
                        continue  # Another worker reserved this exact request.
                    count += 1
                    try:
                        probabilities, usage, raw = ask(provider, kind, evidence)
                    except (ValueError, OSError, KeyError) as error:
                        atomic_json(file, {"error": type(error).__name__})
                        print(
                            f"Classification request failed: {provider}, {type(error).__name__}",
                            flush=True,
                        )
                        continue
                    result = {
                        "probabilities": probabilities,
                        "usage": usage,
                        "raw": raw,
                    }
                    atomic_json(file, result)
                item = {
                    "candidate": row["id"],
                    "kind": kind,
                    "subject": subject,
                    "provider": provider,
                    "model": MODELS[provider],
                    "question_version": QUESTION_VERSION,
                    "source_hash": source_hash,
                    "evidence_hash": identity(evidence),
                    "evidence": evidence,
                    "probabilities": result["probabilities"],
                    "usage": result["usage"],
                }
                print(submit(state, campaign, item), row["label"], kind, flush=True)
    return {"requests": count}
