#!/usr/bin/env python3
"""Differential verification: StealMyBitcoin exploit vs Fil-C PHP 8.4.25.

Runs the adapted PoC (stealmybitcoin_poc_8425.py) against two builds of the
same vulnerable PHP release, one request pipeline through one nginx front:

- the native arm, Nixpkgs' unstripped PHP 8.4.25 (the unsafe baseline). The
  exploit must succeed end to end: heap leak, code leak, forged HashTable,
  zif_system called with the proof command. This proves the PoC really
  exploits this exact PHP before the Fil-C arm can mean anything.

- the Fil-C arm, pkgsFilc.php84_25 (docs/php.md). The exploit must be
  thwarted: the first consumer that reads the corrupted-length session-id
  cookie trips a capability trap, the process dies with a Fil-C panic
  before a single byte of the cookie leaks, and the PoC aborts at the heap
  stage. Every run kills the worker, so each run relaunches the server.

Both servers are single `php -S` processes behind nginx. nginx stays in
front because the PoC pipelines a producer and eight consumers on one
connection; the producer's OOM fatal closes a direct upstream connection,
while nginx re-issues each request on a fresh one.

Each attempt's raw HTTP, stage JSON and server logs land under the output
directory. The final response of a successful native run contains a dummy
flag (bin/print-flag), never a real key.

    verify.py --native PHP --native-ini DIR --filc PHP --filc-ini DIR \\
        --nginx BIN --poc FILE --lab DIR --out DIR
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import socket
import subprocess
import sys
import time
from pathlib import Path

PANIC = "filc panic: thwarted a futile attempt to violate memory safety"
TRAP_SITE = "php_hash_environment"  # the corrupted-length cookie read


def tcp_up(host: str, port: int) -> bool:
    try:
        with socket.create_connection((host, port), timeout=1):
            return True
    except OSError:
        return False


class Lab:
    """The nginx front, the PHP backends and their logs, per output root."""

    def __init__(self, root: Path, nginx: str, front: int, back: int):
        self.root = root
        self.front, self.back = front, back
        self.public = root / "public"
        self.bin = root / "bin"
        self.run = root / "run"
        self.nginx = nginx
        self.back_proc: subprocess.Popen | None = None
        self.front_proc: subprocess.Popen | None = None

    def prepare(self, assets: Path) -> None:
        self.public.mkdir(parents=True)
        self.bin.mkdir(parents=True)
        self.run.mkdir(parents=True)
        shutil.copy(assets / "public" / "php-version.php", self.public / "php-version.php")
        shutil.copy(assets / "bin" / "print-flag", self.bin / "print-flag")
        os.chmod(self.bin / "print-flag", 0o755)
        (self.run / "client_body").mkdir()
        (self.run / "proxy").mkdir()
        (self.root / "nginx.conf").write_text(f"""daemon off;
error_log {self.run / 'nginx-error.log'} notice;
pid {self.run / 'nginx.pid'};
events {{
    worker_connections 64;
}}
http {{
    client_body_temp_path {self.run / 'client_body'};
    proxy_temp_path {self.run / 'proxy'};
    access_log off;
    server {{
        listen 127.0.0.1:{self.front};
        server_name _;
        location / {{
            proxy_pass http://127.0.0.1:{self.back};
            proxy_http_version 1.1;
            proxy_set_header Host $host;
        }}
    }}
}}
""")

    def start_front(self) -> None:
        self.front_proc = subprocess.Popen(
            [self.nginx, "-c", str(self.root / "nginx.conf")],
            stdout=open(self.run / "nginx.log", "ab"), stderr=subprocess.STDOUT,
            start_new_session=True)
        deadline = time.time() + 20
        while time.time() < deadline:
            if tcp_up("127.0.0.1", self.front):
                return
            if self.front_proc.poll() is not None:
                raise RuntimeError(f"nginx exited early: {self.front_proc.returncode}")
            time.sleep(0.2)
        raise RuntimeError("nginx did not come up")

    def start_back(self, php: str, ini: str | None, tag: str) -> None:
        log = open(self.run / f"php-{tag}.log", "ab")
        env = dict(os.environ)
        env["PATH"] = f"{self.bin}:{env['PATH']}"
        if ini:
            env["PHP_INI_SCAN_DIR"] = ini
        # One single process, no PHP_CLI_SERVER_WORKERS, for determinism.
        self.back_proc = subprocess.Popen(
            [php, "-S", f"127.0.0.1:{self.back}", "-t", str(self.public)],
            stdout=log, stderr=subprocess.STDOUT, env=env, start_new_session=True)
        deadline = time.time() + 30
        while time.time() < deadline:
            if tcp_up("127.0.0.1", self.back):
                return
            if self.back_proc.poll() is not None:
                code = self.back_proc.returncode
                raise RuntimeError(f"php exited early ({code}); see {log.name}")
            time.sleep(0.2)
        raise RuntimeError(f"php backend {tag} did not come up")

    def stop_back(self) -> None:
        if self.back_proc and self.back_proc.poll() is None:
            self.back_proc.terminate()
            try:
                self.back_proc.wait(10)
            except subprocess.TimeoutExpired:
                self.back_proc.kill()
                self.back_proc.wait(10)
        self.back_proc = None

    def stop_front(self) -> None:
        if self.front_proc and self.front_proc.poll() is None:
            self.front_proc.terminate()
            try:
                self.front_proc.wait(10)
            except subprocess.TimeoutExpired:
                self.front_proc.kill()
                self.front_proc.wait(10)
        self.front_proc = None

    def back_alive(self) -> bool:
        return self.back_proc is not None and self.back_proc.poll() is None

    def back_log(self, tag: str) -> str:
        return (self.run / f"php-{tag}.log").read_text(errors="replace")


def run_poc(poc: Path, url: str, out: Path) -> tuple[int, str, dict | None]:
    # The PoC insists on creating its own output directory; on a crash before
    # that, run.json will not exist and the caller treats it as no evidence.
    try:
        proc = subprocess.run(
            [sys.executable, str(poc), "--url", url, "--output-dir", str(out)],
            capture_output=True, text=True, timeout=600)
        returncode, stdout = proc.returncode, proc.stdout + proc.stderr
    except subprocess.TimeoutExpired as exc:
        returncode, stdout = 124, f"(PoC timed out: {exc})"
    run_json = out / "run.json"
    record = json.loads(run_json.read_text()) if run_json.exists() else None
    return returncode, stdout, record


def native_arm(lab: Lab, poc: Path, php: str, ini: str | None,
               attempts: int, evidence: Path) -> dict:
    """The exploit must succeed on the unpatched baseline build."""
    url = f"http://127.0.0.1:{lab.front}/php-version.php"
    runs = []
    for attempt in range(1, attempts + 1):
        tag = f"native-{attempt:02d}"
        lab.stop_back()
        try:
            lab.start_back(php, ini, tag)
        except RuntimeError as exc:
            runs.append({"attempt": attempt, "error": f"relaunch failed: {exc}"})
            continue
        out = evidence / tag
        returncode, stdout, record = run_poc(poc, url, out)
        verified = bool(record and record.get("final", {}).get("execution_proof_verified"))
        runs.append({"attempt": attempt, "returncode": returncode,
                     "server_alive_after": lab.back_alive(),
                     "execution_proof_verified": verified})
        print(f"[native {attempt:02d}] exit={returncode} "
              f"verified={verified} alive={lab.back_alive()}", flush=True)
        print("[native stdout] " + stdout.replace("\n", " | ")[:400], flush=True)
        if verified:
            return {"outcome": "exploit-success", "attempts": runs,
                    "verified_attempt": attempt}
    return {"outcome": "exploit-failed", "attempts": runs}


def filc_arm(lab: Lab, poc: Path, php: str, ini: str | None,
             runs_wanted: int, evidence: Path) -> dict:
    """The exploit must be thwarted by the Fil-C build every single time."""
    url = f"http://127.0.0.1:{lab.front}/php-version.php"
    runs = []
    for attempt in range(1, runs_wanted + 1):
        tag = f"filc-{attempt:02d}"
        lab.stop_back()
        try:
            lab.start_back(php, ini, tag)
        except RuntimeError as exc:
            runs.append({"attempt": attempt, "error": f"relaunch failed: {exc}"})
            continue
        out = evidence / tag
        returncode, stdout, record = run_poc(poc, url, out)
        log = lab.back_log(tag)
        # Persist the server log so the check's output alone carries the
        # panic message and backtrace of the capability trap.
        (out / "php-server.log").write_text(log, errors="replace")
        panicked = PANIC in log
        trap_in_parse_path = TRAP_SITE in log
        heap_leaked = "strict Zend base" in stdout
        executed = bool(record and record.get("final", {}).get("execution_proof_verified"))
        heap_abort = bool(
            record and str(record.get("error", "")).startswith("RuntimeError: heap:"))
        # The producer must still walk into its OOM: the vulnerability is
        # there and gets exercised; Fil-C stops the corrupted read after it.
        heap_json = out / "heap.json"
        producer_oom = False
        if heap_json.exists():
            producer = json.loads(heap_json.read_text()).get("producer")
            producer_oom = bool(producer and producer.get("oom"))
        thwarted = (panicked and trap_in_parse_path and not heap_leaked
                    and not executed and heap_abort and producer_oom)
        runs.append({
            "attempt": attempt, "returncode": returncode,
            "producer_oom": producer_oom,
            "filc_panic": panicked, "trap_in_parse_path": trap_in_parse_path,
            "heap_leaked": heap_leaked, "executed": executed,
            "heap_stage_abort": heap_abort,
            "server_alive_after": lab.back_alive(),
            "thwarted": thwarted,
        })
        print(f"[filc {attempt:02d}] exit={returncode} producer_oom={producer_oom} "
              f"panic={panicked} trap_site={trap_in_parse_path} leaked={heap_leaked} "
              f"executed={executed} alive={lab.back_alive()} "
              f"thwarted={thwarted}", flush=True)
        print("[filc stdout] " + stdout.replace("\n", " | ")[:400], flush=True)
        if not thwarted:
            return {"outcome": "not-thwarted", "runs": runs}
    return {"outcome": "thwarted", "runs": runs}


def main() -> int:
    parser = argparse.ArgumentParser(
        description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--native", required=True, help="native php binary")
    parser.add_argument("--native-ini", help="PHP_INI_SCAN_DIR for the native build")
    parser.add_argument("--filc", required=True, help="Fil-C php binary")
    parser.add_argument("--filc-ini", help="PHP_INI_SCAN_DIR for the Fil-C build")
    parser.add_argument("--nginx", required=True, help="nginx binary")
    parser.add_argument("--poc", required=True, help="the adapted PoC")
    parser.add_argument("--assets", required=True, help="lab assets directory")
    parser.add_argument("--lab", required=True, help="scratch lab directory")
    parser.add_argument("--out", required=True, help="evidence output directory")
    parser.add_argument("--native-attempts", type=int, default=8)
    parser.add_argument("--filc-runs", type=int, default=3)
    parser.add_argument("--front-port", type=int, default=18166)
    parser.add_argument("--back-port", type=int, default=8000)
    args = parser.parse_args()

    lab_dir = Path(args.lab)
    lab_dir.mkdir(parents=True, exist_ok=True)
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    evidence = out / "attempts"
    evidence.mkdir()
    lab = Lab(lab_dir, args.nginx, args.front_port, args.back_port)
    lab.prepare(Path(args.assets))

    # Native first: a failing baseline means the PoC stopped being a real
    # exploit for this PHP and the Fil-C result is meaningless.
    lab.start_front()
    summary: dict = {}
    try:
        native = native_arm(lab, Path(args.poc), args.native, args.native_ini,
                            args.native_attempts, evidence)
        summary["native"] = native
        (out / "native.json").write_text(json.dumps(native, indent=2) + "\n")
        if native["outcome"] != "exploit-success":
            print(f"FAIL: native baseline did not fall to the exploit "
                  f"({native['outcome']}); see {out}", flush=True)
            return 1
        print(f"native arm: exploit succeeded "
              f"(attempt {native['verified_attempt']})", flush=True)

        filc = filc_arm(lab, Path(args.poc), args.filc, args.filc_ini,
                        args.filc_runs, evidence)
        summary["filc"] = filc
        (out / "filc.json").write_text(json.dumps(filc, indent=2) + "\n")
        if filc["outcome"] != "thwarted":
            print(f"FAIL: Fil-C build was not exploited-proof in every run "
                  f"({filc['outcome']}); see {out}", flush=True)
            return 1
        print(f"filc arm: thwarted in {len(filc['runs'])}/{len(filc['runs'])} runs "
              f"({PANIC})", flush=True)
    finally:
        lab.stop_back()
        lab.stop_front()

    summary["verdict"] = ("Fil-C PHP 8.4.25 thwarts the StealMyBitcoin "
                          "exploit; the native 8.4.25 baseline falls to it.")
    (out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print("VERIFIED: " + summary["verdict"], flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
