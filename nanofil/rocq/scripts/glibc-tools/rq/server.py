#!/usr/bin/env python3
"""Keep one `rocq repl -emacs` alive and run chunks of Rocq text against it.

Recompiling a long proof file to see the next goal costs the whole file
each time. This server loads the file once and then runs each chunk you
send in a few seconds. Start it with start.sh, send chunks with rq.py.

    server.py SOCK [rocq repl options...]    (start.sh runs this)

Each chunk ends with a Redirect sentinel, so the reply arrives when Rocq
has finished the chunk, however long its tactics take.

Rocq keeps executing the sentences that follow an error, which leaves the
proof in a state nobody asked for. So when a chunk prints an error, the
server sends `BackTo` the state that was current before the chunk, and
the reply ends with "[rq: error, rolled back to state N]". A chunk thus
either applies whole or not at all. A chunk that itself starts with
`BackTo` is not rolled back.

Stop the server with `kill "$(cat /tmp/rq.pid)"` (start.sh writes the
PID file). Do not use `pkill -f` or `ps | grep | kill`: the pattern also
matches the shell that runs the command, and kills it.
"""
import os, re, socket, subprocess, sys, threading, time

sock_path = sys.argv[1]
proc = subprocess.Popen(["rocq", "repl", "-emacs", *sys.argv[2:]], stdin=subprocess.PIPE,
                        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, bufsize=0)
buf = bytearray()
lock = threading.Lock()
sentinel = "/tmp/rq_sentinel_%d" % os.getpid()
last_state = [None]


def reader():
    while True:
        b = proc.stdout.read(4096)
        if not b:
            break
        with lock:
            buf.extend(b)


threading.Thread(target=reader, daemon=True).start()


def raw(text):
    """Send text and wait until Rocq has processed all of it."""
    try:
        os.unlink(sentinel + ".out")
    except FileNotFoundError:
        pass
    with lock:
        buf.clear()
    proc.stdin.write((text.rstrip() + "\nRedirect \"%s\" Check tt.\n" % sentinel).encode())
    proc.stdin.flush()
    while not os.path.exists(sentinel + ".out") and proc.poll() is None:
        time.sleep(0.05)
    time.sleep(0.1)
    with lock:
        out = buf.decode(errors="replace")
    states = re.findall(r"<prompt>\S+ < (\d+) \|", out)
    if states:
        last_state[0] = states[-1]
    return out


def run(text):
    t0 = time.time()
    before = last_state[0]
    out = raw(text)
    if "Error" in out and before is not None and not text.lstrip().startswith("BackTo"):
        raw("BackTo %s." % before)
        out += "\n[rq: error, rolled back to state %s]\n" % before
    return out, time.time() - t0


try:
    os.unlink(sock_path)
except FileNotFoundError:
    pass
srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
srv.bind(sock_path)
srv.listen(1)
while True:
    c, _ = srv.accept()
    data = b""
    while not data.endswith(b"\0"):
        chunk = c.recv(65536)
        if not chunk:
            break
        data += chunk
    out, dt = run(data.rstrip(b"\0").decode())
    c.sendall((out + "\n[rq %.2fs]\n" % dt).encode())
    c.close()
