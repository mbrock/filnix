#!/usr/bin/env python3
"""Send a chunk of Rocq text to a running server.py and print the reply.

    rq.py 'tactics or commands'          run the text
    rq.py -                              run the text read from stdin
    rq.py -f FILE START END              run lines START..END of FILE (1-based, inclusive)

The socket is $RQ_SOCK, default /tmp/rq.sock. The reply drops the REPL's
prompt markup and ends with the time taken and the state number before
the chunk's sentinel; `BackTo N.` returns to any earlier state N.
"""
import os, re, socket, sys

sock = os.environ.get("RQ_SOCK", "/tmp/rq.sock")
args = sys.argv[1:]
if args[0] == "-f":
    lines = open(args[1]).read().split("\n")
    text = "\n".join(lines[int(args[2]) - 1:int(args[3])])
elif args[0] == "-":
    text = sys.stdin.read()
else:
    text = args[0]
c = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
c.connect(sock)
c.sendall(text.encode() + b"\0")
out = b""
while True:
    b = c.recv(65536)
    if not b:
        break
    out += b
s = out.decode(errors="replace")
states = re.findall(r"<prompt>\S+ < (\d+) \|", s)
s = re.sub(r"<prompt>.*?</prompt>", "", s, flags=re.S).replace("\x07", "")
print(s.strip())
if len(states) >= 2:
    print("[state before sentinel: %s]" % states[-2])
