"""Run installed CAVA's raw output with silent FIFO input and no sound hardware."""
import os
from pathlib import Path
import selectors
import signal
import subprocess
import sys
import tempfile
import time

cava, libc = sys.argv[1:]
with tempfile.TemporaryDirectory(prefix="filnix-cava-") as directory:
    root = Path(directory)
    config = root / "config"
    config.write_text("""
[general]
bars = 8
framerate = 30
[input]
method = fifo
source = /dev/zero
sample_rate = 44100
sample_bits = 16
[output]
method = raw
raw_target = /dev/stdout
data_format = ascii
ascii_max_range = 1000
""")
    env = {k: v for k, v in os.environ.items() if k != "LD_LIBRARY_PATH"}
    env.update(HOME=directory, XDG_CONFIG_HOME=directory, FUGC_THREADS="2")
    with (root / "stderr").open("w+") as errors:
        child = subprocess.Popen([cava, "-p", str(config)], env=env,
                                 stdout=subprocess.PIPE, stderr=errors)
        try:
            frames = b""
            deadline = time.monotonic() + 15
            with selectors.DefaultSelector() as selector:
                selector.register(child.stdout, selectors.EVENT_READ)
                while frames.count(b"\n") < 3:
                    assert child.poll() is None, "CAVA exited during startup"
                    assert time.monotonic() < deadline, "CAVA produced no frames"
                    if selector.select(0.1):
                        frames += os.read(child.stdout.fileno(), 4096)
            for line in frames.splitlines()[:3]:
                values = [int(value) for value in line.split(b";") if value]
                assert len(values) == 8 and all(value == 0 for value in values), values
            maps = Path(f"/proc/{child.pid}/maps").read_text().splitlines()
            loaded = [line for line in maps if "/lib/libc.so.6666" in line]
            assert loaded and all(libc in line for line in loaded)
            child.terminate()
            # CAVA cleans up, restores SIG_DFL and re-raises the received signal.
            result = child.wait(timeout=10)
            assert result == -signal.SIGTERM, f"CAVA shutdown failed: {result}"
            print("CAVA: shared libc, config/resources, eight-bar raw output and shutdown passed")
        except BaseException:
            errors.flush()
            errors.seek(0)
            print(errors.read(), file=sys.stderr)
            raise
        finally:
            if child.poll() is None:
                child.kill()
                child.wait()
