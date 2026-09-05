import resource
import subprocess

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
for mode in ("null", "oob", "oob-plain", "overflow"):
    result = subprocess.run(["./runtime", mode], capture_output=True, timeout=15)
    assert result.returncode < 0, (mode, result.returncode, result.stderr)
    if mode != "overflow":
        assert b"filc safety error" in result.stderr, (mode, result.stderr)
print("safety checks: ok")
