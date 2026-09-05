import resource
import subprocess

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
for mode in ("null", "oob", "oob-plain", "overflow", "pointer-overflow",
             "pointer-null", "pointer-missing-capability", "pointer-oob",
             "pointer-oob-plain", "pointer-freed", "store-null", "store-overflow",
             "store-missing-capability", "store-readonly", "store-oob", "store-oob-plain", "store-freed"):
    result = subprocess.run(["./runtime", mode], capture_output=True, timeout=15)
    assert result.returncode < 0, (mode, result.returncode, result.stderr)
    if "overflow" not in mode:
        assert b"filc safety error" in result.stderr, (mode, result.stderr)
    if mode == "store-readonly":
        assert b"read-only" in result.stderr, result.stderr
print("safety checks: ok")
