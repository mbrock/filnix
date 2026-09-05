"""Checks remain effective on later iterations and after pointer backedges."""
import resource
import subprocess

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
modes = ["input-null", "table-null", "output-null", "input-freed", "output-freed", "table-freed",
         "input-oob", "output-oob", "table-oob", "table-tail", "output-readonly", "state-readonly", "state-null",
         "state-short", "alias-oob", "walk-freed", "walk-null", "walk-forged", "walk-bounds"]
for variant in range(2):
    for mode in modes:
        result = subprocess.run(["./decoder-runtime", mode, str(variant)], capture_output=True, timeout=15)
        assert result.returncode < 0 and b"filc safety error" in result.stderr, (mode, variant, result)
        if "readonly" in mode:
            assert b"read-only" in result.stderr, result.stderr
        if mode == "walk-forged":
            assert b"null object" not in result.stderr, result.stderr
print(f"decoder safety: {len(modes)} failure modes checked in both variants")
