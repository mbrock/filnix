"""Capability and pointer-alignment failures through translated assembly."""
import resource
import subprocess

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
modes = ["fresh-address", "changed-address", "free-pointee", "free-slot",
         "free-slot-write", "null-slot", "null-pointee", "load-align",
         "store-align", "load-oob", "store-oob", "store-readonly",
         "store-overflow", "pointee-oob", "readonly-pointee-write"]
for options in [[], ["plain"]]:
    for mode in modes:
        result = subprocess.run(["./pointer-runtime", mode, *options], capture_output=True, timeout=15)
        assert result.returncode < 0, (mode, options, result)
        if mode != "store-overflow":
            assert b"filc safety error" in result.stderr, (mode, result.stderr)
        if mode == "fresh-address":
            assert b"null object" in result.stderr, result.stderr
        if mode == "changed-address":
            assert b"ptr " in result.stderr and b"null object" not in result.stderr, result.stderr
        if "align" in mode:
            assert b"alignment requirement of 8 bytes" in result.stderr, result.stderr
        if "readonly" in mode:
            assert b"read-only" in result.stderr, result.stderr
print(f"pointer-slot safety: {len(modes)} failure modes checked in both variants")
