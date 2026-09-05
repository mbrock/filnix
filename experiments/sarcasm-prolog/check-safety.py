"""Verify conditional fault behavior while protection analysis stays advisory."""
import resource
import subprocess

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
modes = ["null", "freed", "cover-tail", "checked-arm-tail", "unchecked-arm-tail",
         "readonly", "index-overflow", "local-loop-tail"]
for variant in range(2):
    for mode in modes:
        result = subprocess.run(["./check-runtime", mode, str(variant)], capture_output=True, timeout=15)
        assert result.returncode < 0, (mode, variant, result)
        if mode != "index-overflow":
            assert b"filc safety error" in result.stderr, (mode, result.stderr)
        if mode == "readonly":
            assert b"read-only" in result.stderr, result.stderr
print(f"check reuse safety: {len(modes)} failure modes in both variants")
