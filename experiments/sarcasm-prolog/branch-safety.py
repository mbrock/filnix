"""Branch-selected capabilities must retain bounds, lifetime and permission."""
import resource
import subprocess

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
modes = ["null", "freed", "bounds", "readonly", "checked-origin", "checked-null", "swap-readonly"]
for variant in range(2):
    for choice in range(2):
        for mode in modes:
            result = subprocess.run(["./branch-runtime", mode, str(variant), str(choice)],
                                    capture_output=True, timeout=15)
            assert result.returncode < 0 and b"filc safety error" in result.stderr, (mode, variant, choice, result)
            if "readonly" in mode:
                assert b"read-only" in result.stderr, result.stderr
            if mode == "checked-origin":
                assert b"null object" not in result.stderr, result.stderr
print("branch safety: 7 failure modes, both incoming arms, both variants")
