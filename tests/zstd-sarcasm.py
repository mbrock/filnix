"""Cross-check the installed assembly variant with native zstd."""
import random
import subprocess
import sys
r = random.Random(42)
cases = [b"", b"x" * 100000, bytes(range(256)) * 512,
         bytes(r.randrange(16) for _ in range(262144)),
         r.randbytes(131072), b"a test of safe assembly\n" * 10000]

def run(exe, data, *args):
    return subprocess.run([exe, "-q", "-c", *args], input=data,
                          stdout=subprocess.PIPE, check=True).stdout

for data in cases:
    for level in (1, 3, 9):
        for compressor, decoder in ((sys.argv[1], sys.argv[2]), (sys.argv[2], sys.argv[1])):
            encoded = run(compressor, data, f"-{level}")
            assert run(decoder, encoded, "-d") == data
print("36 native/Fil-C cross-codec round trips passed")
