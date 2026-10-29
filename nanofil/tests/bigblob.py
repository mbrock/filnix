#!/usr/bin/env python3
"""Generate a C file with one large static byte array, written as GLib's
glib-compile-resources writes a resource bundle: a union of the bytes,
a double and a pointer. With FORM `string` (what it writes for gcc and
clang) the bytes are concatenated string literals of 16 octal escapes;
with `braces` (any compiler it does not recognize by name, such as `cc`)
a braced list of octal integer constants, 16 per line. gtk3's
gtkresources.c holds 1.5 MB this way. main hashes the bytes, so
progtest compares nanofil's data with clang's.

Usage: bigblob.py FORM BYTES > file.c
"""
import random
import sys

form, n = sys.argv[1], int(sys.argv[2])
rng = random.Random(n)
out = sys.stdout
out.write("#include <stdio.h>\n")
out.write(
    "static const __attribute__((aligned(8))) union { const unsigned char data[%d];"
    " const double alignment; void * const ptr; } blob = {%s\n"
    % (n + 1, " {" if form == "braces" else "")
)
for i in range(0, n, 16):
    row = [rng.randrange(256) for _ in range(min(16, n - i))]
    if form == "braces":
        sep = ",\n" if i + 16 < n else "\n"
        out.write("  " + ", ".join("0%03o" % b for b in row) + sep)
    else:
        out.write('  "' + "".join("\\%03o" % b for b in row) + '"\n')
out.write("} };\n" if form == "braces" else "};\n")
out.write(
    "int main(void)\n{\n"
    "    unsigned long h = 0;\n"
    "    for (unsigned long i = 0; i < sizeof blob.data; i++)\n"
    "        h = h * 31 + blob.data[i];\n"
    '    printf("%zu %lu\\n", sizeof blob, h);\n'
    "    return 0;\n}\n"
)
