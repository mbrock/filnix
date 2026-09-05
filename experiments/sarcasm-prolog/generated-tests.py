"""Bounded, reproducible differential tests against real x86-64 execution.

The oracle assembles the original source with the native compiler. It does
not import the Prolog instruction table or reuse the C emitter's arithmetic.
Every result is compared, without a checksum or tolerance.
"""
import json
import os
from pathlib import Path
import random
import resource
import struct
import subprocess
import sys

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
translator, filcc, native_cc, assembler = sys.argv[1:]
rng = random.Random(0xF11C)
programs = []


def add(label, body):
    programs.append((f"probe_{len(programs)}", label, body))


base = ["movq %rsi, %rax", "movq $0xfedcba9876543210, %rcx",
        "movq $0x1020304050607080, %rdx", "movq %rsi, %r8"]
for op, width, dest in [("movzbl", 1, "eax"), ("movzwl", 2, "eax"),
                         ("movl", 4, "eax"), ("movq", 8, "rax")]:
    for scale in [1, 2, 4, 8]:
        add(f"{op}, scale {scale}", ["andq $15, %rsi", f"{op} 3(%rdi,%rsi,{scale}), %{dest}"])

for suffix, width, dest, src in [("l", 32, "eax", "ecx"), ("q", 64, "rax", "rcx")]:
    for operand in [f"%{src}", "$0", "$-1", f"${(1 << width)-1}"]:
        add(f"mov{suffix} {operand}", base + [f"mov{suffix} {operand}, %{dest}"])
    for op in ["add", "xor", "or", "and"]:
        for operand in [f"%{src}", "$0", "$-1", "$2147483647", "$-2147483648"]:
            add(f"{op}{suffix} {operand}", base + [f"{op}{suffix} {operand}, %{dest}"])
    for op in ["shl", "shr"]:
        for count in [0, 1, 2, 31, 32, 63, 64, 65, 255]:
            add(f"{op}{suffix} count {count}", base + [f"{op}{suffix} ${count}, %{dest}"])

# These interact with the grouping pass, rather than only scalar lowering.
for widths in [(1, 1), (2, 2), (4, 4), (2, 1, 1), (1, 1, 2), (1, 2, 1), (1, 1, 1)]:
    body = ["andq $15, %rsi"]
    offset = 0
    regs = [("eax", "rax"), ("ecx", "rcx"), ("edx", "rdx"), ("r8d", "r8")]
    for i, w in enumerate(widths):
        op = {1: "movzbl", 2: "movzwl", 4: "movl"}[w]
        body.append(f"{op} {offset}(%rdi,%rsi,8), %{regs[i][0]}")
        offset += w
    for i in range(1, len(widths)):
        body.append(f"xorq %{regs[i][1]}, %rax")
    add(f"adjacent widths {widths}", body)

# The load changes the register used as the next load's index. Their textual
# operands look alike but their address values are distinct.
add("load overwrites index", ["andq $15, %rsi", "movzbl (%rdi,%rsi,1), %esi",
                             "andq $15, %rsi", "movzbl 1(%rdi,%rsi,1), %eax"])
for scale in [1, 2, 4, 8]:
    for dest in ["rsi", "r8", "rdi"]:
        add(f"pointer copy/lea, scale {scale}, destination {dest}", [
            "andq $15,%rsi", "movq %rdi,%r8", f"leaq 3(%r8,%rsi,{scale}),%{dest}",
            f"movq %{dest},%r9", "movzwl (%r9),%eax", "movzwl 2(%r9),%ecx", "xorq %rcx,%rax"])
add("pointer self-copy and overwrite", ["movq %rdi,%rdi", "leaq 2(%rdi),%rdi",
    "movq %rdi,%rax", "movzbl (%rax),%eax"])
add("pointer copy becomes integer", ["movq %rdi,%rax", "movq %rsi,%rax"])
for op, source in [("movl", "esi"), ("movq", "rsi")]:
    for offset in [0, 1, 3, 7]:
        add(f"{op} register store, offset {offset}", [f"{op} %{source},{offset}(%rdi)",
            f"movq {offset}(%rdi),%rax"])
    for immediate in [0, -1, -2147483648, 4294967295 if op == "movl" else 2147483647]:
        add(f"{op} immediate store {immediate}", [f"{op} ${immediate},1(%rdi)", "movq 1(%rdi),%rax"])
add("overlapping stores and reads", ["movq (%rdi),%rax", "movq %rax,1(%rdi)",
    "movl 1(%rdi),%ecx", "addl %esi,%ecx", "movl %ecx,2(%rdi)", "movq 1(%rdi),%rax"])
add("store preserves register", ["movq %rsi,(%rdi)", "movq %rsi,%rax"])
add("store through derived pointer", ["movq %rdi,%r8", "leaq 7(%r8),%r9",
    "movq %rsi,(%r9)", "movq (%r9),%rax"])
for n in range(40):
    body = base.copy()
    for _ in range(rng.randrange(3, 14)):
        suffix = rng.choice(["l", "q"])
        regs = ["eax", "ecx", "edx", "r8d"] if suffix == "l" else ["rax", "rcx", "rdx", "r8"]
        dest = rng.choice(regs)
        op = rng.choice(["mov", "add", "xor", "or", "and", "shl", "shr"])
        source = f"${rng.randrange(256)}" if op in ["shl", "shr"] else rng.choice(
            [f"%{rng.choice(regs)}", f"${rng.randrange(-2147483648, 2147483648)}"])
        body.append(f"{op}{suffix} {source}, %{dest}")
    add(f"mixed program seed 0xf11c, case {n}", body)

assembly = [".text"]
for name, label, body in programs:
    assembly += [f"# {label}", f".globl {name}", f".type {name}, @function",
                 f"{name}: #! unsigned long(ptr, unsigned long)", *body, "ret"]
assembly += ['.section .note.GNU-stack,"",@progbits']
Path("generated.s").write_text("\n".join(assembly) + "\n")
Path("generated-cases.json").write_text(json.dumps(programs, indent=2) + "\n")
declarations = "\n".join(f"uint64_t {name}(const unsigned char *, uint64_t);" for name, _, _ in programs)
names = ",".join(name for name, _, _ in programs)
Path("generated.c").write_text("""#include <stdint.h>
#include <stdio.h>
""" + declarations + "\ntypedef uint64_t (*fn)(const unsigned char *, uint64_t);\nfn functions[]={" + names + "};\n" + r"""
int main(void) {
  unsigned char bytes[256];
  uint64_t state=42, values[64]={0,1,2,31,32,63,64,65,255,256,
    UINT64_C(0x7fffffff), UINT64_C(0x80000000), UINT64_C(0xffffffff),
    UINT64_C(0x100000000), UINT64_C(0x7fffffffffffffff),
    UINT64_C(0x8000000000000000), UINT64_MAX};
  for (unsigned i=17;i<64;i++) {
    state=state*UINT64_C(6364136223846793005)+1;
    values[i]=state;
  }
  for (unsigned f=0;f<sizeof functions/sizeof functions[0];f++)
    for (unsigned v=0;v<64;v++) for (unsigned alignment=0;alignment<4;alignment++) {
      for (unsigned i=0;i<sizeof bytes;i++) bytes[i]=(unsigned char)(i*179+31+v);
      uint64_t result=functions[f](bytes+alignment,values[v]);
      if (fwrite(&result,sizeof result,1,stdout)!=1) return 1;
      if (fwrite(bytes,sizeof bytes,1,stdout)!=1) return 1;
    }
}
""")


def run(args, *, output=None, limit=60):
    with open(output, "wb") if output else open(os.devnull, "wb") as stream:
        result = subprocess.run(args, stdout=stream, stderr=subprocess.PIPE, timeout=limit)
    if result.returncode:
        raise AssertionError((args, result.returncode, result.stderr.decode(errors="replace")))


run([native_cc, "-O2", "generated.c", "generated.s", "-o", "native-reference"])
run(["./native-reference"], output="native-results.bin", limit=15)
expected = Path("native-results.bin").read_bytes()
record_size = 8 + 256  # Return value plus the entire buffer, including guard bytes.
records = len(programs) * 64 * 4
assert len(expected) == records * record_size
for mode, options in [("grouped", []), ("separate", ["--no-coalesce"])]:
    run([translator, *options, "generated.s"], output=f"generated-{mode}.s")
    run([assembler, f"generated-{mode}.s", "-o", f"generated-{mode}.o"])
    run([filcc, "-O2", "generated.c", f"generated-{mode}.o", "-o", f"translated-{mode}"])
    run([f"./translated-{mode}"], output=f"{mode}-results.bin", limit=15)
    actual = Path(f"{mode}-results.bin").read_bytes()
    assert len(actual) == len(expected), (mode, len(actual), len(expected))
    for i in range(records):
        start = i * record_size
        a, b = expected[start:start + record_size], actual[start:start + record_size]
        if a != b:
            p = i // 256
            byte = next(j for j in range(record_size) if a[j] != b[j])
            difference = (("return", struct.unpack_from("<Q", a)[0], struct.unpack_from("<Q", b)[0])
                          if byte < 8 else ("memory byte", byte - 8, a[byte], b[byte]))
            raise AssertionError((mode, programs[p], "value index", (i % 256)//4,
                                  "alignment", i % 4, "native/translated", difference))
print(f"native differential: {len(programs)} programs, {records} return-and-memory results per variant")
