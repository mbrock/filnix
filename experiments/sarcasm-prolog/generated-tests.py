"""Bounded, reproducible differential tests against real x86-64 execution.

The oracle assembles the original source with the native compiler. It does
not import the Prolog instruction table or reuse the C emitter's arithmetic.
Every result is compared, without a checksum or tolerance.
"""
import random
import sys

from native_oracle import check_programs
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

check_programs(programs, translator, filcc, native_cc, assembler, variants=[
    ("grouped", []), ("separate", ["--no-coalesce"]),
    ("linear-grouped", ["--linear"]), ("linear-separate", ["--linear", "--no-coalesce"]),
])
