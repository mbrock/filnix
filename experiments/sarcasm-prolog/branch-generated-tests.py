"""Compare flag-dependent control flow with the actual x86 instructions."""
import sys

from native_oracle import check_programs

translator, filcc, native_cc, assembler = sys.argv[1:]
programs = []
conditions = ["e", "ne", "b", "ae", "be", "a", "l", "ge", "le", "g",
              "s", "ns", "o", "no", "p", "np"]


def add(label, body):
    name = f"branch_{len(programs)}"
    # Each fixture uses its own assembler-local label namespace.
    programs.append((name, label, [line.replace(".L", f".L{name}_") for line in body]))


def outcome(condition):
    return [f"j{condition} .Lyes", "movq $0,%rax", "jmp .Ldone",
            ".Lyes:", "movq $1,%rax", ".Ldone:"]


for suffix, width, dest, src in [("l", 32, "eax", "ecx"), ("q", 64, "rax", "rcx")]:
    for condition in conditions:
        for op, immediate in [("cmp", -1), ("test", -1), ("add", 1),
                              ("xor", -1), ("and", 255), ("or", 1),
                              ("shl", 1), ("shr", 1)]:
            add(f"{op}{suffix} ${immediate}; j{condition}", [
                "movq %rsi,%rax", f"{op}{suffix} ${immediate},%{dest}", *outcome(condition)])
        for op in ["cmp", "test", "add"]:
            add(f"{op}{suffix} register; j{condition}", [
                "movq %rsi,%rax", f"movq ${1 << (width-1)},%rcx",
                f"{op}{suffix} %{src},%{dest}", *outcome(condition)])
        add(f"masked zero shift preserves cmp flags, width {width}; j{condition}", [
            "movq %rsi,%rax", f"cmp{suffix} $1,%{dest}",
            f"shl{suffix} ${width},%{dest}", *outcome(condition)])
        # For counts above one, OF is undefined: conditions reading it are
        # rejected separately. These cases consume only defined flags.
        if condition not in ["l", "ge", "le", "g", "o", "no"]:
            for op, count in [("shl", 2), ("shr", 31)]:
                add(f"{op}{suffix} ${count}; j{condition}", [
                    "movq %rsi,%rax", f"{op}{suffix} ${count},%{dest}", *outcome(condition)])
        add(f"flags join from add or compare, width {width}; j{condition}", [
            "movq %rsi,%rax", "testq $1,%rsi", "je .Lleft",
            f"add{suffix} $1,%{dest}", "jmp .Ljoin",
            ".Lleft:", f"cmp{suffix} $1,%{dest}",
            ".Ljoin:", *outcome(condition)])

for condition in conditions:
    for middle in [
        ["movq $1,%rax"],  # The comparison retains its original operands.
        ["addq $1,%rax"],  # New arithmetic replaces the comparison flags.
        ["movq (%rdi),%rax", "movq $0,(%rdi)"],  # Memory accesses preserve flags.
        ["movq $1,%rcx", "leaq (%rdi,%rcx,1),%r8", "movq (%r8),%rax"],
    ]:
        add(f"flag value lifetime; j{condition}; {middle}", [
            "movq %rsi,%rax", "cmpq $-1,%rax", *middle, *outcome(condition)])

add("selected pointer and store branches", [
    "testq $1,%rsi", "je .Lleft", "leaq 13(%rdi),%r8", "jmp .Ljoin",
    ".Lleft:", "leaq 7(%rdi),%r8", ".Ljoin:", "movq %rsi,(%r8)", "movq (%r8),%rax"])
add("pointer swap on one predecessor", [
    "movq %rdi,%r8", "leaq 16(%rdi),%r9", "testq $1,%rsi", "je .Ljoin",
    "movq %r8,%r10", "movq %r9,%r8", "movq %r10,%r9",
    ".Ljoin:", "movq (%r8),%rax", "movq %rax,(%r9)"])
add("check on one predecessor only", [
    "testq $1,%rsi", "je .Ljoin", "movq (%rdi),%rax", ".Ljoin:", "movq (%rdi),%rax"])
add("dead typed-invalid block with a cycle", [
    "movq %rsi,%rax", "jmp .Llive", ".Ldead:", "movq (%rsi),%rax",
    "jmp .Ldead", ".Llive:"])
add("adjacent label aliases and explicit fallthrough", [
    "movq %rsi,%rax", "testq $1,%rsi", "je .Lalias", ".Lfirst:", ".Lalias:",
    "addq $1,%rax", ".Lnext:", "xorq $7,%rax"])

check_programs(programs, translator, filcc, native_cc, assembler, variants=[
    ("grouped", []), ("separate", ["--no-coalesce"]),
    ("flags", ["--no-simplify-conditions"]),
    ("flags-separate", ["--no-simplify-conditions", "--no-coalesce"]),
])
