"""Bounded loops and loop-carried values checked against native execution."""
import sys

from native_oracle import check_programs

translator, filcc, native_cc, assembler = sys.argv[1:]
programs = []


def add(label, body):
    name = f"loop_{len(programs)}"
    programs.append((name, label, [line.replace(".L", f".L{name}_").replace(".ENTRY", name) for line in body]))


for suffix, dest in [("l", "edx"), ("q", "rdx")]:
    for op, value in [("add", 1), ("add", -1), ("add", -2147483648),
                      ("xor", -1), ("or", 1), ("and", 255), ("shl", 1), ("shr", 1)]:
        for condition in ["e", "ae", "ge"]:
            add(f"counter loop {op}{suffix}, exit j{condition}", [
                "movq %rsi,%rdx", "andq $15,%rsi", "movq $0,%rax",
                ".Lhead:", "cmpq %rsi,%rax", f"j{condition} .Ldone",
                f"{op}{suffix} ${value},%{dest}", "addq $1,%rax", "jmp .Lhead",
                ".Ldone:", "movq %rdx,%rax"])

add("countdown flags across backedge", [
    "andq $15,%rsi", "movq $0,%rax", "testq %rsi,%rsi", "je .Ldone",
    ".Lhead:", "addq $7,%rax", "addq $-1,%rsi", "jne .Lhead", ".Ldone:"])
add("entry backedge carries changed arguments", [
    "testq %rsi,%rsi", "je .Ldone", "andq $15,%rsi", "leaq 1(%rdi),%rdi",
    "addq $-1,%rsi", "jmp .ENTRY", ".Ldone:", "movzbl (%rdi),%eax"])
add("loop swaps and stores through pointers", [
    "andq $15,%rsi", "movq %rdi,%r8", "leaq 16(%rdi),%r9", "movq $0,%rax",
    ".Lhead:", "cmpq %rsi,%rax", "je .Ldone",
    "movq %r8,%r10", "movq %r9,%r8", "movq %r10,%r9",
    "movq (%r8),%rdx", "addq $1,%rdx", "movq %rdx,(%r9)",
    "addq $1,%rax", "jmp .Lhead", ".Ldone:", "movq (%r8),%rax"])
add("two backedges advance pointer differently", [
    "andq $15,%rsi", "movq %rdi,%r8", "movq $0,%rax", "movq $0,%rcx",
    ".Lhead:", "cmpq %rsi,%rcx", "je .Ldone",
    "movzbl (%r8),%edx", "addq %rdx,%rax", "testq $1,%rcx", "jne .Lodd",
    "leaq 1(%r8),%r8", "addq $1,%rcx", "jmp .Lhead",
    ".Lodd:", "leaq 2(%r8),%r8", "addq $1,%rcx", "jmp .Lhead", ".Ldone:"])
add("loads and stores can alias future input", [
    "andq $15,%rsi", "movq %rdi,%r8", "leaq 3(%rdi),%r9", "movq $0,%rax",
    ".Lhead:", "cmpq %rsi,%rax", "je .Ldone", "movl (%r8),%edx",
    "movl %edx,(%r9)", "leaq 1(%r8),%r8", "leaq 4(%r9),%r9",
    "addq $1,%rax", "jmp .Lhead", ".Ldone:"])
add("nested loops initialize the inner counter each time", [
    "andq $7,%rsi", "movq $0,%rax", "movq $0,%rcx", ".Louter:",
    "cmpq %rsi,%rcx", "je .Ldone", "movq $0,%rdx", ".Linner:",
    "cmpq %rsi,%rdx", "je .Lnext", "addq %rcx,%rax", "addq $1,%rax",
    "addq $1,%rdx", "jmp .Linner", ".Lnext:", "addq $1,%rcx", "jmp .Louter", ".Ldone:"])
add("cycle with two entry points", [
    "andq $7,%rsi", "movq $0,%rax", "testq $1,%rsi", "jne .Lb",
    ".La:", "cmpq %rsi,%rax", "je .Ldone", "addq $1,%rax", "jmp .Lb",
    ".Lb:", "cmpq %rsi,%rax", "je .Ldone", "addq $1,%rax", "jmp .La", ".Ldone:"])

check_programs(programs, translator, filcc, native_cc, assembler, variants=[
    ("grouped", []), ("separate", ["--no-coalesce"]),
    ("flags", ["--no-simplify-conditions"]),
    ("flags-separate", ["--no-simplify-conditions", "--no-coalesce"]),
])
