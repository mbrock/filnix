"""Small permanent malformed-source fixtures with bounded CLI execution."""
from pathlib import Path
import subprocess
import sys

translator = sys.argv[1]
prefix = "probe: #! unsigned long(ptr, unsigned long)\n"
cases = [
    ("unknown-opcode", "ud2\n", "unsupported_instruction(ud2)"),
    ("undefined", "ret\n", "uninitialized_register(rax)"),
    ("missing-return", "movq $1,%rax\n", "missing_return"),
    ("pointer-as-integer", "addq $1,%rdi; ret\n", "register_type(rdi"),
    ("integer-copy-as-pointer", "movq %rsi,%r8; movq (%r8),%rax; ret\n", "register_type(r8"),
    ("narrow-pointer-copy", "movl %edi,%eax; ret\n", "register_type(rdi"),
    ("integer-lea-base", "leaq (%rsi),%rax; ret\n", "register_type(rsi"),
    ("pointer-lea-index", "leaq (%rdi,%rdi,1),%rax; ret\n", "register_type(rdi"),
    ("integer-as-pointer", "movq (%rsi),%rax; ret\n", "register_type(rsi"),
    ("width", "movl %rax,%eax; ret\n", "register_width(rax"),
    ("partial-register", "movq %ah,%rax; ret\n", "unsupported_register(ah)"),
    ("shift-register", "shlq %rcx,%rax; ret\n", "immediate_shift_required"),
    ("shift-range", "shlq $256,%rax; ret\n", "out_of_range(shift_immediate"),
    ("binary-range", "addq $2147483648,%rax; ret\n", "out_of_range(arithmetic_immediate"),
    ("move-range", "movl $4294967296,%eax; ret\n", "out_of_range(move_immediate"),
    ("scale", "movq (%rdi,%rsi,3),%rax; ret\n", "invalid_scale(3)"),
    ("negative-offset", "movq -1(%rdi),%rax; ret\n", "out_of_range(displacement"),
    ("symbolic-offset", "movq mystery(%rdi),%rax; ret\n", "constant_expression_required"),
    ("pointer-store", "movq %rdi,(%rdi); ret\n", "register_type(rdi"),
    ("store-range", "movq $2147483648,(%rdi); ret\n", "out_of_range(store_immediate"),
    ("store-width", "movq %esi,(%rdi); ret\n", "register_width(esi"),
    ("store-memory-source", "movq (%rdi),8(%rdi); ret\n", "integer_source_required"),
    ("unsupported-write", "addq $1,(%rdi); ret\n", "unsupported_memory_destination"),
    ("directive", ".p2align 4\n", "unsupported_directive"),
    ("octal", "movq $08,%rax; ret\n", "unexpected_character"),
    ("quote", '.ascii "unterminated\n', "unexpected_character"),
    ("separator", "movq $1,%rax ret\n", "statement_syntax"),
    ("ret-operands", "ret $8\n", "operand_count"),
]
for name, body, reason in cases:
    path = Path(f"invalid-{name}.s")
    path.write_text(prefix + body)
    result = subprocess.run([translator, str(path)], capture_output=True, timeout=10)
    assert result.returncode != 0 and not result.stdout, (name, result)
    message = result.stderr.decode()
    assert f"{path}:2:" in message and reason in message, (name, message, reason)

sample = "input.s"
for options, expected in [
    (["--explain"], ["8 bytes rejected", "ordering barrier", "4 bytes accepted"]),
    (["--explain", "--no-coalesce"], ["grouping disabled"]),
    (["--emit-effects"], ["read(register(rdi,64),pointer)", "alignment(1)", "zero_extend(64)", "preserved"]),
]:
    result = subprocess.run([translator, *options, sample], capture_output=True, text=True, timeout=10)
    assert result.returncode == 0 and not result.stderr, result
    assert all(text in result.stdout for text in expected), result.stdout
conflict = subprocess.run([translator, "--emit-c", "--explain", sample], capture_output=True, timeout=10)
assert conflict.returncode != 0 and not conflict.stdout
assert b"conflicting_output_modes" in conflict.stderr
help_result = subprocess.run([translator, "--help"], capture_output=True, timeout=10)
assert help_result.returncode == 0 and b"--emit-effects" in help_result.stdout
print(f"diagnostics: {len(cases)} rejected inputs, source locations and inspection modes checked")
