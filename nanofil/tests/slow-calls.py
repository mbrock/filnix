#!/usr/bin/env python3
"""Exercise actual CLI-emitted save stubs, including a fail-first mutation.

The wrapped native helpers destroy both full registers, check arguments and
stack alignment, and return a distinct result. No Fil-C runtime is needed
for this isolated native ABI test; run-c.sh covers the real helpers and GC.
"""
import os
from pathlib import Path
import re
import shlex
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
COMPILER = HERE.parent / "bin/nanofil"
HELPERS = ("filc_pollcheck_slow", "filc_store_barrier_for_lower_slow",
           "filc_object_ensure_aux_ptr_outline")


def emission(*options, env):
    return subprocess.check_output(
        [str(COMPILER), "-O", *options, "compile", str(HERE / "filc/pointer-effects.ir")],
        env=env, stdin=subprocess.DEVNULL, text=True)


def main():
    env = dict(os.environ)
    env.pop("NANOFIL_STATE", None)
    env.pop("NANOFIL_SLOW_CALLS", None)
    reference = emission(env=env)
    assert ".Lnanofil_save_" not in reference
    # emit-terms exposes chunk boundaries to the Gallina mirror, not
    # just flattened assembly. Reference has no synthetic stub chunk.
    for options in ([], ["-O"]):
        terms = subprocess.check_output(
            [str(COMPILER), *options, "emit-terms", str(HERE / "filc/pointer-effects.ir")],
            env=env, stdin=subprocess.DEVNULL, text=True).splitlines()
        assert terms[-1] == "[section(note_gnu_stack)]."
        assert terms[-2] != "[].", "reference emitted an empty save-stub chunk"
    env["NANOFIL_SLOW_CALLS"] = "save"
    assert emission("--slow-calls=reference", env=env) == reference
    saved = emission("--slow-calls=save", env=env)
    stubs = []
    for helper in HELPERS:
        label = ".Lnanofil_save_" + helper
        assert saved.count(label + ":\n") == 1
        block = re.search(re.escape(label) + r":\n(.*?)\t.size " + re.escape(label),
                          saved, re.S).group(1)
        assert f"call {helper}@PLT\n" in block
        stubs.append(label + ":\n" + block)
    assembly = ".text\n" + "".join(stubs)
    assembly += ".globl probe\nprobe:\n pushq %rbp\n movq %rsp,%rbp\n"
    # Repeated calls also exercise a lazy PLT resolver with a shared helper.
    for helper in HELPERS * 2:
        assembly += f"""
 movabsq $0x12345678abcdef01,%r10
 movabsq $0xfedcba9876543210,%r11
 movl $11,%edi
 movl $37,%esi
 call .Lnanofil_save_{helper}
 cmpq $48,%rax
 jne bad
 movabsq $0x12345678abcdef01,%rcx
 cmpq %rcx,%r10
 jne bad
 movabsq $0xfedcba9876543210,%rcx
 cmpq %rcx,%r11
 jne bad
 cmpq %rbp,%rsp
 jne bad
"""
    assembly += " xorl %eax,%eax\n leave\n ret\nbad:\n movl $1,%eax\n leave\n ret\n"
    assembly += '.section .note.GNU-stack,"",@progbits\n'
    helpers = ".text\n"
    for helper in HELPERS:
        helpers += f".globl {helper}\n{helper}:\n"
    helpers += """
 leaq 8(%rsp),%rax
 testq $15,%rax
 jnz alignment_bad
 cmpq $11,%rdi
 jne alignment_bad
 cmpq $37,%rsi
 jne alignment_bad
 movq $-1,%r10
 movq $-2,%r11
 movq %rdi,%rax
 addq %rsi,%rax
 ret
alignment_bad:
 movq $-1,%rax
 ret
.section .note.GNU-stack,"",@progbits
"""
    cc = shlex.split(os.environ.get("CC", "cc"))
    with tempfile.TemporaryDirectory() as work:
        work = Path(work)
        (work / "main.c").write_text("extern int probe(void); int main(void) { return probe(); }\n")
        (work / "helpers.s").write_text(helpers)
        subprocess.run([*cc, "-shared", "-fPIC", "-o", str(work / "helpers.so"),
                        str(work / "helpers.s")], check=True)
        for mutation in (False, True):
            source = assembly.replace("popq %r10", "addq $8, %rsp") if mutation else assembly
            (work / "probe.s").write_text(source)
            subprocess.run([*cc, "-o", str(work / "probe"), str(work / "main.c"),
                            str(work / "probe.s"), str(work / "helpers.so"),
                            "-Wl,-rpath," + str(work)], check=True)
            status = subprocess.run([str(work / "probe")]).returncode
            assert status == int(mutation), (mutation, status)
    print("slow calls: native arguments/alignment/results/full-register restoration; missing restore rejected")


if __name__ == "__main__":
    main()
