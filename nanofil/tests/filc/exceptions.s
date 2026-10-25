# Native Fil-C ABI probes, derived from staging af813053's
# filc_runtime.h and FilPizlonator.cpp; see docs/abi-findings.md.
# thread->top_frame is +16; register exception is AL bit 0; buffered
# exception is byte 0 of the return buffer (thread moves to RSI).
# No fake thread, frames or unwind state: use the real C caller's thread.
# No C++ throw/unwind: raise_* only synthesize the ABI exception flag.

        .text
.Lraise_reg:
        movl $1, %eax
        ret
.Lraise_buffer:
        movb $1, (%rdi)
        movq %rdi, %rax
        ret

# Each probe consumes the synthetic exception and returns an ordinary 1
# to C. Trap immediately if the flag or real parent frame was lost, before
# any call can overwrite the dead nanofil frame and obscure the failure.
        .macro probe name, buffered
.L\name:
        pushq %rbx
        pushq %r12
        subq $40, %rsp
        movq %rdi, %rbx
        movq 16(%rbx), %r12
        .if \buffered
        movb $0, (%rsp)
        movq %rbx, %rsi
        movq %rsp, %rdi
        xorl %edx, %edx
        call pizlonatedFI90_exception_buffer
        movzbl (%rsp), %eax
        .else
        xorl %esi, %esi
        xorl %edx, %edx
        xorl %ecx, %ecx
        call pizlonatedFI1066_exception_reg
        .endif
        testb $1, %al
        jz .Lbad_exception
        cmpq %r12, 16(%rbx)
        jne .Lbad_exception
        movl $1, %edx
        xorl %eax, %eax
        addq $40, %rsp
        popq %r12
        popq %rbx
        ret
        .endm
        probe probe_reg, 0
        probe probe_buffer, 1
.Lbad_exception:
        ud2

# Both probes are long(void). Generic entries put that scalar in the
# inline CC payload buffer, clear its aux and return its size in RDX.
        .macro generic name
.Lgeneric_\name:
        pushq %rbx
        movq %rdi, %rbx
        call .L\name
        movq %rdx, 128(%rbx)
        movq $0, 384(%rbx)
        movl $8, %edx
        popq %rbx
        ret
        .endm
        generic probe_reg
        generic probe_buffer

# Ordinary getters/function objects let clang's and nanofil's real thunks
# dispatch to the fixtures. Signatures: long(void)=2; {long,ptr}(void)=90.
# The object flags are GLOBAL|READONLY|FUNCTION, with its payload as aux.
        .macro expose name, signature, fast, generic
        .text
        .globl pizlonated_\name
        .type pizlonated_\name, @function
pizlonated_\name:
        leaq .Lobject_\name+16(%rip), %rax
        movq %rax, %rdx
        ret
        .size pizlonated_\name, .-pizlonated_\name
        .section .data.rel.ro,"aw",@progbits
        .p2align 4
.Lobject_\name:
        .quad .Lobject_\name+16
        .quad (.Lobject_\name+16)+36873221949095936
        .quad \fast
        .quad \generic
        .quad \signature
        .endm
        expose raise_reg, 2, .Lraise_reg, .Lraise_reg
        expose raise_buffer, 90, .Lraise_buffer, .Lraise_reg
        expose probe_reg, 2, .Lprobe_reg, .Lgeneric_probe_reg
        expose probe_buffer, 2, .Lprobe_buffer, .Lgeneric_probe_buffer
        .section .note.GNU-stack,"",@progbits
