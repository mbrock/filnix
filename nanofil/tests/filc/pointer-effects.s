# Read-only observation of the pinned runtime's published marking state,
# exactly as the compiler's lower-barrier fast path reads it. Never write
# GC state, object headers, or roots. Allocation and collection are driven
# exclusively by the normal APIs in pointer-effects.c.
        .text
.Lis_marking:
        movq filc_current_marking_state@GOTPCREL(%rip), %rax
        movl (%rax), %edx
        xorl %eax, %eax
        ret
.Lis_marking_generic:
        movq filc_current_marking_state@GOTPCREL(%rip), %rax
        movl (%rax), %edx
        movq %rdx, 128(%rdi)
        movq $0, 384(%rdi)
        movl $8, %edx
        xorl %eax, %eax
        ret
        .globl pizlonated_c_is_marking
        .type pizlonated_c_is_marking, @function
pizlonated_c_is_marking:
        leaq .Lis_marking_object+16(%rip), %rax
        movq %rax, %rdx
        ret
        .size pizlonated_c_is_marking, .-pizlonated_c_is_marking
        .section .data.rel.ro,"aw",@progbits
        .p2align 4
.Lis_marking_object:
        .quad .Lis_marking_object+16
        .quad (.Lis_marking_object+16)+36873221949095936
        .quad .Lis_marking
        .quad .Lis_marking_generic
        .quad 2
        .section .note.GNU-stack,"",@progbits
