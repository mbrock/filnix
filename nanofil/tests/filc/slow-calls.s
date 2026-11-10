# Queue SIGUSR1 with a real tgkill while the Fil-C mutator is entered.
# The runtime defers it until an exit-capable helper. No GC/runtime state
# is fabricated. Return 91 through the ordinary scalar fast channel.
        .text
.Lqueue_signal:
        movl $39, %eax
        syscall
        movq %rax, %r8
        movl $186, %eax
        syscall
        movq %rax, %rsi
        movq %r8, %rdi
        movl $10, %edx
        movl $234, %eax
        syscall
        movl $91, %edx
        xorl %eax, %eax
        ret
.Lqueue_generic:
        pushq %rbx
        movq %rdi, %rbx
        call .Lqueue_signal
        movq %rdx, 128(%rbx)
        movq $0, 384(%rbx)
        movl $8, %edx
        xorl %eax, %eax
        popq %rbx
        ret
        .globl pizlonated_queue_signal
        .type pizlonated_queue_signal, @function
pizlonated_queue_signal:
        leaq .Lqueue_object+16(%rip), %rax
        movq %rax, %rdx
        ret
        .size pizlonated_queue_signal, .-pizlonated_queue_signal
        .section .data.rel.ro,"aw",@progbits
        .p2align 4
.Lqueue_object:
        .quad .Lqueue_object+16
        .quad (.Lqueue_object+16)+36873221949095936
        .quad .Lqueue_signal
        .quad .Lqueue_generic
        .quad 2
        .section .note.GNU-stack,"",@progbits
