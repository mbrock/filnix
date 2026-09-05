.text
.globl integer_update
.type integer_update, @function
integer_update: #! unsigned long(ptr, unsigned long)
    movl (%rdi), %eax
    addl %esi, %eax
    movl %eax, 1(%rdi)
    movq 1(%rdi), %r8
    movq $-1, 9(%rdi)
    xorq %rsi, %r8
    movq %r8, 2(%rdi)
    movq 2(%rdi), %rax
    ret
.size integer_update, .-integer_update

.globl integer_store
.type integer_store, @function
integer_store: #! unsigned long(ptr, unsigned long)
    movq $7, (%rdi,%rsi,8)
    movq $0, %rax
    ret
.size integer_store, .-integer_store
.section .note.GNU-stack,"",@progbits
