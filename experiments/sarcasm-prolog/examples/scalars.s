.text
.globl scalar_mix
.type scalar_mix, @function
scalar_mix: #! unsigned long(ptr, unsigned long)
    movq %rsi, %rax
    addq $-1, %rax
    movl %eax, %eax
    shlq $65, %rax
    xorq $0x1234, %rax
    ret
.globl changed_index
.type changed_index, @function
changed_index: #! unsigned long(ptr, unsigned long)
    movzbl (%rdi,%rsi,1), %eax
    addq $1, %rsi
    movzbl (%rdi,%rsi,1), %ecx
    addq %rcx, %rax
    ret
.section .note.GNU-stack,"",@progbits
