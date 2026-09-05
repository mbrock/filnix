.text
.globl pointer_entry
.type pointer_entry, @function
pointer_entry: #! unsigned long(ptr, unsigned long)
    movq %rdi, %r8
    leaq 3(%r8,%rsi,4), %r9
    movq %r9, %r10
    movzwl (%r10), %eax
    movzbl 2(%r10), %edx
    movzbl 3(%r10), %ecx
    shlq $16, %rdx
    shlq $24, %rcx
    orq %rdx, %rax
    orq %rcx, %rax
    ret
.size pointer_entry, .-pointer_entry
.section .note.GNU-stack,"",@progbits
