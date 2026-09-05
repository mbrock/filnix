.text
.globl asm_load
.type asm_load, @function
asm_load: #! unsigned(ptr)
    movl (%rdi), %eax
    ret
.size asm_load, .-asm_load

.globl asm_identity
.type asm_identity, @function
asm_identity: #! ptr(ptr)
    movq %rdi, %rax
    ret
.size asm_identity, .-asm_identity
.section .note.GNU-stack,"",@progbits
