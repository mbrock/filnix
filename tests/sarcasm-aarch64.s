.text
.p2align 2
.globl asm_load
.type asm_load, %function
asm_load: //! unsigned(ptr)
    ldr w0, [x0]
    ret
.size asm_load, .-asm_load

.globl asm_identity
.type asm_identity, %function
asm_identity: //! ptr(ptr)
    mov x1, x0
    mov x0, x1
    ret
.size asm_identity, .-asm_identity
.section .note.GNU-stack,"",@progbits
