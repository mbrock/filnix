.text
.globl unaligned_load
.type unaligned_load, @function
unaligned_load: #! unsigned long(ptr)
    movq (%rdi), %rax; ret
.globl unaligned_store
.type unaligned_store, @function
unaligned_store: #! void(ptr, unsigned)
    movw %si, (%rdi); ret
.globl pointer_load
.type pointer_load, @function
pointer_load: #! ptr(ptr)
    movq (%rdi), %rax #! load ptr
    ret
.section .note.GNU-stack,"",@progbits
