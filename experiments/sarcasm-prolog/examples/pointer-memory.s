.text
.globl slot_read
.type slot_read, @function
slot_read: #! unsigned long(ptr, unsigned long)
    movq (%rdi), %r8 #! ptr
    leaq (%r8,%rsi,1), %r8
    movzbl (%r8), %eax
    ret
.size slot_read, .-slot_read

.globl slot_copy
.type slot_copy, @function
slot_copy: #! unsigned long(ptr)
    movq (%rdi), %r8 #! ptr
    movq %r8, 8(%rdi) #! ptr
    movq 8(%rdi), %r9 #! ptr
    movzbl (%r9), %eax
    ret
.size slot_copy, .-slot_copy

.globl slot_self
.type slot_self, @function
slot_self: #! unsigned long(ptr)
    movq %rdi, (%rdi) #! ptr
    movq (%rdi), %r8 #! ptr
    movq (%r8), %r9 #! ptr
    movq (%r9), %rax
    ret
.size slot_self, .-slot_self

.globl slot_write
.type slot_write, @function
slot_write: #! unsigned long(ptr, unsigned long)
    movq %rdi, (%rdi,%rsi,1) #! ptr
    movq $0, %rax
    ret
.size slot_write, .-slot_write
.section .note.GNU-stack,"",@progbits
