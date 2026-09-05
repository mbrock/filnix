.text
.globl branch_read
.type branch_read, @function
branch_read: #! unsigned long(ptr, unsigned long)
    testq $1,%rsi
    je .Lread_left
    movq 8(%rdi),%r8 #! ptr
    jmp .Lread_join
.Lread_left:
    movq (%rdi),%r8 #! ptr
.Lread_join:
    movzbl (%r8),%eax
    ret

.globl branch_store
.type branch_store, @function
branch_store: #! unsigned long(ptr, unsigned long)
    testq $1,%rsi
    je .Lstore_left
    movq 8(%rdi),%r8 #! ptr
    jmp .Lstore_join
.Lstore_left:
    movq (%rdi),%r8 #! ptr
.Lstore_join:
    movq %rsi,(%r8)
    movq (%r8),%rax
    ret

# Only one predecessor reads a before the join. That successful access
# cannot authorize a read through b's different capability at the join.
.globl branch_checked
.type branch_checked, @function
branch_checked: #! unsigned long(ptr, unsigned long)
    movq (%rdi),%r8 #! ptr
    testq $1,%rsi
    je .Lchecked_join
    movzbl (%r8),%eax
    movq 8(%rdi),%r8 #! ptr
.Lchecked_join:
    movzbl (%r8),%eax
    ret

.globl branch_swap
.type branch_swap, @function
branch_swap: #! unsigned long(ptr, unsigned long)
    movq (%rdi),%r8 #! ptr
    movq 8(%rdi),%r9 #! ptr
    testq $1,%rsi
    je .Lswap_join
    movq %r8,%r10
    movq %r9,%r8
    movq %r10,%r9
.Lswap_join:
    movq (%r8),%rax
    movq %rax,(%r9)
    ret
.section .note.GNU-stack,"",@progbits
