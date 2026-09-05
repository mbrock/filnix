.text
.globl checks_cover
.type checks_cover, @function
checks_cover: #! unsigned long(ptr, unsigned long)
    movq (%rdi),%rax
    addq %rsi,%rax
    movzbl 3(%rdi),%ecx
    addq %rcx,%rax
    ret

.globl checks_diamond
.type checks_diamond, @function
checks_diamond: #! unsigned long(ptr, unsigned long)
    movq (%rdi),%rax
    testq $1,%rsi
    je .Lchecks_left
    addq %rsi,%rax
    jmp .Lchecks_join
.Lchecks_left:
    xorq %rsi,%rax
.Lchecks_join:
    movzbl 3(%rdi),%ecx
    addq %rcx,%rax
    ret

.globl checks_one_path
.type checks_one_path, @function
checks_one_path: #! unsigned long(ptr, unsigned long)
    testq $1,%rsi
    je .Lchecks_unprotected
    movq (%rdi),%rax
    jmp .Lchecks_one_join
.Lchecks_unprotected:
    movq $0,%rax
.Lchecks_one_join:
    movzbl 3(%rdi),%ecx
    addq %rcx,%rax
    ret

.globl checks_store
.type checks_store, @function
checks_store: #! unsigned long(ptr, unsigned long)
    movq (%rdi),%rax
    movl %esi,1(%rdi)
    movzbl 3(%rdi),%ecx
    addq %rcx,%rax
    ret

.globl checks_index
.type checks_index, @function
checks_index: #! unsigned long(ptr, unsigned long)
    movq (%rdi,%rsi,1),%rax
    addq $1,%rsi
    movzbl (%rdi,%rsi,1),%ecx
    addq %rcx,%rax
    ret

.globl checks_cycle
.type checks_cycle, @function
checks_cycle: #! unsigned long(ptr, unsigned long)
    andq $7,%rsi
    movq (%rdi),%rax
    movq $0,%rcx
.Lchecks_cycle:
    cmpq %rsi,%rcx
    je .Lchecks_cycle_done
    movzbl 3(%rdi),%edx
    addq %rdx,%rax
    addq $1,%rcx
    jmp .Lchecks_cycle
.Lchecks_cycle_done:
    ret

.globl checks_local_loop
.type checks_local_loop, @function
checks_local_loop: #! unsigned long(ptr, unsigned long)
    andq $7,%rsi
    movq $0,%rax
    movq $0,%rcx
.Lchecks_local:
    cmpq %rsi,%rcx
    je .Lchecks_local_done
    movq (%rdi,%rcx,8),%r9
    addq %r9,%rax
    movzbl 3(%rdi,%rcx,8),%edx
    addq %rdx,%rax
    addq $1,%rcx
    jmp .Lchecks_local
.Lchecks_local_done:
    ret
.section .note.GNU-stack,"",@progbits
