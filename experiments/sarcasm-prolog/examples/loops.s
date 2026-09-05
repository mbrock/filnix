# Sum node values for exactly the requested number of steps.
# Each node is {next pointer, uint64_t value}; the chain may contain cycles.
.text
.globl loop_walk
.type loop_walk, @function
loop_walk: #! unsigned long(ptr, unsigned long)
    movq %rdi,%r8
    movq $0,%rax
    movq $0,%rcx
.Lwalk:
    cmpq %rsi,%rcx
    je .Lwalk_done
    movq 8(%r8),%rdx
    addq %rdx,%rax
    movq (%r8),%r8 #! ptr
    addq $1,%rcx
    jmp .Lwalk
.Lwalk_done:
    ret
.size loop_walk, .-loop_walk
.section .note.GNU-stack,"",@progbits
