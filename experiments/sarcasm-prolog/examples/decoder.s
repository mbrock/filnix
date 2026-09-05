# A tiny table decoder. State is {table pointer, input pointer, output
# pointer, consumed count}. Each valid input byte 0..63 selects one
# little-endian four-byte output word. The integer argument bounds the
# number of input bytes. Return 0 on success, 1 at the first invalid byte.
# Final input/output pointers and consumed count are written back to state.
.text
.globl tiny_decode
.type tiny_decode, @function
tiny_decode: #! unsigned long(ptr, unsigned long)
    movq (%rdi),%r8 #! ptr
    movq 8(%rdi),%r9 #! ptr
    movq 16(%rdi),%r10 #! ptr
    movq $0,%rcx
.Ldecode_loop:
    cmpq %rsi,%rcx
    jae .Ldecode_done
    movzbl (%r9),%edx
    cmpl $63,%edx
    ja .Ldecode_bad
    movzwl (%r8,%rdx,4),%eax
    movzwl 2(%r8,%rdx,4),%r11d
    shll $16,%r11d
    orl %r11d,%eax
    movl %eax,(%r10)
    leaq 1(%r9),%r9
    leaq 4(%r10),%r10
    addq $1,%rcx
    jmp .Ldecode_loop
.Ldecode_done:
    movq $0,%rax
    jmp .Ldecode_save
.Ldecode_bad:
    movq $1,%rax
.Ldecode_save:
    movq %r9,8(%rdi) #! ptr
    movq %r10,16(%rdi) #! ptr
    movq %rcx,24(%rdi)
    ret
.section .note.GNU-stack,"",@progbits
