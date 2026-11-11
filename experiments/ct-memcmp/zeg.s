# zeg_request(op, ptr, size, flags): a zegarmistrz client request, or 0
# when the process is not running under zegarmistrz. This is the body of
# zegarmistrz_client_request in zegarmistrz.h, as unchecked assembly:
# the pinned Fil-C runtime does not yet have the natives that header
# declares under __FILC__, so harness.c reaches the magic address
# through zunsafe_fast_call instead. Assembled by plain `as`.

.text
.globl zeg_request
.type zeg_request, @function
zeg_request:
    pushq %rbx
    movq %rdx, %r8              # cpuid writes %rdx and %rcx
    movq %rcx, %r9
    movl $1, %eax
    xorl %ecx, %ecx
    cpuid
    movl %ecx, %r10d            # bit 31: hypervisor present
    movl $0x40000000, %eax
    xorl %ecx, %ecx
    cpuid
    xorl %eax, %eax
    testl %r10d, %r10d
    jns .Lzeg_out
    cmpl $0x6167655A, %ebx      # "Zega"
    jne .Lzeg_out
    cmpl $0x73696D72, %ecx      # "rmis"
    jne .Lzeg_out
    cmpl $0x007A7274, %edx      # "trz\0"
    jne .Lzeg_out
    movq %r8, %rdx
    movq %r9, %rcx
    movabsq $0x1410141014101410, %rax
    call *%rax
.Lzeg_out:
    popq %rbx
    ret
.size zeg_request, .-zeg_request
.section .note.GNU-stack,"",@progbits
