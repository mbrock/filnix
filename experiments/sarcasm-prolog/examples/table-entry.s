# A small slice of zstd's X2 lookup: sequence, bit count, output length.
.text
.globl table_entry
.type table_entry, @function
table_entry: #! unsigned long(ptr, unsigned long)
    movzwl 0(%rdi,%rsi,4), %eax; movzbl 2(%rdi,%rsi,4), %ecx
    movzbl (1+2)(%rdi,%rsi,4), %edx
    shlq $16, %rcx
    shlq $24, %rdx
    orq %rcx, %rax
    orq %rdx, %rax
    ret
.size table_entry, .-table_entry
.section .note.GNU-stack,"",@progbits
