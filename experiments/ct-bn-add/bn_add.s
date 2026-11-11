# bn_add_words and bn_sub_words from OpenSSL 3.6 crypto/bn/asm/x86_64-gcc.c,
# and a control that branches on the carry.
#
# OpenSSL has the two loops as inline assembly in C functions whose
# count is an int. Lines 5 to 13 of each function below are that
# assembly with the registers a compiler could give it (%0 = %rax,
# %1 = %rcx, %2 = %r8, %3 = %rdi, %4 = %rsi, %5 = %rdx) and its local
# label 1 named. Lines 1 to 4 and 14 stand for the C around it
# ("if (n <= 0) return 0", "i = 0", "return ret & 1"), written with
# 64-bit registers and a size_t count, since the lifter refuses 32-bit
# registers.
#
# Each label has a SaRCAsm signature ("#!"), the annotation
# ports/patch/openssl-sarcasm-3.6.5.patch adds to OpenSSL's assembly
# files. Plain `as` reads "#!" as a comment, so one file serves the
# unchecked build (clang -yolo-assembler) and the SaRCAsm build.

.text
.globl bn_add_words
.type bn_add_words, @function
.align 16
bn_add_words: #! size_t(ptr,ptr,ptr,size_t)
    xor %rax, %rax          #  1  the result when n == 0
    cmp $0, %rcx            #  2
    je .Ladd_done           #  3
    xor %r8, %r8            #  4  i = 0
    sub %rax, %rax          #  5  clear carry
    jmp .Ladd_loop          #  6
.p2align 4
.Ladd_loop:
    mov (%rsi,%r8,8), %rax  #  7  rax = a[i]
    adc (%rdx,%r8,8), %rax  #  8  rax += b[i] + CF, sets CF
    mov %rax, (%rdi,%r8,8)  #  9  r[i] = rax
    lea 1(%r8), %r8         # 10  i++, leaves CF
    dec %rcx                # 11  n--, sets ZF, leaves CF
    jnz .Ladd_loop          # 12
    sbb %rax, %rax          # 13  rax = -CF
    and $1, %rax            # 14  rax = CF
.Ladd_done:
    ret                     # 15
.size bn_add_words, .-bn_add_words

.globl bn_sub_words
.type bn_sub_words, @function
.align 16
bn_sub_words: #! size_t(ptr,ptr,ptr,size_t)
    xor %rax, %rax          #  1  the result when n == 0
    cmp $0, %rcx            #  2
    je .Lsub_done           #  3
    xor %r8, %r8            #  4  i = 0
    sub %rax, %rax          #  5  clear borrow
    jmp .Lsub_loop          #  6
.p2align 4
.Lsub_loop:
    mov (%rsi,%r8,8), %rax  #  7  rax = a[i]
    sbb (%rdx,%r8,8), %rax  #  8  rax -= b[i] + CF, sets CF
    mov %rax, (%rdi,%r8,8)  #  9  r[i] = rax
    lea 1(%r8), %r8         # 10  i++, leaves CF
    dec %rcx                # 11  n--, sets ZF, leaves CF
    jnz .Lsub_loop          # 12
    sbb %rax, %rax          # 13  rax = -CF
    and $1, %rax            # 14  rax = CF
.Lsub_done:
    ret                     # 15
.size bn_sub_words, .-bn_sub_words

# The control: the same sums, with the carry kept in %rax and set by
# two branches on CF.
.globl leaky_add_words
.type leaky_add_words, @function
.align 16
leaky_add_words: #! size_t(ptr,ptr,ptr,size_t)
    xor %rax, %rax          #  1  carry = 0, the result when n == 0
    cmp $0, %rcx            #  2
    je .Lleaky_done         #  3
    xor %r8, %r8            #  4  i = 0
.Lleaky_loop:
    mov (%rsi,%r8,8), %r9   #  5  r9 = a[i]
    add %rax, %r9           #  6  r9 += carry, sets CF
    mov $0, %rax            #  7  carry = 0, leaves CF
    jnc .Lleaky_second      #  8  a secret-dependent branch
    mov $1, %rax            #  9  carry = 1
.Lleaky_second:
    add (%rdx,%r8,8), %r9   # 10  r9 += b[i], sets CF
    jnc .Lleaky_store       # 11  a secret-dependent branch
    mov $1, %rax            # 12  carry = 1
.Lleaky_store:
    mov %r9, (%rdi,%r8,8)   # 13  r[i] = r9
    lea 1(%r8), %r8         # 14  i++
    dec %rcx                # 15  n--, sets ZF
    jnz .Lleaky_loop        # 16
.Lleaky_done:
    ret                     # 17
.size leaky_add_words, .-leaky_add_words
.section .note.GNU-stack,"",@progbits
