# CRYPTO_memcmp from OpenSSL 3.6 crypto/x86_64cpuid.pl, as perlasm prints
# it for ELF ($arg1 = %rdi, $arg2 = %rsi, $arg3 = %rdx), renamed
# ct_memcmp, and followed by an early-exit comparison as the control.
#
# The only change to the instructions is the SaRCAsm signature on each
# label ("#!"), the same annotation ports/patch/openssl-sarcasm-3.6.5.patch
# adds. Plain `as` reads "#!" as a comment, so one file serves the
# unchecked build (clang -yolo-assembler) and the SaRCAsm build.
#
# Each instruction is numbered; memcmp.ir cites these numbers.

.text
.globl ct_memcmp
.type ct_memcmp, @function
.align 16
ct_memcmp: #! int(ptr,ptr,size_t)
    xor %rax, %rax          #  1  rax = 0
    xor %r10, %r10          #  2  r10 = 0
    cmp $0, %rdx            #  3  flags of len - 0
    je .Lno_data            #  4  len == 0: return 0
    cmp $16, %rdx           #  5  flags of len - 16
    jne .Loop_cmp           #  6  len != 16: byte loop
    mov (%rdi), %r10        #  7  r10 = a[0..8)
    mov 8(%rdi), %r11       #  8  r11 = a[8..16)
    mov $1, %rdx            #  9  rdx = 1 (the length register, reused)
    xor (%rsi), %r10        # 10  r10 ^= b[0..8)
    xor 8(%rsi), %r11       # 11  r11 ^= b[8..16)
    or %r11, %r10           # 12  r10 |= r11, sets ZF
    cmovnz %rdx, %rax       # 13  rax = ZF ? rax : rdx
    ret                     # 14

.align 16
.Loop_cmp:
    mov (%rdi), %r10b       # 15  low byte of r10 = *a
    lea 1(%rdi), %rdi       # 16  a++
    xor (%rsi), %r10b       # 17  low byte of r10 ^= *b
    lea 1(%rsi), %rsi       # 18  b++
    or %r10b, %al           # 19  low byte of rax |= low byte of r10
    dec %rdx                # 20  len--, sets ZF
    jnz .Loop_cmp           # 21
    neg %rax                # 22  rax = -rax
    shr $63, %rax           # 23  rax = rax != 0
.Lno_data:
    ret                     # 24
.size ct_memcmp, .-ct_memcmp

# The control: the same contract, but it leaves at the first difference.
.globl leaky_memcmp
.type leaky_memcmp, @function
.align 16
leaky_memcmp: #! int(ptr,ptr,size_t)
    xor %rax, %rax          #  1  rax = 0
    cmp $0, %rdx            #  2
    je .Lleaky_done         #  3  len == 0: return 0
.Lleaky_loop:
    mov (%rdi), %r10b       #  4  low byte of r10 = *a
    cmp (%rsi), %r10b       #  5  flags of *a - *b
    jne .Lleaky_diff        #  6  the secret-dependent branch
    lea 1(%rdi), %rdi       #  7  a++
    lea 1(%rsi), %rsi       #  8  b++
    dec %rdx                #  9  len--, sets ZF
    jnz .Lleaky_loop        # 10
.Lleaky_done:
    ret                     # 11
.Lleaky_diff:
    mov $1, %rax            # 12
    ret                     # 13
.size leaky_memcmp, .-leaky_memcmp
.section .note.GNU-stack,"",@progbits
