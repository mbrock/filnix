/* What saving and restoring the flags costs a carry loop.

   `plain` is bn_add_words's loop from bn_add.s. `flags4` is the same
   loop with four `pushf; pop` ... `push; popf` pairs in each iteration,
   one before each memory access and one more, which is where SaRCAsm
   puts them around its checks when the carry is live (see README.md).
   The checks themselves are left out, so the difference is the cost of
   the flag saves alone. `lahf4` saves the flags in the same four places
   with `lahf` and `seto`, and restores them with `add` and `sahf`.

     gcc -O2 -o pushf pushf.c && ./pushf

   This is plain C for the host, not a Fil-C program. */
#include <stdint.h>
#include <stdio.h>
#include <time.h>

uint64_t plain(uint64_t *r, const uint64_t *a, const uint64_t *b, uint64_t n);
uint64_t flags4(uint64_t *r, const uint64_t *a, const uint64_t *b, uint64_t n);
uint64_t lahf4(uint64_t *r, const uint64_t *a, const uint64_t *b, uint64_t n);

#define SAVE "    pushf\n    pop %r9\n    push %r9\n    popf\n"
/* %ah holds SF, ZF, AF, PF and CF; adding 0x7f to the byte seto wrote
   overflows, and so sets OF again, exactly when OF was set. */
#define LAHF \
    "    mov %rax, %r9\n    lahf\n    seto %r10b\n" \
    "    add $0x7f, %r10b\n    sahf\n    mov %r9, %rax\n"

__asm__(
    ".text\n"
    ".globl plain\n"
    "plain:\n"
    "    xor %r8, %r8\n"
    "    sub %rax, %rax\n"
    "1:\n"
    "    mov (%rsi,%r8,8), %rax\n"
    "    adc (%rdx,%r8,8), %rax\n"
    "    mov %rax, (%rdi,%r8,8)\n"
    "    lea 1(%r8), %r8\n"
    "    dec %rcx\n"
    "    jnz 1b\n"
    "    sbb %rax, %rax\n"
    "    and $1, %rax\n"
    "    ret\n"
    ".globl flags4\n"
    "flags4:\n"
    "    xor %r8, %r8\n"
    "    sub %rax, %rax\n"
    "1:\n"
    SAVE
    "    mov (%rsi,%r8,8), %rax\n"
    SAVE
    "    adc (%rdx,%r8,8), %rax\n"
    SAVE
    "    mov %rax, (%rdi,%r8,8)\n"
    SAVE
    "    lea 1(%r8), %r8\n"
    "    dec %rcx\n"
    "    jnz 1b\n"
    "    sbb %rax, %rax\n"
    "    and $1, %rax\n"
    "    ret\n"
    ".globl lahf4\n"
    "lahf4:\n"
    "    xor %r8, %r8\n"
    "    sub %rax, %rax\n"
    "1:\n"
    LAHF
    "    mov (%rsi,%r8,8), %rax\n"
    LAHF
    "    adc (%rdx,%r8,8), %rax\n"
    LAHF
    "    mov %rax, (%rdi,%r8,8)\n"
    LAHF
    "    lea 1(%r8), %r8\n"
    "    dec %rcx\n"
    "    jnz 1b\n"
    "    sbb %rax, %rax\n"
    "    and $1, %rax\n"
    "    ret\n"
    ".section .note.GNU-stack,\"\",@progbits\n"
    ".text\n");

typedef uint64_t kernel(uint64_t *, const uint64_t *, const uint64_t *, uint64_t);

static double now(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec * 1e9 + t.tv_nsec;
}

static uint64_t a[512], b[512], r[512];

static double ns_per_word(kernel *k)
{
    enum { size = 512, rounds = 20000 };
    uint64_t sum = 0;
    double t = now();
    for (int i = 0; i < rounds; i++)
        sum += k(r, a, b, size);
    t = now() - t;
    /* Every variant must compute the sum the C below computes. */
    uint64_t carry = 0;
    for (int i = 0; i < size; i++) {
        unsigned __int128 x = (unsigned __int128)a[i] + b[i] + carry;
        if (r[i] != (uint64_t)x)
            return -1;
        carry = x >> 64;
    }
    if (sum != carry * rounds)
        return -1;
    return t / ((double)rounds * size);
}

int main(void)
{
    for (int i = 0; i < 512; i++) {
        a[i] = ~0ull - i;
        b[i] = i * 3 + 1;
    }
    for (int rep = 0; rep < 3; rep++)
        printf("ns/word: plain %.2f, four pushf and popf pairs %.2f, four lahf and sahf pairs %.2f\n",
               ns_per_word(plain), ns_per_word(flags4), ns_per_word(lahf4));
    return 0;
}
