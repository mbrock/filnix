// trap-reason
/* A 32-byte AVX vector load or store is checked as one access of its
   full width before any byte moves, with filcc's alignment capped at 8:
   the same reason as filcc, and nothing written before a trap
   (vector-access.c covers 16 bytes). Each case runs in its own child.
   Offsets are run-time values so that clang -O1 does not fold them into
   the base. The cases call AVX code only where the CPU has AVX2. An
   aligned access at an address only 8-aligned is left out: filcc's
   VMOVDQA faults there (undefined behavior, not a Fil-C check). */
#include <immintrin.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/wait.h>

#define AVX2 __attribute__((target("avx2")))
static volatile int off33 = 33, offm1 = -1, off4 = 4, off8 = 8, off16 = 16, off4072 = 4072, off4065 = 4065, off64 = 64, off32 = 32;
static const char ro[64] = "read-only";
static int x = 1, y[8] = {2, 3, 4, 5, 6, 7, 8, 9};
static char *shared;
static void (*volatile release)(void *) = free;

AVX2 static void run(int i) {
    char *b = malloc(64);
    memset(b, 7, 64);
    __m256i z = _mm256_set1_epi8(1);
    switch (i) {
    case 0: z = _mm256_loadu_si256((const __m256i *)(b + off33)); break;
    case 1: _mm256_storeu_si256((__m256i *)(b + off33), z); break;
    case 2: z = _mm256_loadu_si256((const __m256i *)(b + offm1)); break;
    case 3: _mm256_storeu_si256((__m256i *)(b + offm1), z); break;
    case 4: _mm256_storeu_si256((__m256i *)(ro + off8 - 8), z); break;
    case 5: z = _mm256_load_si256((const __m256i *)(b + off4)); break;
    case 6: _mm256_store_si256((__m256i *)(b + off4), z); break;
    case 7: release(b); z = _mm256_loadu_si256((const __m256i *)b); break;
    case 8: release(b); _mm256_storeu_si256((__m256i *)b, z); break;
    case 9: z = _mm256_loadu_si256((const __m256i *)(long)(off8 - 8)); break;
    case 10: _mm256_storeu_si256((__m256i *)(long)(off8 - 8), z); break;
    case 11: { /* a vector store over pointer slots keeps their capabilities:
                  the new address of y is used with x's bounds */
        int *slots[4] = {&x, &x, &x, &x};
        long bits[4] = {(long)&y[2], (long)&y[2], (long)&y[2], (long)&y[2]};
        _mm256_storeu_si256((__m256i *)slots, _mm256_loadu_si256((const __m256i *)bits));
        printf("%d\n", *slots[3]); break; }
    case 12: { /* the same bits and capabilities: unchanged */
        int *slots[4] = {&x, &x, &y[1], &x};
        _mm256_storeu_si256((__m256i *)slots, _mm256_loadu_si256((const __m256i *)slots));
        printf("%d %d\n", *slots[1], *slots[2]); break; }
    case 13: /* half in bounds: the trap comes before any byte is written */
        _mm256_storeu_si256((__m256i *)(shared + off4072), z); break;
    case 14: z = _mm256_loadu_si256((const __m256i *)(b + off64)); break;   /* exactly at the end */
    case 15: _mm256_storeu_si256((__m256i *)(b + off64), z); break;
    case 16: z = _mm256_loadu_si256((const __m256i *)(ro + off8 - 8)); break; /* a read-only load runs */
    case 17: /* one byte short of the end of a shared page: nothing written */
        _mm256_storeu_si256((__m256i *)(shared + off4065), z); break;
    case 18: z = _mm256_loadu_si256((const __m256i *)(b + off32)); break;   /* the last 32 bytes */
    case 19: /* a 32-byte store straddling two adjacent ints: out of y's bounds */
        _mm256_storeu_si256((__m256i *)&y[1], z); break;
    case 20: { /* AVX's maskless 128-bit halves of the same store */
        __m256i v = _mm256_loadu_si256((const __m256i *)b);
        _mm256_storeu2_m128i((__m128i *)(b + off33), (__m128i *)b, v); break; }
    }
    printf("%d %d\n", _mm256_cvtsi256_si32(z), _mm256_extract_epi32(z, 7));
    fflush(stdout);
}

int main(void) {
    __builtin_cpu_init();
    if (!__builtin_cpu_supports("avx2")) { puts("skip: no avx2"); return 0; }
    shared = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    for (int i = 0; i <= 20; i++) {
        printf("case %d\n", i); fflush(stdout);
        pid_t p = fork();
        if (p == 0) { run(i); _exit(0); }
        int st; waitpid(p, &st, 0);
        printf("signaled %d\n", WIFSIGNALED(st));
    }
    int sum = 0;
    for (int k = 4064; k < 4096; k++) sum += shared[k];
    printf("shared %d %d %d\n", shared[4071], shared[4072], sum);
    return 0;
}
