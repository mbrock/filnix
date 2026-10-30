// trap-reason
// vectors
/* A vector load or store is checked as one access of the vector's full
   width before any byte moves, with filcc's alignment capped at 8: the
   same reason as filcc, and nothing written before a trap. Each case
   runs in its own child. Offsets are run-time values so that clang -O1
   does not fold them into the base, which changes filcc's reason. */
#include <emmintrin.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/mman.h>
#include <sys/wait.h>

static volatile int off17 = 17, offm1 = -1, off4 = 4, off8 = 8, off4088 = 4088, off4081 = 4081, off32 = 32;
static const char ro[32] = "read-only";
static int x = 1, y[4] = {2, 3, 4, 5};
static char *shared;
/* through a volatile pointer: clang -O1 folds a direct free followed by
   an access into "cannot access pointer to free object", scalars too */
static void (*volatile release)(void *) = free;

static void run(int i) {
    char *b = malloc(32);
    memset(b, 7, 32);
    __m128i z = _mm_set1_epi8(1);
    switch (i) {
    case 0: z = _mm_loadu_si128((const __m128i *)(b + off17)); break;
    case 1: _mm_storeu_si128((__m128i *)(b + off17), z); break;
    case 2: z = _mm_loadu_si128((const __m128i *)(b + offm1)); break;
    case 3: _mm_storeu_si128((__m128i *)(b + offm1), z); break;
    case 4: _mm_storeu_si128((__m128i *)(ro + off8 - 8), z); break;
    case 5: z = _mm_load_si128((const __m128i *)(b + off4)); break;
    case 6: _mm_store_si128((__m128i *)(b + off4), z); break;
    case 7: release(b); z = _mm_loadu_si128((const __m128i *)b); break;
    case 8: release(b); _mm_storeu_si128((__m128i *)b, z); break;
    case 9: z = _mm_loadu_si128((const __m128i *)(long)(off8 - 8)); break;
    case 10: _mm_storeu_si128((__m128i *)(long)(off8 - 8), z); break;
    case 11: { /* a vector store over a pointer slot keeps its capability:
                  the new address of y is used with x's bounds */
        int *slots[2] = {&x, &x};
        long bits[2] = {(long)&y[2], (long)&y[2]};
        _mm_storeu_si128((__m128i *)slots, _mm_loadu_si128((const __m128i *)bits));
        printf("%d\n", *slots[0]); break; }
    case 12: { /* the same bits and capability: unchanged */
        int *slots[2] = {&x, &x};
        _mm_storeu_si128((__m128i *)slots, _mm_loadu_si128((const __m128i *)slots));
        printf("%d\n", *slots[1]); break; }
    case 13: /* half in bounds: the trap comes before any byte is written */
        _mm_storeu_si128((__m128i *)(shared + off4088), z); break;
    case 14: z = _mm_loadu_si128((const __m128i *)(b + off32)); break;   /* exactly at the end */
    case 15: _mm_storeu_si128((__m128i *)(b + off32), z); break;
    case 16: z = _mm_loadu_si128((const __m128i *)(ro + off8 - 8)); break; /* a read-only load runs */
    case 17: /* one byte short of the end of a shared page: nothing written */
        _mm_storeu_si128((__m128i *)(shared + off4081), z); break;
    }
    printf("%d\n", _mm_cvtsi128_si32(z));
    fflush(stdout);
}

int main(void) {
    shared = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    for (int i = 0; i <= 17; i++) {
        printf("case %d\n", i); fflush(stdout);
        pid_t p = fork();
        if (p == 0) { run(i); _exit(0); }
        int st; waitpid(p, &st, 0);
        printf("signaled %d\n", WIFSIGNALED(st));
    }
    int sum = 0;
    for (int k = 4080; k < 4096; k++) sum += shared[k];
    printf("shared %d %d %d\n", shared[4087], shared[4088], sum);
    return 0;
}
