// trap-reason
// vectors
/* SSE3's _mm_lddqu_si128 (gtk4's roaring.c) loads 16 bytes at any
   alignment, checked as one 16-byte access with alignment 1, like
   _mm_loadu_si128. Each case runs in its own child; offsets are
   run-time values so clang -O1 does not fold them. */
#include <pmmintrin.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>

static volatile int off1 = 1, off17 = 17, offm1 = -1;
static void (*volatile release)(void *) = free;

static void show(__m128i z) {
    unsigned char o[16];
    _mm_storeu_si128((__m128i *)o, z);
    for (int k = 0; k < 16; k++) printf("%02x", o[k]);
    printf("\n");
}

static void run(int i) {
    unsigned char *b = malloc(32);
    for (int k = 0; k < 32; k++) b[k] = (unsigned char)(k * 13 + 5);
    switch (i) {
    case 0: show(_mm_lddqu_si128((const __m128i *)(b + off1))); break;
    case 1: show(_mm_lddqu_si128((const __m128i *)(b + off17 - 1))); break;
    case 2: show(_mm_lddqu_si128((const __m128i *)(b + off17))); break;
    case 3: show(_mm_lddqu_si128((const __m128i *)(b + offm1))); break;
    case 4: release(b); show(_mm_lddqu_si128((const __m128i *)b)); break;
    }
    fflush(stdout);
}

int main(void) {
    for (int i = 0; i < 5; i++) {
        pid_t p = fork();
        if (p == 0) { run(i); _exit(0); }
        int st; waitpid(p, &st, 0);
        printf("case %d: %s\n", i, WIFEXITED(st) ? "ran" : "trapped");
        fflush(stdout);
    }
    return 0;
}
