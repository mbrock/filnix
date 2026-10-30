// trap-reason
/* immintrin.h's bodiless intrinsics: filcc runs _mm_pause and
   _mm_sfence, and compiles _mm_lfence and _mm_mfence to a run-time
   error, reached only when they run. */
#include <immintrin.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/wait.h>
static void run(int i) {
    switch (i) {
    case 0: _mm_pause(); _mm_sfence(); printf("ran\n"); break;
    case 1: _mm_lfence(); printf("after lfence\n"); break;
    case 2: _mm_mfence(); printf("after mfence\n"); break;
    }
    fflush(stdout);
}
int main(void) {
    for (int i = 0; i <= 2; i++) {
        printf("case %d\n", i); fflush(stdout);
        pid_t p = fork();
        if (p == 0) { run(i); _exit(0); }
        int st; waitpid(p, &st, 0);
        printf("signaled %d\n", WIFSIGNALED(st));
    }
    return 0;
}
