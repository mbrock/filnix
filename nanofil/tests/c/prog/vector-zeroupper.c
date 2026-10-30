// trap-reason
/* filcc compiles _mm256_zeroupper and _mm256_zeroall to its run-time
   "Unhandled intrinsic" error, which nanofil raises too, after the
   code before them has run. */
#include <immintrin.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/wait.h>

__attribute__((target("avx"))) static void upper(void) { _mm256_zeroupper(); }
__attribute__((target("avx"))) static void all(void) { _mm256_zeroall(); }

int main(void) {
    for (int i = 0; i < 2; i++) {
        pid_t p = fork();
        if (p == 0) {
            printf("case %d\n", i); fflush(stdout);
            if (i == 0) upper(); else all();
            printf("ran\n"); fflush(stdout);
            _exit(0);
        }
        int st; waitpid(p, &st, 0);
        printf("case %d: %s\n", i, WIFEXITED(st) ? "ran" : "trapped");
        fflush(stdout);
    }
    return 0;
}
