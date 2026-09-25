#define ZSTD_STATIC_LINKING_ONLY
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <zstd.h>
static double now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return t.tv_sec + t.tv_nsec * 1e-9;
}
int main(int argc, char **argv) {
  int first = 0, last = 1, trials = 5, iterations = 100;
  if (argc > 1) {
    if (!strcmp(argv[1], "asm"))
      first = last = 0;
    else if (!strcmp(argv[1], "c"))
      first = last = 1;
    else {
      fprintf(stderr, "usage: %s [asm|c [iterations]]\n", argv[0]);
      return 2;
    }
    trials = 1;
  }
  if (argc > 2) {
    iterations = atoi(argv[2]);
    if (iterations < 1)
      return 2;
  }
  size_t n = 1 << 20;
  char *src = malloc(n), *out = malloc(n), *buf = malloc(ZSTD_compressBound(n));
  unsigned r = 42;
  for (size_t i = 0; i < n; i++) {
    r = r * 1664525 + 1013904223;
    src[i] = r >> 28;
  }
  size_t c = ZSTD_compress(buf, ZSTD_compressBound(n), src, n, 3);
  assert(!ZSTD_isError(c));
  ZSTD_DCtx *d = ZSTD_createDCtx();
  for (int trial = 0; trial < trials; trial++)
    for (int off = first; off <= last; off++) {
      assert(!ZSTD_isError(
          ZSTD_DCtx_setParameter(d, ZSTD_d_disableHuffmanAssembly, off)));
      double t = now();
      for (int i = 0; i < iterations; i++)
        assert(ZSTD_decompressDCtx(d, out, n, buf, c) == n);
      t = now() - t;
      assert(!memcmp(src, out, n));
      printf("%s %.6f seconds (%d MiB)\n", off ? "C" : "SaRCAsm", t,
             iterations);
      fflush(stdout);
    }
}
