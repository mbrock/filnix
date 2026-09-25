#include "huf_decompress.c"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static unsigned rng = 42;
static unsigned next(void) {
  rng = rng * 1664525u + 1013904223u;
  return rng;
}
int main(int argc, char **argv) {
  unsigned char *input = malloc(1025), *outa = malloc(2049),
                *outc = malloc(2049);
  HUF_DEltX1 *dt1 = malloc(2048 * sizeof(*dt1));
  HUF_DEltX2 *dt2 = malloc(2048 * sizeof(*dt2));
  for (int trial = 0; trial < 100; ++trial) {
    for (int k = 0; k < 1025; ++k)
      input[k] = next() >> 24;
    for (int k = 0; k < 2048; ++k) {
      dt1[k].nbBits = 1 + next() % 11;
      dt1[k].byte = next() >> 24;
      dt2[k].nbBits = 1 + next() % 11;
      dt2[k].length = 1 + next() % 2;
      dt2[k].sequence = next() >> 16;
    }
    for (int mode = argc > 2 ? atoi(argv[2]) : 1; mode <= 2; ++mode) {
      HUF_DecompressFastArgs a = {0}, c;
      memset(outa, 0xcd, 2049);
      memset(outc, 0xcd, 2049);
      for (int k = 0; k < 4; ++k) {
        a.ip[k] = input + 1 + 256 * (k + 1) - 8;
        a.op[k] = outa + 1 + 512 * k;
        a.bits[k] = HUF_initFastDStream(a.ip[k]);
      }
      a.dt = mode == 1 ? (void *)dt1 : (void *)dt2;
      a.ilowest = input + 1;
      a.oend = outa + 2049;
      c = a;
      c.oend = outc + 2049;
      for (int k = 0; k < 4; ++k)
        c.op[k] = outc + 1 + 512 * k;
      if (argc > 1) {
        if (!strcmp(argv[1], "null")) {
          volatile uintptr_t lost = (uintptr_t)a.dt;
          a.dt = (void *)lost;
        } else if (!strcmp(argv[1], "oob"))
          a.dt = malloc(1);
        else if (!strcmp(argv[1], "store"))
          a.op[0] = malloc(1);
      }
      if (mode == 1) {
        HUF_decompress4X1_usingDTable_internal_fast_c_loop(&c);
        HUF_decompress4X1_usingDTable_internal_fast_asm_loop(&a);
      } else {
        HUF_decompress4X2_usingDTable_internal_fast_c_loop(&c);
        HUF_decompress4X2_usingDTable_internal_fast_asm_loop(&a);
      }
      if (memcmp(outa, outc, 2049)) {
        fprintf(stderr, "output mismatch trial %d mode %d\n", trial, mode);
        return 1;
      }
      for (int k = 0; k < 4; ++k) {
        if (a.ip[k] != c.ip[k] || a.bits[k] != c.bits[k] ||
            a.op[k] - outa != c.op[k] - outc) {
          fprintf(stderr, "state mismatch trial %d mode %d stream %d\n", trial,
                  mode, k);
          return 1;
        }
        /* Dereference the returned pointers to exercise their capabilities. */
        if (a.op[k] > outa + 1 + 512 * k)
          assert(*(volatile BYTE *)(a.op[k] - 1) == c.op[k][-1]);
      }
    }
  }
  puts("200 X1/X2 loop comparisons passed (unaligned input/output)");
  return 0;
}
