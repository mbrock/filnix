#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint64_t covering(const unsigned char *, uint64_t);
uint64_t diamond(const unsigned char *, uint64_t);
uint64_t one_path(const unsigned char *, uint64_t);
uint64_t checked(const unsigned char *, uint64_t);
uint64_t changed(unsigned char *, uint64_t);
uint64_t retained_loads(const unsigned char *, uint64_t);
uint64_t call_barrier(const unsigned char *, uint64_t);
static int free_on_call;
static unsigned effects;
/* Compiled in a separate translation unit from the probe. */
void check_probe_effect(void *p) {
  effects++;
  if (free_on_call) free(p);
}
static uint64_t load8(const unsigned char *p) {
  uint64_t result = 0;
  for (unsigned i = 0; i < 8; i++) result |= (uint64_t)p[i] << (8 * i);
  return result;
}
int main(int argc, char **argv) {
  if (argc > 1) {
    assert(!strcmp(argv[1], "free"));
    free_on_call = 1;
    return call_barrier(calloc(1, 16), 0);
  }
  for (unsigned trial = 0; trial < 256; trial++) {
    unsigned char bytes[32];
    for (unsigned i = 0; i < sizeof bytes; i++) bytes[i] = trial + i * 179;
    uint64_t n = UINT64_C(0xfedcba9876543200) | trial, first = load8(bytes);
    assert(covering(bytes, n) == first + n + bytes[3]);
    assert(diamond(bytes, n) == ((n & 1) ? first + n : first ^ n) + bytes[3]);
    assert(one_path(bytes, n) == ((n & 1) ? first : 0) + bytes[3]);
    assert(checked(bytes, n) == bytes[n & 7]);
    assert(retained_loads(bytes, n) == first + n + bytes[3]);
    assert(call_barrier(bytes, n) == first + n + bytes[3]);
    assert(changed(bytes, n) == first + (unsigned char)n);
    assert(bytes[3] == (unsigned char)n);
  }
  assert(effects == 256);
  puts("compiler protection probes: ok");
}
