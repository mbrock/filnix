#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint64_t checks_cover(void *, uint64_t);
uint64_t checks_diamond(void *, uint64_t);
uint64_t checks_one_path(void *, uint64_t);
uint64_t checks_store(void *, uint64_t);
uint64_t checks_index(void *, uint64_t);
uint64_t checks_cycle(void *, uint64_t);
uint64_t checks_local_loop(void *, uint64_t);
#ifdef NATIVE
#define checks_plain_cover checks_cover
#define checks_plain_diamond checks_diamond
#define checks_plain_one_path checks_one_path
#define checks_plain_store checks_store
#define checks_plain_index checks_index
#define checks_plain_cycle checks_cycle
#define checks_plain_local_loop checks_local_loop
#else
uint64_t checks_plain_cover(void *, uint64_t);
uint64_t checks_plain_diamond(void *, uint64_t);
uint64_t checks_plain_one_path(void *, uint64_t);
uint64_t checks_plain_store(void *, uint64_t);
uint64_t checks_plain_index(void *, uint64_t);
uint64_t checks_plain_cycle(void *, uint64_t);
uint64_t checks_plain_local_loop(void *, uint64_t);
#endif
typedef uint64_t (*function)(void *, uint64_t);
static function functions[][7] = {
  {checks_cover, checks_diamond, checks_one_path, checks_store, checks_index, checks_cycle, checks_local_loop},
  {checks_plain_cover, checks_plain_diamond, checks_plain_one_path, checks_plain_store,
   checks_plain_index, checks_plain_cycle, checks_plain_local_loop}
};
static const unsigned char readonly_data[128] = {42};
static uint64_t read8(const unsigned char *p) {
  uint64_t value = 0;
  for (unsigned i = 0; i < 8; i++) value |= (uint64_t)p[i] << (8 * i);
  return value;
}
static uint64_t reference(unsigned which, unsigned char *p, uint64_t n) {
  switch (which) {
  case 0: return read8(p) + n + p[3];
  case 1: return ((n & 1) ? read8(p) + n : read8(p) ^ n) + p[3];
  case 2: return ((n & 1) ? read8(p) : 0) + p[3];
  case 3: {
    uint64_t first = read8(p);
    for (unsigned i = 0; i < 4; i++) p[i + 1] = (unsigned char)(n >> (8 * i));
    return first + p[3];
  }
  case 4: return read8(p + n) + p[n + 1];
  case 5: return read8(p) + (n & 7) * p[3];
  default: {
    uint64_t result = 0;
    for (unsigned i = 0; i < (n & 7); i++) result += read8(p + 8 * i) + p[8 * i + 3];
    return result;
  }
  }
}
static int negative(const char *mode, unsigned variant) {
  unsigned char *bytes = calloc(1, 16);
  if (!strcmp(mode, "null")) return functions[variant][0](NULL, 0);
  if (!strcmp(mode, "freed")) { free(bytes); return functions[variant][1](bytes, 1); }
  if (!strcmp(mode, "cover-tail")) return functions[variant][0](bytes + 12, 0);
  if (!strcmp(mode, "checked-arm-tail")) return functions[variant][2](bytes + 12, 1);
  if (!strcmp(mode, "unchecked-arm-tail")) return functions[variant][2](bytes + 16, 0);
  if (!strcmp(mode, "readonly")) return functions[variant][3]((void *)readonly_data, 7);
  if (!strcmp(mode, "index-overflow")) return functions[variant][4](bytes, UINT64_MAX);
  if (!strcmp(mode, "local-loop-tail")) return functions[variant][6](bytes, 3);
  return 99;
}
int main(int argc, char **argv) {
  if (argc > 1) return negative(argv[1], (unsigned)atoi(argv[2]));
  for (unsigned variant = 0; variant < 2; variant++) {
    for (unsigned trial = 0; trial < 256; trial++)
      for (unsigned alignment = 0; alignment < 8; alignment++)
        for (unsigned f = 0; f < 7; f++) {
          unsigned char actual[128], expected[128];
          for (unsigned i = 0; i < sizeof actual; i++) actual[i] = (unsigned char)(i * 179 + trial * 31);
          memcpy(expected, actual, sizeof actual);
          uint64_t n = f == 4 ? trial % 8 : (UINT64_C(0xfedcba9876543200) | trial);
          uint64_t want = reference(f, expected + alignment, n);
          assert(functions[variant][f](actual + alignment, n) == want);
          assert(!memcmp(actual, expected, sizeof actual));
        }
    /* The wide read occurs only on the other arm. Hoisting that check here
       would reject a valid one-byte read at the allocation's last byte. */
    unsigned char *bytes = calloc(1, 16);
    bytes[15] = 123;
    assert(functions[variant][2](bytes + 12, 0) == 123);
    free(bytes);
  }
  puts("check reuse fixtures: ok (14336 cases and conditional boundary per variant)");
}
