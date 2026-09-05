#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
uint64_t table_entry(const void *, uint64_t);
uint64_t table_entry_plain(const void *, uint64_t);
uint64_t scalar_mix(const void *, uint64_t);
uint64_t changed_index(const void *, uint64_t);
int main(int argc, char **argv) {
  if (argc > 1) {
    if (!strcmp(argv[1], "null"))
      return table_entry(NULL, 0);
    if (!strcmp(argv[1], "overflow"))
      return table_entry("abcd", UINT64_MAX);
    unsigned char *short_object = malloc(16);
    memset(short_object, 1, 16);
    if (!strcmp(argv[1], "oob-plain"))
      return table_entry_plain(short_object + 14, 0);
    if (!strcmp(argv[1], "oob"))
      return table_entry(short_object + 14, 0);
    return 99;
  }
  uint64_t rng = 42;
  unsigned char data[65];
  for (unsigned trial = 0; trial < 1000; trial++) {
    for (unsigned j = 0; j < sizeof data; j++) {
      rng = rng * UINT64_C(6364136223846793005) + 1;
      data[j] = rng >> 56;
    }
    for (unsigned alignment = 0; alignment < 2; alignment++) {
      for (unsigned i = 0; i < 16; i++) {
        const unsigned char *p = data + alignment + 4 * i;
        uint64_t expected = (uint64_t)p[0] | (uint64_t)p[1] << 8 |
                            (uint64_t)p[2] << 16 | (uint64_t)p[3] << 24;
        assert(table_entry(data + alignment, i) == expected);
        assert(table_entry_plain(data + alignment, i) == expected);
      }
    }
    assert(scalar_mix(data, rng) ==
           (((uint64_t)(uint32_t)(rng - 1) << 1) ^ 0x1234));
    assert(changed_index(data, trial % 64) ==
           (uint64_t)data[trial % 64] + data[trial % 64 + 1]);
  }
  puts("runtime checks: ok (32000 lookup cases per variant)");
}
