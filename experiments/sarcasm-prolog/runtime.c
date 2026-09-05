#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
uint64_t table_entry(const void *, uint64_t);
uint64_t table_entry_plain(const void *, uint64_t);
uint64_t scalar_mix(const void *, uint64_t);
uint64_t changed_index(const void *, uint64_t);
uint64_t pointer_entry(const void *, uint64_t);
uint64_t pointer_entry_plain(const void *, uint64_t);
uint64_t integer_update(void *, uint64_t);
uint64_t integer_update_plain(void *, uint64_t);
uint64_t integer_store(void *, uint64_t);
uint64_t integer_store_plain(void *, uint64_t);

static uint64_t read_integer(const unsigned char *p, unsigned bytes) {
  uint64_t value = 0;
  for (unsigned i = 0; i < bytes; i++) value |= (uint64_t)p[i] << (i * 8);
  return value;
}
static void write_integer(unsigned char *p, unsigned bytes, uint64_t value) {
  for (unsigned i = 0; i < bytes; i++) p[i] = value >> (i * 8);
}
static uint64_t update_reference(unsigned char *p, uint64_t input) {
  uint32_t first = (uint32_t)read_integer(p, 4) + (uint32_t)input;
  write_integer(p + 1, 4, first);
  uint64_t second = read_integer(p + 1, 8);
  write_integer(p + 9, 8, UINT64_MAX);
  second ^= input;
  write_integer(p + 2, 8, second);
  return read_integer(p + 2, 8);
}
int main(int argc, char **argv) {
  if (argc > 1) {
    if (!strcmp(argv[1], "null"))
      return table_entry(NULL, 0);
    if (!strcmp(argv[1], "overflow"))
      return table_entry("abcd", UINT64_MAX);
    if (!strcmp(argv[1], "pointer-overflow"))
      return pointer_entry("abcd", UINT64_MAX);
    if (!strcmp(argv[1], "pointer-null"))
      return pointer_entry(NULL, 0);
    if (!strcmp(argv[1], "pointer-missing-capability"))
      return pointer_entry((const void *)(uintptr_t)0x1234, 0);
    if (!strcmp(argv[1], "store-overflow"))
      return integer_store((void *)"abcdefghijklmnop", UINT64_MAX);
    if (!strcmp(argv[1], "store-null"))
      return integer_store(NULL, 0);
    if (!strcmp(argv[1], "store-missing-capability"))
      return integer_store((void *)(uintptr_t)0x1234, 0);
    if (!strcmp(argv[1], "store-readonly"))
      return integer_store((void *)"abcdefghijklmnop", 0);
    unsigned char *short_object = malloc(16);
    memset(short_object, 1, 16);
    if (!strcmp(argv[1], "oob-plain"))
      return table_entry_plain(short_object + 14, 0);
    if (!strcmp(argv[1], "oob"))
      return table_entry(short_object + 14, 0);
    if (!strcmp(argv[1], "pointer-oob"))
      return pointer_entry(short_object + 11, 0);
    if (!strcmp(argv[1], "pointer-oob-plain"))
      return pointer_entry_plain(short_object + 11, 0);
    if (!strcmp(argv[1], "pointer-freed")) {
      free(short_object);
      return pointer_entry(short_object, 0);
    }
    if (!strcmp(argv[1], "store-oob"))
      return integer_store(short_object + 12, 0);
    if (!strcmp(argv[1], "store-oob-plain"))
      return integer_store_plain(short_object + 12, 0);
    if (!strcmp(argv[1], "store-freed")) {
      free(short_object);
      return integer_store(short_object, 0);
    }
    return 99;
  }
  uint64_t rng = 42;
  unsigned char data[72];
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
        p += 3;
        expected = (uint64_t)p[0] | (uint64_t)p[1] << 8 |
                   (uint64_t)p[2] << 16 | (uint64_t)p[3] << 24;
        assert(pointer_entry(data + alignment, i) == expected);
        assert(pointer_entry_plain(data + alignment, i) == expected);
      }
    }
    assert(scalar_mix(data, rng) ==
           (((uint64_t)(uint32_t)(rng - 1) << 1) ^ 0x1234));
    assert(changed_index(data, trial % 64) ==
           (uint64_t)data[trial % 64] + data[trial % 64 + 1]);
    for (unsigned alignment = 0; alignment < 8; alignment++) {
      unsigned char changed[40], plain[40], reference[40];
      memcpy(changed, data, sizeof changed);
      memcpy(plain, data, sizeof plain);
      memcpy(reference, data, sizeof reference);
      uint64_t expected = update_reference(reference + alignment, rng);
      assert(integer_update(changed + alignment, rng) == expected);
      assert(integer_update_plain(plain + alignment, rng) == expected);
      assert(!memcmp(changed, reference, sizeof changed));
      assert(!memcmp(plain, reference, sizeof plain));
    }
  }
  puts("runtime checks: ok (32000 lookup and pointer cases per variant)");
  puts("store checks: ok (8000 overlapping read/write cases per variant)");
}
