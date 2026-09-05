#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint64_t slot_read(void *, uint64_t);
uint64_t slot_copy(void *);
uint64_t slot_self(void *);
uint64_t slot_write(void *, uint64_t);
uint64_t slot_plain_read(void *, uint64_t);
uint64_t slot_plain_copy(void *);
uint64_t slot_plain_self(void *);
uint64_t slot_plain_write(void *, uint64_t);
typedef uint64_t (*indexed_fn)(void *, uint64_t);
typedef uint64_t (*unary_fn)(void *);
static indexed_fn reads[] = {slot_read, slot_plain_read};
static indexed_fn writes[] = {slot_write, slot_plain_write};
static unary_fn copies[] = {slot_copy, slot_plain_copy};
static unary_fn selves[] = {slot_self, slot_plain_self};
static const unsigned char readonly_data[16] = {42};
static const void *const readonly_slots[2] = {readonly_data, readonly_data};

/* Volatile byte stores change the address bits without copying a capability.
   A fresh slot and a slot that previously held a pointer are different tests. */
static void write_address_bits(void *slot, const void *pointer) {
  uintptr_t bits = (uintptr_t)pointer;
  volatile unsigned char *bytes = slot;
  for (unsigned i = 0; i < sizeof bits; i++) bytes[i] = bits >> (i * 8);
}

static int negative(const char *mode, unsigned variant) {
  unsigned char *slots = calloc(1, 16);
  unsigned char *a = calloc(1, 16), *b = calloc(1, 16);
  if (!strcmp(mode, "fresh-address")) {
    write_address_bits(slots, a);
    return reads[variant](slots, 0);
  }
  *(void **)slots = a;
  if (!strcmp(mode, "changed-address")) {
    write_address_bits(slots, b);
    return reads[variant](slots, 0);
  }
  if (!strcmp(mode, "free-pointee")) {
    free(a);
    return copies[variant](slots);
  }
  if (!strcmp(mode, "free-slot")) {
    free(slots);
    return reads[variant](slots, 0);
  }
  if (!strcmp(mode, "free-slot-write")) {
    free(slots);
    return writes[variant](slots, 0);
  }
  if (!strcmp(mode, "null-slot")) return reads[variant](NULL, 0);
  if (!strcmp(mode, "null-pointee")) {
    *(void **)slots = NULL;
    return reads[variant](slots, 0);
  }
  if (!strcmp(mode, "load-align")) return reads[variant](slots + 1, 0);
  if (!strcmp(mode, "store-align")) return writes[variant](slots, 1);
  if (!strcmp(mode, "load-oob")) return reads[variant](slots + 16, 0);
  if (!strcmp(mode, "store-oob")) return writes[variant](slots, 16);
  if (!strcmp(mode, "store-readonly")) return writes[variant]((void *)readonly_slots, 0);
  if (!strcmp(mode, "store-overflow")) return writes[variant](slots, UINT64_MAX);
  if (!strcmp(mode, "pointee-oob")) return reads[variant](slots, 16);
  if (!strcmp(mode, "readonly-pointee-write")) {
    *(const void **)slots = readonly_data;
    assert(copies[variant](slots) == 42);
    *(unsigned char *)((void **)slots)[1] = 7;
    return 0;
  }
  return 99;
}

int main(int argc, char **argv) {
  if (argc > 1) return negative(argv[1], argc > 2 ? 1 : 0);
  for (unsigned variant = 0; variant < 2; variant++) {
    for (unsigned trial = 0; trial < 256; trial++) {
      unsigned char data[32];
      for (unsigned i = 0; i < sizeof data; i++) data[i] = trial + i * 23;
      void *slots[2] = {NULL, NULL};
      for (unsigned alignment = 0; alignment < 8; alignment++) {
        slots[0] = data + alignment;
        for (unsigned index = 0; index < 8; index++)
          assert(reads[variant](slots, index) == data[alignment + index]);
        assert(copies[variant](slots) == data[alignment]);
        assert(slots[1] == slots[0]);
        assert(*(unsigned char *)slots[1] == data[alignment]);
        *(unsigned char *)slots[1] ^= 1;
        assert(reads[variant](slots, 0) == data[alignment]);
      }
      assert(selves[variant](slots) == (uintptr_t)slots);
      assert(slots[0] == slots && *(void **)slots[0] == slots);
    }
  }
  puts("pointer slots: ok (16384 indexed reads, 2048 round trips, 256 self references per variant)");
}
