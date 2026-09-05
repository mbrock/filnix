#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

uint64_t branch_read(void *, uint64_t);
uint64_t branch_store(void *, uint64_t);
uint64_t branch_checked(void *, uint64_t);
uint64_t branch_swap(void *, uint64_t);
uint64_t branch_plain_read(void *, uint64_t);
uint64_t branch_plain_store(void *, uint64_t);
uint64_t branch_plain_checked(void *, uint64_t);
uint64_t branch_plain_swap(void *, uint64_t);
typedef uint64_t (*function)(void *, uint64_t);
static function reads[] = {branch_read, branch_plain_read};
static function stores[] = {branch_store, branch_plain_store};
static function checked[] = {branch_checked, branch_plain_checked};
static function swaps[] = {branch_swap, branch_plain_swap};
static const unsigned char readonly_data[16] = {42};

static void write_address_bits(void *slot, const void *pointer) {
  uintptr_t bits = (uintptr_t)pointer;
  volatile unsigned char *bytes = slot;
  for (unsigned i = 0; i < sizeof bits; i++) bytes[i] = bits >> (8 * i);
}

static int negative(const char *mode, unsigned variant, unsigned choice) {
  unsigned char *a = calloc(1, 16), *b = calloc(1, 16);
  void **slots = calloc(2, sizeof(void *));
  slots[0] = a;
  slots[1] = b;
  if (!strcmp(mode, "null")) slots[choice] = NULL;
  else if (!strcmp(mode, "freed")) free(slots[choice]);
  else if (!strcmp(mode, "bounds")) slots[choice] = (unsigned char *)slots[choice] + 16;
  else if (!strcmp(mode, "readonly")) {
    slots[choice] = (void *)readonly_data;
    return stores[variant](slots, choice);
  } else if (!strcmp(mode, "checked-origin")) {
    /* Retain the selected slot's capability while changing its address to
       the other object's address. On arm one, a was read before the join. */
    write_address_bits(slots + choice, choice ? a : b);
    return checked[variant](slots, choice);
  } else if (!strcmp(mode, "checked-null")) {
    slots[choice] = NULL;
    return checked[variant](slots, choice);
  } else if (!strcmp(mode, "swap-readonly")) {
    slots[!choice] = (void *)readonly_data;
    return swaps[variant](slots, choice);
  } else return 99;
  return reads[variant](slots, choice);
}

int main(int argc, char **argv) {
  if (argc > 1) return negative(argv[1], (unsigned)atoi(argv[2]), (unsigned)atoi(argv[3]));
  for (unsigned variant = 0; variant < 2; variant++)
    for (unsigned trial = 0; trial < 256; trial++)
      for (unsigned offset = 0; offset < 8; offset++)
        for (unsigned choice = 0; choice < 2; choice++) {
          unsigned char a[32], b[32], expected_a[32], expected_b[32];
          for (unsigned i = 0; i < sizeof a; i++) {
            a[i] = (unsigned char)(trial + i * 13);
            b[i] = (unsigned char)(trial * 17 + i * 7);
          }
          void *slots[] = {a + offset, b + offset};
          unsigned char *selected = choice ? b + offset : a + offset;
          assert(reads[variant](slots, choice) == *selected);
          assert(checked[variant](slots, choice) == *selected);
          /* Reads and stores do not touch the unselected null pointer. */
          slots[!choice] = NULL;
          assert(reads[variant](slots, choice) == *selected);
          uint64_t value = ((uint64_t)trial << 32) | choice;
          memcpy(expected_a, a, sizeof a);
          memcpy(expected_b, b, sizeof b);
          memcpy((choice ? expected_b : expected_a) + offset, &value, sizeof value);
          assert(stores[variant](slots, value) == value);
          assert(!memcmp(expected_a, a, sizeof a) && !memcmp(expected_b, b, sizeof b));
          slots[0] = a + offset;
          slots[1] = b + offset;
          memcpy(&value, selected, sizeof value);
          memcpy((choice ? expected_a : expected_b) + offset, &value, sizeof value);
          assert(swaps[variant](slots, choice) == value);
          assert(!memcmp(expected_a, a, sizeof a) && !memcmp(expected_b, b, sizeof b));
          /* Both parameters may denote the very same object. */
          slots[0] = slots[1] = a + offset;
          memcpy(&value, a + offset, sizeof value);
          assert(swaps[variant](slots, choice) == value);
        }
  puts("branch capabilities: ok (4096 selections, stores and swaps per variant)");
}
