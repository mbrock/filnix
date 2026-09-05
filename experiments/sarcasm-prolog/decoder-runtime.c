#include <assert.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct decoder {
  const unsigned char *table, *input;
  unsigned char *output;
  uint64_t consumed;
};
struct node { struct node *next; uint64_t value; };
_Static_assert(sizeof(struct decoder) == 32 && offsetof(struct decoder, consumed) == 24, "decoder layout");
_Static_assert(sizeof(struct node) == 16 && offsetof(struct node, value) == 8, "node layout");
uint64_t tiny_decode(void *, uint64_t);
uint64_t loop_walk(void *, uint64_t);
#ifdef NATIVE
#define tiny_decode_plain tiny_decode
#define loop_walk_plain loop_walk
#else
uint64_t tiny_decode_plain(void *, uint64_t);
uint64_t loop_walk_plain(void *, uint64_t);
#endif
typedef uint64_t (*function)(void *, uint64_t);
static function decoders[] = {tiny_decode, tiny_decode_plain};
static function walkers[] = {loop_walk, loop_walk_plain};
static const unsigned char readonly_bytes[256] = {0};
static const struct decoder readonly_state = {readonly_bytes, readonly_bytes, NULL, 0};

/* A bytewise C reference derived from the format description. State must
   be separate from data; input, output and table may alias each other. */
static uint64_t reference(struct decoder *s, uint64_t bound) {
  uint64_t done = 0, status = 0;
  while (done < bound) {
    unsigned symbol = *s->input;
    if (symbol > 63) { status = 1; break; }
    uint32_t word = 0;
    for (unsigned i = 0; i < 4; i++)
      word |= (uint32_t)s->table[4 * symbol + i] << (8 * i);
    for (unsigned i = 0; i < 4; i++) s->output[i] = (unsigned char)(word >> (8 * i));
    s->input++;
    s->output += 4;
    done++;
  }
  s->consumed = done;
  return status;
}
static uint64_t random_word(uint64_t *s) {
  *s = *s * UINT64_C(6364136223846793005) + 1;
  return *s;
}
static void write_address_bits(void *slot, const void *pointer) {
  uintptr_t bits = (uintptr_t)pointer;
  volatile unsigned char *bytes = slot;
  for (unsigned i = 0; i < sizeof bits; i++) bytes[i] = bits >> (i * 8);
}
static int negative(const char *mode, unsigned variant) {
  unsigned char *table = calloc(1, 256), *input = calloc(1, 32), *output = calloc(1, 128);
  struct decoder state = {table, input, output, 0};
  uint64_t bound = 1;
  if (!strcmp(mode, "input-null")) state.input = NULL;
  else if (!strcmp(mode, "table-null")) state.table = NULL;
  else if (!strcmp(mode, "output-null")) state.output = NULL;
  else if (!strcmp(mode, "input-freed")) free(input);
  else if (!strcmp(mode, "output-freed")) free(output);
  else if (!strcmp(mode, "table-freed")) free(table);
  else if (!strcmp(mode, "input-oob")) { state.input = calloc(1, 16); bound = 17; }
  else if (!strcmp(mode, "output-oob")) { state.output = calloc(1, 64); bound = 17; }
  else if (!strcmp(mode, "table-oob")) { state.table = calloc(1, 16); input[0] = 4; }
  else if (!strcmp(mode, "table-tail")) { state.table = (unsigned char *)calloc(1, 16) + 2; input[0] = 3; }
  else if (!strcmp(mode, "output-readonly")) state.output = (void *)readonly_bytes;
  else if (!strcmp(mode, "state-readonly")) return decoders[variant]((void *)&readonly_state, 0);
  else if (!strcmp(mode, "state-null")) return decoders[variant](NULL, 0);
  else if (!strcmp(mode, "state-short")) return decoders[variant](calloc(1, 16), 0);
  else if (!strcmp(mode, "alias-oob")) {
    state.input = state.output = calloc(1, 16);
    bound = 5;
  } else if (!strncmp(mode, "walk-", 5)) {
    struct node *a = calloc(1, sizeof *a), *b = calloc(1, sizeof *b);
    a->next = b; a->value = 3; b->next = a; b->value = 7;
    if (!strcmp(mode, "walk-freed")) free(b);
    else if (!strcmp(mode, "walk-null")) a->next = NULL;
    else if (!strcmp(mode, "walk-forged")) write_address_bits(&a->next, a);
    else if (!strcmp(mode, "walk-bounds")) a->next = (void *)((unsigned char *)b + 8);
    else return 99;
    return walkers[variant](a, 2);
  } else return 99;
  return decoders[variant](&state, bound);
}

int main(int argc, char **argv) {
  if (argc > 1) return negative(argv[1], (unsigned)atoi(argv[2]));
  for (unsigned variant = 0; variant < 2; variant++) {
    uint64_t rng = 42;
    for (unsigned trial = 0; trial < 256; trial++)
      for (unsigned alignment = 0; alignment < 8; alignment++)
        for (unsigned alias = 0; alias < 5; alias++) {
          unsigned char table[272], expected_table[272], arena[640], expected_arena[640];
          for (unsigned i = 0; i < sizeof table; i++)
            table[i] = (unsigned char)((random_word(&rng) >> 32) & (trial % 2 ? 255 : 63));
          for (unsigned i = 0; i < sizeof arena; i++) arena[i] = (unsigned char)(random_word(&rng) >> 32);
          unsigned bound = (unsigned)(random_word(&rng) % 65), start = 40 + alignment;
          unsigned dest = alias == 0 ? 256 + alignment : alias == 1 ? start :
                          alias == 2 ? start + 1 : alias == 3 ? start - 3 : alignment;
          for (unsigned i = 0; i < bound; i++) arena[start + i] &= 63;
          if (bound && trial % 3 == 0) arena[start + random_word(&rng) % bound] |= 64;
          memcpy(expected_table, table, sizeof table);
          memcpy(expected_arena, arena, sizeof arena);
          unsigned char *out_base = alias == 4 ? table : arena;
          unsigned char *expected_out = alias == 4 ? expected_table : expected_arena;
          struct decoder actual = {table + alignment, arena + start, out_base + dest, UINT64_MAX};
          struct decoder expected = {expected_table + alignment, expected_arena + start, expected_out + dest, UINT64_MAX};
          uint64_t want = reference(&expected, bound);
          assert(decoders[variant](&actual, bound) == want);
          assert(actual.consumed == expected.consumed);
          assert(actual.input - arena == expected.input - expected_arena);
          assert(actual.output - out_base == expected.output - expected_out);
          assert(!memcmp(arena, expected_arena, sizeof arena));
          assert(!memcmp(table, expected_table, sizeof table));
          /* Saved cursor pointers still carry usable capabilities. */
          assert(*actual.input == *expected.input);
          assert(*actual.output == *expected.output);
        }
    unsigned char *table = malloc(256), *input = malloc(16), *output = calloc(1, 64);
    for (unsigned i = 0; i < 256; i++) table[i] = (unsigned char)i;
    memset(input, 63, 16);
    struct decoder boundary = {table, input, output, 0};
    assert(decoders[variant](&boundary, 16) == 0);
    assert(boundary.consumed == 16 && boundary.input == input + 16 && boundary.output == output + 64);
    for (unsigned i = 0; i < 64; i++) assert(output[i] == 252 + i % 4);
    struct decoder empty = {NULL, NULL, NULL, UINT64_MAX};
    assert(decoders[variant](&empty, 0) == 0 && empty.consumed == 0);
    input[0] = 64;
    struct decoder malformed = {NULL, input, NULL, UINT64_MAX};
    assert(decoders[variant](&malformed, 1) == 1 && malformed.consumed == 0);
    assert(malformed.input == input && malformed.output == NULL);
    struct node *nodes[8];
    for (unsigned i = 0; i < 8; i++) nodes[i] = malloc(sizeof *nodes[i]);
    for (unsigned i = 0; i < 8; i++) {
      nodes[i]->value = random_word(&rng);
      nodes[i]->next = nodes[(i + 3) % 8];
    }
    for (unsigned start = 0; start < 8; start++)
      for (unsigned count = 0; count <= 64; count++) {
        uint64_t sum = 0;
        const struct node *node = nodes[start];
        for (unsigned i = 0; i < count; i++, node = node->next) sum += node->value;
        assert(walkers[variant](nodes[start], count) == sum);
      }
    assert(walkers[variant](NULL, 0) == 0);
    for (unsigned i = 0; i < 8; i++) free(nodes[i]);
    free(table); free(input); free(output);
  }
  puts("decoder: ok (10240 cases, five alias layouts, exact boundaries and 520 node walks per variant)");
}
