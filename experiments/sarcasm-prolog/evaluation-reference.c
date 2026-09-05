#include "evaluation.h"

/* Both references are compiled separately from the caller without LTO.
   PACKED uses ordinary checked memcpy for a competitive C baseline. */
uint64_t table_entry(const void *base, uint64_t index) {
  const unsigned char *p = (const unsigned char *)base + index * 4;
#ifdef PACKED
  uint32_t result;
  __builtin_memcpy(&result, p, 4);
  return result;
#else
  return (uint64_t)p[0] | (uint64_t)p[1] << 8 |
         (uint64_t)p[2] << 16 | (uint64_t)p[3] << 24;
#endif
}
uint64_t tiny_decode(void *state, uint64_t bound) {
  struct decoder *s = state;
  const unsigned char *input = s->input, *table = s->table;
  unsigned char *output = s->output;
  uint64_t done = 0, status = 0;
  while (done < bound) {
    unsigned symbol = *input;
    if (symbol > 63) { status = 1; break; }
    uint32_t word = 0;
#ifdef PACKED
    __builtin_memcpy(&word, table + 4 * symbol, 4);
    __builtin_memcpy(output, &word, 4);
#else
    for (unsigned j = 0; j < 4; j++) word |= (uint32_t)table[4 * symbol + j] << (8 * j);
    for (unsigned j = 0; j < 4; j++) output[j] = (unsigned char)(word >> (8 * j));
#endif
    input++; output += 4; done++;
  }
  s->input = input; s->output = output; s->consumed = done;
  return status;
}
uint64_t loop_walk(void *start, uint64_t bound) {
  const struct node *p = start;
  uint64_t sum = 0;
  for (uint64_t i = 0; i < bound; i++, p = p->next) sum += p->value;
  return sum;
}
