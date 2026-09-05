#include <stdint.h>
struct decoder {
  const unsigned char *table, *input;
  unsigned char *output;
  uint64_t consumed;
};
struct node { struct node *next; uint64_t value; };
uint64_t table_entry(const void *, uint64_t);
uint64_t tiny_decode(void *, uint64_t);
uint64_t loop_walk(void *, uint64_t);
