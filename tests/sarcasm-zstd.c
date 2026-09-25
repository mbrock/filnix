#include <assert.h>
#include <stdint.h>
#include <string.h>
extern uint64_t unaligned_load(void *);
extern void unaligned_store(void *, unsigned);
extern void *pointer_load(void *);
int main(int argc, char **argv) {
  unsigned char bytes[32];
  for (unsigned i = 0; i < sizeof bytes; ++i)
    bytes[i] = i;
  void *pointers[2] = {bytes, bytes};
  if (argc > 1) {
    if (!strcmp(argv[1], "load-oob"))
      return (int)unaligned_load(bytes + 25);
    if (!strcmp(argv[1], "store-oob"))
      unaligned_store(bytes + 31, 42);
    if (!strcmp(argv[1], "readonly"))
      unaligned_store("immutable", 42);
    if (!strcmp(argv[1], "pointer-alignment"))
      return pointer_load((char *)pointers + 1) != 0;
    return 0;
  }
  uint64_t expected;
  memcpy(&expected, bytes + 1, sizeof expected);
  assert(unaligned_load(bytes + 1) == expected);
  unaligned_store(bytes + 3, 0xabcd);
  assert(bytes[3] == 0xcd && bytes[4] == 0xab);
  assert(pointer_load(pointers) == bytes);
  return 0;
}
