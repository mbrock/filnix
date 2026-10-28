/* clang's __builtin_rotateleft8/16/32/64 and __builtin_rotateright*
   rotate an unsigned value of their width by a count taken modulo the
   width, so 0 and the width leave it unchanged (lighttpd's xxhash).
   Each operand is evaluated once. */
#include <stdint.h>
#include <stdio.h>
static int calls;
static uint32_t next(void) { return ++calls; }
int main(void)
{
    uint8_t b = 0x81;
    uint16_t h = 0x8001;
    uint32_t w = 0x80000001u;
    uint64_t q = 0x8000000000000001ull;
    printf("%x %x %x %x\n", __builtin_rotateleft8(b, 1), __builtin_rotateright8(b, 1),
           __builtin_rotateleft16(h, 4), __builtin_rotateright16(h, 4));
    printf("%x %x %x %x\n", __builtin_rotateleft32(w, 0), __builtin_rotateleft32(w, 32),
           __builtin_rotateleft32(w, 33), __builtin_rotateright32(w, 31));
    printf("%llx %llx %llx\n", (unsigned long long)__builtin_rotateleft64(q, 8),
           (unsigned long long)__builtin_rotateright64(q, 72),
           (unsigned long long)__builtin_rotateleft64(q, (uint64_t)-1));
    uint32_t r = __builtin_rotateleft32(next(), next());
    printf("%x %d %zu %zu\n", r, calls, sizeof __builtin_rotateleft8(b, 1),
           sizeof __builtin_rotateright64(q, 1));
    return 0;
}
