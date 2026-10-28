/* xz's memcmplen.h includes <immintrin.h> and uses none of it on
   x86-64. Its headers declare vector types (vector_size, some of
   _Float16 and __bf16) and static inline functions with asm bodies
   (hresetintrin.h's _hreset). Like clang, nanofil emits a static inline
   function only when it is used, and refuses those types and asm only
   where code it compiles uses them. A static function that nanofil
   cannot compile (amxcomplexintrin.h's __tile_cmmimfp16ps takes a
   struct with a vector member) is refused only if something refers to
   it; clang emits an unreferenced one not at all. */
#include <immintrin.h>
#include <stdio.h>
static inline unsigned ticks(void) {
    unsigned lo, hi;
    __asm__ volatile("rdtsc" : "=a"(lo), "=d"(hi));
    return lo ^ hi;
}
typedef int v4si __attribute__((vector_size(16)));
static inline v4si twice(v4si v) { return v + v; }
struct tile { v4si t; short rows; };
static void tile_zero(struct tile *dst, struct tile src) { dst->t = src.t; }
static int used_static(int x) { return x + 1; }
int main(void) {
    puts("no asm or vector was compiled");
    return used_static(-1);
}
