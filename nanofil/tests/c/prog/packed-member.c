/* packed on a member gives that member alignment 1 unless aligned asks
   for more (GCC, Common Variable Attributes, packed), whatever the
   struct's own packing: glibc's struct __res_state, inside struct
   pthread, ends in `unsigned long long __glibc_extension_index
   __attribute__((packed))`. Offsets, sizes and alignments by hand:
   a: l at 1, d at 9, size 10, align 1; b: i at 2, size 6, align 2;
   c: q at 40 (already 8-aligned), size 48; d: s at 1, z at 8, size 16;
   e: packed listed with another attribute, i at 1, j at 8, size 12;
   f: a typedef's alignment gives way too, t at 1, size 9. */
#include <stdio.h>
#include <stddef.h>
typedef long wide __attribute__((aligned(16)));
struct a { char c; long l __attribute__((packed)); char d; };
struct b { char c; int i __attribute__((packed, aligned(2))); };
struct c { char c; struct { char x; void *p[3]; long long q __attribute__((packed)); } e; };
struct d { char c; short s __attribute__((__packed__)); long z; };
struct e { char c; int i __attribute__((unused, packed)); int j; };
struct f { char c; wide t __attribute__((packed)); };
int main(void)
{
    printf("%zu %zu %zu %zu | %zu %zu %zu\n", sizeof(struct a), _Alignof(struct a),
           offsetof(struct a, l), offsetof(struct a, d),
           sizeof(struct b), _Alignof(struct b), offsetof(struct b, i));
    printf("%zu %zu | %zu %zu %zu\n", sizeof(struct c), offsetof(struct c, e.q),
           sizeof(struct d), offsetof(struct d, s), offsetof(struct d, z));
    printf("%zu %zu %zu | %zu %zu %zu\n", sizeof(struct e), offsetof(struct e, i),
           offsetof(struct e, j), sizeof(struct f), _Alignof(struct f), offsetof(struct f, t));
    struct a v = { 1, 0x1122334455667788, 3 };
    struct e w = { 2, -5, 7 };
    printf("%lx %d %d %d\n", v.l, v.d, w.i, w.j);
    return 0;
}
