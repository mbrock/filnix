/* An aligned attribute's argument may name a typedef: libiberty's md5.h
   declares char buffer[128] __attribute__ ((__aligned__ (__alignof__
   (md5_uint32)))). */
#include <stddef.h>
#include <stdio.h>

typedef unsigned int md5_uint32;
typedef double wide __attribute__((aligned(sizeof(md5_uint32) * 4)));

struct md5_ctx {
    md5_uint32 total[2];
    md5_uint32 buflen;
    char buffer[128] __attribute__((__aligned__(__alignof__(md5_uint32))));
    char tail __attribute__((aligned(_Alignof(wide))));
};

static wide w;

int main(void)
{
    struct md5_ctx c = {{1, 2}, 3, "abc", 'x'};
    printf("%zu %zu %zu %zu %s %c\n", sizeof c, offsetof(struct md5_ctx, buffer),
           offsetof(struct md5_ctx, tail), _Alignof(wide), &c.buffer[0], c.tail);
    printf("%d\n", (int)((size_t)&w % 16));
    return 0;
}
