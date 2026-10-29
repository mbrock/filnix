/* A type name in an expression may define a struct: krb5's
   k5-platform.h reads and writes unaligned integers through
   ((struct { uint16_t i; } __attribute__((packed)) *)(p))->i. The tag is
   in scope to the end of the block. */
#include <stdint.h>
#include <stdio.h>

#define PUT(SIZE, PTR, VAL) (((struct { uint##SIZE##_t i; } __attribute__((packed)) *)(PTR))->i = (VAL))
#define GET(SIZE, PTR) (((const struct { uint##SIZE##_t i; } __attribute__((packed)) *)(PTR))->i)

static unsigned load_16(const void *p) { return GET(16, p); }
static uint32_t load_32(const void *p) { return GET(32, p); }
static void store_64(void *p, uint64_t v) { PUT(64, p, v); }

int main(void)
{
    unsigned char buf[16] = {0};
    for (int i = 0; i < 16; i++)
        buf[i] = (unsigned char)(i * 17);
    store_64(buf + 3, 0x0102030405060708ULL);
    uint32_t w = GET(32, buf + 1);
    unsigned n = sizeof(struct pair { short a, b; }) + ((struct pair *)buf)->b;
    struct pair q = {3, 4};
    if (((struct { int k; } *)&n)->k > 0)
        printf("%u %u %u %u %d\n", load_16(buf + 1), load_32(buf + 5), w, n, q.a + q.b);
    return 0;
}
