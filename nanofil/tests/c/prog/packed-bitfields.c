/* Packed bit-fields follow the bits before them across any boundary; a
   zero-width one still moves to its type's boundary. parted's GPT
   partition attributes are one packed uint64_t of bit-fields, and its
   verify() checks the sizes. Each field is read, written and statically
   initialized, and the bytes are printed. */
#include <stdio.h>
#include <stdint.h>
#include <string.h>

struct __attribute__((packed)) attrs {
    uint64_t RequiredToFunction:1;
    uint64_t NoBlockIOProtocol:1;
    uint64_t LegacyBIOSBootable:1;
    uint64_t Reserved:45;
    uint64_t GuidSpecific:15;
    uint64_t NoAutomount:1;
};
struct __attribute__((packed)) entry { uint8_t type[16]; struct attrs a; uint16_t name[3]; };
struct __attribute__((packed)) mixed { char a; int x:30; char b; short s:4; int :0; char c; long l:60; };

_Static_assert(sizeof(struct attrs) == 8, "attrs");
_Static_assert(sizeof(struct entry) == 30, "entry");

static struct mixed gm = { 1, -5, 2, -3, 4, -77 };
static struct attrs ga = { 1, 0, 1, 0x123456789ULL, 0x7abc, 1 };

static void bytes(const void *p, size_t n) {
    const unsigned char *b = p;
    for (size_t i = 0; i < n; i++) printf("%02x", b[i]);
    printf("\n");
}

int main(void) {
    struct entry e;
    memset(&e, 0, sizeof e);
    e.a.GuidSpecific = 0x7fff;
    e.a.LegacyBIOSBootable = 1;
    e.a.Reserved = 5;
    e.name[0] = 'x';
    printf("%u %u %llu\n", (unsigned)e.a.GuidSpecific, (unsigned)e.a.NoAutomount,
           (unsigned long long)e.a.Reserved);
    bytes(&e, sizeof e);
    struct mixed m = gm;
    m.x += 7; m.s = 5; m.l = m.l * 3;
    printf("%zu %d %d %d %d %d %ld\n", sizeof m, m.a, m.x, m.b, m.s, m.c, m.l);
    bytes(&gm, sizeof gm);
    bytes(&m, sizeof m);
    bytes(&ga, sizeof ga);
    return 0;
}
