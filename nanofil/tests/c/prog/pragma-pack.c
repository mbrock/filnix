/* #pragma pack(N) caps the alignment of the members of each struct and
   union defined after it at N; push saves the current value, pop
   restores it. tpm2-tss's command header (sysapi_util.h) is a packed
   10-byte TPM20_Header_In that its marshalling code writes through a
   cast pointer; nanofil ignored the pragma and laid it out in 12. */
#include <stdio.h>
#include <stddef.h>
#include <string.h>

#pragma pack(push, 1)
typedef struct Hdr { unsigned short tag; unsigned size, code; } Hdr;
#pragma pack(push, 2)
union U { char c; int i; double d; };
struct P2 { char c; long l; struct { char a; int b; } in; };
#pragma pack(pop)
struct Inner1 { char c; short s; };
#pragma pack(pop)
struct Natural { char c; int i; };
#pragma pack(4)
struct P4 { char c; double d; short s; };
#pragma pack()
struct Again { char c; double d; };
#pragma pack(8)
struct P8 { char c; char *p; int i; };
#pragma pack()
/* A named push, and a pop to it past an unnamed one (GCC and clang). */
#pragma pack(push, outer, 2)
#pragma pack(push, 1)
struct N1 { char c; int i; };
#pragma pack(pop, outer)
struct N0 { char c; int i; };

static Hdr gh = { 0x8001, 12, 0x17b };

int main(void) {
    printf("%zu %zu %zu\n", sizeof(Hdr), offsetof(Hdr, size), offsetof(Hdr, code));
    printf("%zu %zu %zu %zu\n", sizeof(union U), _Alignof(union U), sizeof(struct P2), offsetof(struct P2, in));
    printf("%zu %zu %zu %zu\n", sizeof(struct Inner1), sizeof(struct Natural), sizeof(struct P4), offsetof(struct P4, s));
    printf("%zu %zu %zu %zu %zu\n", sizeof(struct Again), sizeof(struct P8), offsetof(struct P8, i),
           sizeof(struct N1), sizeof(struct N0));
    unsigned char buf[16];
    memset(buf, 0xee, sizeof buf);
    Hdr *h = (Hdr *)buf;
    h->tag = 0x0180;
    h->size = 0x0c000000;
    h->code = 0x7b010000;
    for (int i = 0; i < 12; i++) printf("%02x", buf[i]);
    printf("\n%x %u %x\n", gh.tag, gh.size, gh.code);
    struct P2 p = { 1, -2, { 3, 4 } };
    p.in.b += p.l;
    printf("%d %ld %d %d\n", p.c, p.l, p.in.a, p.in.b);
    return 0;
}
