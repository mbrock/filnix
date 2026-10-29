/* A packed struct may hold a pointer anywhere. Fil-C keeps a pointer's
   capability only at an 8-aligned address, and each access of a pointer
   checks at run time that its address is 8-aligned, as filcc's does:
   these accesses are all at 8-aligned addresses, so none traps. The
   layouts are libmbim's fragment_info, elfutils' Dwarf_Abbrev and
   parted's GPT header (Reserved2 at 92); packed-pointer-*-trap.c
   access each at a misaligned address. */
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct header { uint32_t type, length, transaction_id; } __attribute__((packed));
struct fragment_header { uint32_t total, current; } __attribute__((packed));
struct fragment_info {
    struct header header;
    struct fragment_header fragment_header;
    uint32_t data_length;
    const uint8_t *data;
} __attribute__((packed));

struct Dwarf_Abbrev {
    uint64_t offset;
    unsigned char *attrp;
    bool has_children : 1;
    unsigned int code : 31;
    unsigned int tag;
} __attribute__((packed));

typedef struct { uint32_t a; uint16_t b, c; uint8_t d, e, node[6]; } __attribute__((packed)) efi_guid_t;
struct __attribute__((packed)) GptHeader {
    uint64_t Signature;
    uint32_t Revision, HeaderSize, HeaderCRC32, Reserved1;
    uint64_t MyLBA, AlternateLBA, FirstUsableLBA, LastUsableLBA;
    efi_guid_t DiskGUID;
    uint64_t PartitionEntryLBA;
    uint32_t NumberOfPartitionEntries, SizeOfPartitionEntry, PartitionEntryArrayCRC32;
    uint8_t *Reserved2;
};

/* A pointer at 1, and the former reject tests' #pragma pack(4) and
   aligned(1) pointer members. */
struct __attribute__((packed)) mis { char c; int *p; };
#pragma pack(4)
struct pack4 { char c; int *p; };
#pragma pack()
typedef int *up __attribute__((aligned(1)));
struct under { char c; up p; };

static int x = 7, y = 9;
static const uint8_t bytes[] = "abc";

int main(void)
{
    printf("%zu %zu %zu | %zu %zu %zu | %zu %zu %zu\n",
           sizeof(struct fragment_info), offsetof(struct fragment_info, data), _Alignof(struct fragment_info),
           sizeof(struct Dwarf_Abbrev), offsetof(struct Dwarf_Abbrev, attrp), _Alignof(struct Dwarf_Abbrev),
           sizeof(struct GptHeader), offsetof(struct GptHeader, Reserved2), _Alignof(struct GptHeader));
    printf("%zu %zu %zu %zu %zu %zu\n", sizeof(struct mis), offsetof(struct mis, p),
           sizeof(struct pack4), offsetof(struct pack4, p), sizeof(struct under), offsetof(struct under, p));

    /* libmbim: an array of fragments, as _mbim_message_split_fragments
       allocates it, and a copy by assignment. */
    struct fragment_info *frags = calloc(3, sizeof *frags);
    for (int i = 0; i < 3; i++) {
        frags[i].header.type = 3;
        frags[i].fragment_header.current = i;
        frags[i].data_length = 1;
        frags[i].data = bytes + i;
    }
    struct fragment_info copy = frags[2];
    printf("mbim %c%c %c %u\n", *frags[0].data, *(frags + 1)->data, *copy.data, copy.fragment_header.current);

    /* elfutils: from a typed allocation, its bit-fields beside the pointer. */
    struct Dwarf_Abbrev *abb = malloc(sizeof *abb);
    abb->offset = 11;
    abb->attrp = (unsigned char *)"xyz";
    abb->has_children = 1;
    abb->code = 0x7fffffff;
    abb->tag = 5;
    struct Dwarf_Abbrev a2 = *abb;
    printf("elf %c %d %u %u %c\n", abb->attrp[1], a2.has_children, a2.code, a2.tag, a2.attrp[2]);

    /* parted: the header placed so that Reserved2, at 92, is 8-aligned. */
    uint64_t *store = calloc(16, 8);
    struct GptHeader *gpt = (struct GptHeader *)((char *)store + 4);
    gpt->Signature = 0x5452415020494645LL;
    gpt->Reserved2 = malloc(4);
    memset(gpt->Reserved2, 'r', 4);
    printf("gpt %llx %c\n", (unsigned long long)gpt->Signature, gpt->Reserved2[3]);

    /* A copy through misaligned memory keeps the bytes but not the
       capability: memcpy keeps one only where both ends are 8-aligned. */
    char *raw = calloc(64, 1);
    struct Dwarf_Abbrev *odd = (struct Dwarf_Abbrev *)(raw + 33);
    *odd = *abb;
    struct Dwarf_Abbrev back = *odd;
    printf("odd %d %u\n", back.attrp == abb->attrp, odd->tag);

    /* A pointer at 1 is 8-aligned in an object at 7 mod 8: it keeps its
       capability, also across a copy to another such place. */
    char *raw2 = calloc(64, 1);
    struct mis *m1 = (struct mis *)(raw2 + 7), *m2 = (struct mis *)(raw2 + 23);
    m1->c = 'm';
    m1->p = &y;
    *m2 = *m1;
    printf("mis %c %d\n", m2->c, *m2->p);

    struct pack4 *q = (struct pack4 *)(raw2 + 36);
    q->p = &x;
    struct under *u = (struct under *)(raw2 + 47);
    u->p = &y;
    printf("pack %d %d\n", *q->p, *u->p);
    return 0;
}
