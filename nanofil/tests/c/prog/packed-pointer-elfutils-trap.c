/* elfutils' packed Dwarf_Abbrev has its attrp pointer at 8: inside a
   buffer at an odd address the pointer is misaligned, and storing it
   traps, as filcc's alignment check does (prog/packed-pointer.c has the
   aligned accesses). */
// trap-reason
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
struct Dwarf_Abbrev {
    uint64_t offset;
    unsigned char *attrp;
    bool has_children : 1;
    unsigned int code : 31;
    unsigned int tag;
} __attribute__((packed));
int main(void)
{
    char *raw = calloc(64, 1);
    struct Dwarf_Abbrev *abb = (struct Dwarf_Abbrev *)(raw + 1);
    abb->code = 12;
    abb->tag = 3;
    printf("code %u tag %u\n", abb->code, abb->tag);
    fflush(stdout);
    abb->attrp = (unsigned char *)"abc";
    printf("%c\n", abb->attrp[0]);
    return 0;
}
