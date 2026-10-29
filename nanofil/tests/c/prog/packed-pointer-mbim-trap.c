/* libmbim's packed fragment_info has its data pointer at 24: in an
   array that starts at 4 mod 8 the pointer is misaligned, and reading
   it traps, as filcc's alignment check does (prog/packed-pointer.c has
   the aligned accesses). */
// trap-reason
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
struct header { uint32_t type, length, transaction_id; } __attribute__((packed));
struct fragment_header { uint32_t total, current; } __attribute__((packed));
struct fragment_info {
    struct header header;
    struct fragment_header fragment_header;
    uint32_t data_length;
    const uint8_t *data;
} __attribute__((packed));
int main(void)
{
    char *raw = calloc(80, 1);
    struct fragment_info *frags = (struct fragment_info *)(raw + 4);
    frags[1].data_length = 3;
    printf("length %u\n", frags[1].data_length);
    fflush(stdout);
    printf("%p\n", (void *)frags[1].data);
    return 0;
}
