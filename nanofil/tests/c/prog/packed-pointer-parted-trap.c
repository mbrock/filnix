/* parted's packed GPT header has Reserved2 at 92: in a malloc'd header
   the pointer is misaligned, and parted's pth_new storing it traps, as
   filcc's alignment check does (prog/packed-pointer.c places a header
   where it is aligned). */
// trap-reason
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
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
int main(void)
{
    struct GptHeader *pth = calloc(1, sizeof *pth);
    pth->SizeOfPartitionEntry = 128;
    printf("entry %u\n", pth->SizeOfPartitionEntry);
    fflush(stdout);
    pth->Reserved2 = malloc(420);
    printf("%d\n", pth->Reserved2 != 0);
    return 0;
}
