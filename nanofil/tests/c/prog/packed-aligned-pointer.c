/* A packed struct may hold a pointer when the struct is aligned to 8
   and the pointer is at a multiple of 8 in it, so every instance has it
   8-aligned: parted's packed, aligned(8) GPTDiskData starts with a
   PedGeometry. reject/packed-pointer.c has the misaligned case. */
#include <stdio.h>
#include <stddef.h>
typedef struct { void *dev; long start, length, end; } Geom;
typedef struct { unsigned a; unsigned short b, c; unsigned char d[8]; } __attribute__((packed)) guid;
struct __attribute__((packed, aligned(8))) Disk { Geom data_area; int entry_count; guid uuid; int boot; long alt; };
struct __attribute__((packed, aligned(8))) Ptrs { char *p[2]; long n; };
int main(void) {
    static int x = 7;
    struct Disk d = { { &x, 1, 2, 3 }, 4, { 5, 6, 7, {8} }, 9, 10 };
    struct Disk arr[2] = { d, d };
    struct Ptrs q = { { "a", "b" }, 3 };
    printf("%zu %zu %zu %zu %zu\n", sizeof d, _Alignof(struct Disk), offsetof(struct Disk, uuid), offsetof(struct Disk, alt), sizeof q);
    printf("%d %ld %d %d %ld %s%s\n", *(int *)arr[1].data_area.dev, arr[1].data_area.end, d.entry_count, d.boot, d.alt, q.p[0], q.p[1]);
    return 0;
}
