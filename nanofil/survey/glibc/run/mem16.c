/* memcmp, memcpy and memmove of 16 bytes and more, where the glibc
   units reach their alignment helpers. The helpers used to keep the
   block pointers as long int, which Fil-C traps on (regress.nix's
   units check, patches/filc-glibc-string-pointers.patch). Only the
   signs of the memcmp results are printed, since only the sign is
   specified. */
#include <stdio.h>
#include <string.h>

int main(void)
{
    unsigned char a[64], b[64];
    for (int i = 0; i < 64; i++) { a[i] = 0x40 + i; b[i] = 0x40 + i; }
    printf("eq: %d %d %d\n", memcmp(a, b, 16) == 0, memcmp(a, b, 24) == 0, memcmp(a, b, 48) == 0);
    b[15] += 1; b[31] += 1; b[63] += 1;
    printf("last bytes: %d %d %d\n",
           (memcmp(a, b, 16) < 0) - (memcmp(a, b, 16) > 0),
           (memcmp(a, b, 32) < 0) - (memcmp(a, b, 32) > 0),
           (memcmp(a, b, 64) < 0) - (memcmp(a, b, 64) > 0));
    for (int i = 0; i < 64; i++) { a[i] = 0x40 + i; b[i] = 0x40 + i; }
    for (int off = 1; off < 8; off++)
        printf("offset %d: %d %d\n", off,
               (memcmp(a, b + off, 24) < 0) - (memcmp(a, b + off, 24) > 0),
               memcmp(a + off, b, 24) == 0);
    /* memcpy(b, a, 16); memcpy(b + 8, a, 48); memmove(b + 4, b, 32)
       leaves b[0..3] = a[0..3] and b[56..63] untouched, everything
       between equal to some a[j] with j != i, so marked below. */
    memcpy(b, a, 16);
    memcpy(b + 8, a, 48);
    memmove(b + 4, b, 32);
    int same = 0;
    for (int i = 0; i < 64; i++) { b[i] = b[i] == a[i] ? b[i] : '!'; same += b[i] != '!'; }
    printf("copies: %d %d %d %d\n", same, b[0] == 0x40, b[32] == '!', b[63] == 0x7f);
    return 0;
}
