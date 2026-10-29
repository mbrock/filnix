/* GNU case ranges, as procps (case '0' ... '9':) and libinput write
   them: each value of Lo ... Hi matches, and an empty range none. */
#include <stdio.h>

enum btn { BTN_A = 0x130, BTN_B, BTN_C, BTN_D, BTN_TOOL = 0x140, BTN_TOOL_LAST = 0x14f };

static int kind(int c)
{
    switch (c) {
    case '0' ... '9':
        return 1;
    case 'a' ... 'f':
    case 'A' ... 'F':
        return 2;
    case 'z' ... 'y':                   /* empty */
        return 9;
    case -3 ... -1:
        return 3;
    case BTN_A ... BTN_D:
        return 4;
    case BTN_TOOL ... BTN_TOOL_LAST:
        return 5;
    case 'z':
        return 6;
    default:
        return 0;
    }
}

/* Ranges of 4096 values or more are tested as intervals, not expanded
   (cryptsetup's case 0 ... 0xd7ffU), signed and unsigned, both sides of
   each bound. */
static int cls(unsigned c) {
    switch (c) {
    case 0 ... 0xd7ffU: return 1;
    case 0xd800U: return 9;
    case 0xe000U ... 0xffffU: return 2;
    case 0x10000U ... 0x10ffffU: return 3;
    case 0x110000U: case 0x110001U: case 0x110003U: case 0x110005U: return 4;
    default: return 0;
    }
}
static int sgn(long v) {
    switch (v) {
    case -100000 ... -1: return -1;
    case 0: return 0;
    case 1 ... 99999: return 1;
    case 1000000000L ... 0x7fffffffffffffffL: return 5;
    }
    return 7;
}
int main(void)
{
    static const int probe[] = {'/', '0', '5', '9', ':', 'a', 'f', 'g', 'F', 'G', 'y', 'z',
                                -4, -3, -1, 0, 0x12f, 0x130, 0x133, 0x134, 0x140, 0x14f, 0x150};
    for (unsigned i = 0; i < sizeof probe / sizeof probe[0]; i++)
        printf("%d", kind(probe[i]));
    printf("\n");
    unsigned char u = 200;
    switch (u) {
    case 100 ... 255: printf("high\n"); break;
    default: printf("low\n");
    }
    unsigned t[] = {0, 5, 0xd7ff, 0xd800, 0xd801, 0xdfff, 0xe000, 0xffff, 0x10000, 0x10ffff, 0x110000, 0x110002, 0x110003, 0xffffffffu};
    for (unsigned i = 0; i < sizeof t / sizeof *t; i++) printf("%d", cls(t[i]));
    long w[] = {-100001, -100000, -5, -1, 0, 1, 99999, 100000, 999999999L, 1000000000L, 0x7fffffffffffffffL, (long)0x8000000000000000UL};
    for (unsigned i = 0; i < sizeof w / sizeof *w; i++) printf(" %d", sgn(w[i]));
    printf("\n");
    return 0;
}
