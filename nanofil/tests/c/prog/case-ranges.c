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
    return 0;
}
