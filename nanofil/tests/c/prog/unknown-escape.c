// An unknown escape is the character itself, as clang has it (with a
// warning); \E is GNU ESC like \e. btrfs-progs prints "\t\(".
#include <stdio.h>

int main(void)
{
    const char *s = "a\(b\%c\e\E\q\{";
    for (; *s; s++)
        printf("%d ", *s);
    printf("%d %d %d %d\n", (int)sizeof "\(", (int)'\(', (int)L'\q', (int)u'\E');
    return 0;
}
