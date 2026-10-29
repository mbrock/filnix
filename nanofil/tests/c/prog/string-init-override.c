/* String literals initialize a byte array as one data chunk (static)
   or one leaf; a designator that goes back overrides only the bytes it
   covers, and a later string clears what it initializes. A braced
   list of integer constants for a byte array takes the same path. */
#include <stdio.h>
struct S { char s[8]; int k; };
static struct S a = { .s = "abcdefg", .s[2] = 'Z', .k = 3 };
static struct S b = { .s[5] = 'Q', .s = "xy" };
static char c[] = { "hello" };
static unsigned char d[6] = "\377\200a";
static struct { char t[4]; char u[4]; } e = { "abc", "def", .t[1] = '!' };
static signed char f[3] = "\377\376";
static const unsigned char g[6] = { 0x1ff, 0101, 'b', 255 };
static const signed char h[4] = { 200, 0177, 'c' };
static const union { const unsigned char data[5]; double a; } u = { { 1, 2, 3 } };
static unsigned char m[4] = { 1, 2, 3, [1] = 9 };
int main(void) {
    struct S la = { .s = "abcdefg", .s[2] = 'Z', .k = 3 };
    char lc[] = "local";
    unsigned char lg[5] = { 0x141, 66, 'z' };
    printf("%d %d %d %d %d|%d %d %d|%d %d %d|%d %d %d %d|%d %d %d %d\n", g[0], g[1], g[2], g[3], g[5],
           h[0], h[1], h[2], u.data[2], u.data[4], (int)sizeof u, m[0], m[1], m[2], m[3], lg[0], lg[1], lg[2], lg[4]);
    printf("%s %d|%s %d|%s|%d %d %d|%s %s|%d %d\n", a.s, a.k, b.s, b.s[5], c, d[0], d[1], d[5], e.t, e.u, f[0], f[1]);
    printf("%s %s %zu\n", la.s, lc, sizeof c);
    return 0;
}
