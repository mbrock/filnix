// cflags: -D_GNU_SOURCE -fno-builtin
// Contracts: counts do not imply a NUL; results retain the source's
// capability, not authority to a neighbouring object. Never assume that
// strcmp/memcmp return exactly -1/+1. Bounded scans need no extra byte.
#include "libc-probe.h"
static void missing_nul(void) {
    char *p = malloc(16);
    memset(p, 'x', 16);
    volatile size_t n = strlen(p);
    (void)n;
}
static void short_destination(void) {
    char *p = malloc(16);
    memcpy(p, "abcdefghijklmnopq", 17);
}
static void freed_result(void) {
    char *p = strdup("abc");
    char *q = strchr(p, 'b');
    free(p);
    volatile char c = *q;
    (void)c;
}
static void cleared_capability(void) {
    char *p = strdup("abc");
    // Leave the address unchanged by writing back one of its own bytes.
    unsigned char byte = *(unsigned char *)&p;
    memset(&p, byte, 1);
    volatile char c = *p;
    (void)c;
}
int main(void) {
    char s[3] = {'x', 'y', 'z'}, d[5] = {'!', '!', '!', '!', '!'};
    answer("bounded scans need no NUL", strnlen(s, 3) == 3 && strncmp(s, "xyq", 2) == 0 && memchr(s, 'z', 3) == s + 2);
    char short_string[3] = {'x', (char)255, 0};
    _Alignas(16) char high_bytes[16] = {'!', (char)128, (char)255, 'z', 'a', 'b', 'c', 'd', 'e', 'f', (char)255, 'h', 'i', 'j', 'k', 'l'};
    answer("strnlen stops before a huge bound", strnlen(short_string, (size_t)-1) == 2 && strnlen(short_string + 1, (size_t)-1) == 1);
    answer("strnlen unaligned high bytes need no extra byte", strnlen(high_bytes + 1, 15) == 15 && strnlen(short_string + 1, 2) == 1);
    answer("strnlen zero count permits live one-past", strnlen(s + 3, 0) == 0 && strnlen(&"r"[2], 0) == 0);
    _Alignas(16) char terminated[16] = {'!', (char)128, (char)255, 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l', 0};
    answer("strlen includes final-byte NUL", strlen(terminated) == 15 && strlen(terminated + 1) == 14 && strlen(terminated + 2) == 13);
    answer("strlen empty still reads a live NUL", strlen(terminated + 15) == 0 && strlen("") == 0 && strlen(short_string + 1) == 1);
    answer("memchr converts int and selects first match", memchr(high_bytes + 1, 511, 15) == high_bytes + 2 && memchr(high_bytes + 1, -1, 15) == high_bytes + 2 && memchr(short_string, 0, 3) == short_string + 2);
    answer("memchr respects last byte and zero count", memchr(high_bytes + 1, 'l', 15) == high_bytes + 15 && !memchr(high_bytes + 1, 0, 15) && !memchr(high_bytes + 16, 0, 0));
    _Alignas(16) unsigned char compare_left[16] = {'!', 128, 255, 0, 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l'};
    _Alignas(16) unsigned char compare_right[16] = {'!', 127, 0, 0, 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'm'};
    answer("memcmp unsigned first difference controls sign", memcmp(compare_left + 1, compare_right + 1, 15) > 0 && memcmp(compare_right + 1, compare_left + 1, 15) < 0 && memcmp(compare_left + 2, compare_right + 2, 1) > 0);
    answer("memcmp binary zero and count boundary", memcmp(compare_left + 3, compare_right + 3, 12) == 0 && memcmp(compare_left + 3, compare_right + 3, 13) < 0 && memcmp(compare_left + 3, compare_left + 3, 13) == 0);
    answer("memcmp permits overlap and zero count", memcmp(compare_left + 1, compare_left + 2, 14) < 0 && memcmp(compare_left + 16, compare_right + 16, 0) == 0);
    char short_left[3] = {'a', 0, 'z'}, short_right[3] = {'a', 0, 'b'};
    const char *cl = (const char *)compare_left, *cr = (const char *)compare_right;
    answer("strncmp stops at shared NUL and compares terminators", strncmp(short_left, short_right, (size_t)-1) == 0 && strncmp("a", "ab", 3) < 0 && strncmp("ab", "a", 3) > 0);
    answer("strncmp unsigned order and exact count boundary", strncmp(cl + 1, cr + 1, 15) > 0 && strncmp(cr + 1, cl + 1, 15) < 0 && strncmp(cl + 4, cr + 4, 11) == 0 && strncmp(cl + 4, cr + 4, 12) < 0 && strncmp(cl + 4, cl + 4, 12) == 0);
    answer("strncmp permits overlap and zero count", strncmp(high_bytes + 1, high_bytes + 2, 14) < 0 && strncmp(high_bytes + 16, high_bytes + 16, 0) == 0);
    char *end = mempcpy(d + 1, s, 3);
    answer("copy returns end and preserves neighbours", end == d + 4 && memcmp(d, "!xyz!", 5) == 0);
    answer("memcpy and memset return destination", memcpy(d, "pq", 2) == d && memset(d + 2, '#', 2) == d + 2 && memcmp(d, "pq##!", 5) == 0);
    char *p = strdup("abaca");
    answer("string results and comparison signs", p && strlen(p) == 5 && strchr(p, 'a') == p && strrchr(p, 'a') == p + 4 && strchr(p, 0) == p + 5 && !strchr(p, 'z') && strcmp(p, "abacb") < 0 && memcmp("z", "a", 1) > 0);
    char *copy = 0;
    memcpy(&copy, &p, sizeof p);
    answer("memcpy preserves stored pointer authority", copy == p && copy[2] == 'a');
    free(p);
    answer("unbounded scan needs in-object NUL", libc_traps(missing_nul));
    answer("copy needs entire writable destination", libc_traps(short_destination));
    answer("search result dies with source", libc_traps(freed_result));
    answer("memset clears touched word authority", libc_traps(cleared_capability));
    return 0;
}
