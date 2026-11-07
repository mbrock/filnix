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
