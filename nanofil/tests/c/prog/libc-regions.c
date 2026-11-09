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
    // The aux slot starts before the last byte, whose bits stay unchanged.
    unsigned char *last = (unsigned char *)&p + sizeof p - 1;
    unsigned char byte = *last;
    memset(last, byte, 1);
    volatile char c = *p;
    (void)c;
}
static void copied_fragment(void) {
    char *source = "abc", *destination = source;
    unsigned char *src = (unsigned char *)&source + sizeof source - 1;
    unsigned char *dst = (unsigned char *)&destination + sizeof destination - 1;
    memcpy(dst, src, 1); // unchanged address bits, but no complete pointer word
    volatile char c = *destination;
    (void)c;
}
static void copied_out_of_phase(void) {
    char *source = "abc", *destination = source;
    _Alignas(16) unsigned char bytes[16];
    memcpy(bytes + 1, &source, sizeof source);
    memcpy(&destination, bytes + 1, sizeof destination);
    volatile char c = *destination;
    (void)c;
}
static void strdup_out_of_phase(void) {
    char *saved = "retain";
    union { char *pointer; unsigned char bytes[32]; } source;
    source.pointer = saved;
    volatile unsigned char *raw = source.bytes;
    for (unsigned i = 0; i < 16; ++i) raw[i] = 'A';
    raw[16] = 0;
    char *copy = strdup((char *)source.bytes + 1);
    for (unsigned i = 0; i < sizeof saved; ++i)
        ((volatile unsigned char *)copy)[i] = ((unsigned char *)&saved)[i];
    char *restored;
    memcpy(&restored, copy, sizeof restored);
    volatile char c = restored[1];
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
    answer("strchr converts int and includes final NUL", strchr(terminated + 1, 511) == terminated + 2 && strchr(terminated, -1) == terminated + 2 && strchr(terminated, 0) == terminated + 15 && strchr(terminated + 1, 256) == terminated + 15);
    char cutoff[4] = {'a', 0, 'z', 0};
    answer("strchr stops at NUL and permits empty strings", !strchr(cutoff, 'z') && strchr(cutoff, 256) == cutoff + 1 && strchr(terminated + 15, 0) == terminated + 15 && !strchr(terminated + 15, 'l'));
    _Alignas(16) char reverse_search[16] = {'!', (char)128, (char)255, 'a', 'b', 'a', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', (char)255, 0};
    answer("strrchr selects last converted match", strrchr(reverse_search, 511) == reverse_search + 14 && strrchr(reverse_search + 1, -1) == reverse_search + 14 && strrchr(reverse_search, 'a') == reverse_search + 5);
    answer("strrchr includes final NUL but not earlier bytes", strrchr(reverse_search, 0) == reverse_search + 15 && strrchr(reverse_search + 1, 256) == reverse_search + 15 && strrchr(reverse_search + 15, 0) == reverse_search + 15 && !strrchr(reverse_search + 15, 511) && !strrchr(reverse_search + 1, '!'));
    answer("strrchr ignores bytes after first NUL", !strrchr(cutoff, 'z') && !strrchr(cutoff, '?') && strrchr(cutoff, 256) == cutoff + 1);
    answer("memchr converts int and selects first match", memchr(high_bytes + 1, 511, 15) == high_bytes + 2 && memchr(high_bytes + 1, -1, 15) == high_bytes + 2 && memchr(short_string, 0, 3) == short_string + 2);
    answer("memchr respects last byte and zero count", memchr(high_bytes + 1, 'l', 15) == high_bytes + 15 && !memchr(high_bytes + 1, 0, 15) && !memchr(high_bytes + 16, 0, 0));
    char greeting[14] = "Hello, world!";
    int early_match = 1;
    for (unsigned i = 4; i < sizeof greeting; ++i)
        early_match = early_match && memchr(greeting + i, 0, 12) == greeting + 13;
    answer("memchr stops at final-byte NUL before an oversized bound", early_match && memchr(terminated + 15, 0, (size_t)-1) == terminated + 15);
    answer("memchr crosses NUL for nonzero search and excludes byte n", memchr(cutoff, 'z', (size_t)-1) == cutoff + 2 && !memchr(short_string, 0, 2) && memchr(short_string, 0, 3) == short_string + 2);
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
    _Alignas(16) char terminated_copy[16];
    memcpy(terminated_copy, terminated, 16);
    answer("strcmp distinct equal strings reach final NUL", strcmp(terminated, terminated_copy) == 0 && strcmp(terminated + 1, terminated_copy + 1) == 0 && strcmp(terminated + 15, terminated_copy + 15) == 0);
    answer("strcmp stops at NUL and permits overlap", strcmp(short_left, short_right) == 0 && strcmp("a", "ab") < 0 && strcmp("ab", "a") > 0 && strcmp(terminated + 1, terminated + 2) < 0 && strcmp(terminated + 15, terminated + 1) < 0);
    terminated_copy[14] = 'm';
    answer("strcmp compares last nonzero byte", strcmp(terminated, terminated_copy) < 0 && strcmp(terminated_copy + 1, terminated + 1) > 0);
    terminated_copy[1] = 127;
    answer("strcmp unsigned first difference wins", strcmp(terminated + 1, terminated_copy + 1) > 0 && strcmp(terminated_copy, terminated) < 0);
    char *end = mempcpy(d + 1, s, 3);
    answer("copy returns end and preserves neighbours", end == d + 4 && memcmp(d, "!xyz!", 5) == 0);
    answer("memcpy and memset return destination", memcpy(d, "pq", 2) == d && memset(d + 2, '#', 2) == d + 2 && memcmp(d, "pq##!", 5) == 0);
    unsigned char fill[18];
    for (unsigned i = 0; i < sizeof fill; ++i) fill[i] = 17 + i;
    int fill_ok = memset(fill + 3, 511, 10) == fill + 3;
    for (unsigned i = 0; i < sizeof fill; ++i)
        fill_ok = fill_ok && fill[i] == (i >= 3 && i < 13 ? 255 : 17 + i);
    answer("memset repeats converted byte and frames neighbours", fill_ok);
    char *slots[3] = {"left", "middle", "right"};
    unsigned char *last = (unsigned char *)&slots[1] + sizeof slots[1] - 1;
    unsigned char byte = *last;
    answer("partial memset frames adjacent pointer capabilities", memset(last, byte, 1) == last && slots[0][1] == 'e' && slots[2][1] == 'i');
    slots[1] = "middle";
    answer("zero memset keeps bytes and pointer capabilities", memset(slots + 3, -1, 0) == slots + 3 && memset(&slots[1], 511, 0) == &slots[1] && slots[1][2] == 'd');
    answer("word-boundary memset does not clear next capability", memset(&slots[1], 0, sizeof slots[1]) == &slots[1] && slots[1] == 0 && slots[0][1] == 'e' && slots[2][1] == 'i');
    char *p = strdup("abaca");
    answer("string results and comparison signs", p && strlen(p) == 5 && strchr(p, 'a') == p && strrchr(p, 'a') == p + 4 && strchr(p, 0) == p + 5 && !strchr(p, 'z') && strcmp(p, "abacb") < 0 && memcmp("z", "a", 1) > 0);
    char *copy = 0;
    memcpy(&copy, &p, sizeof p);
    answer("memcpy preserves stored pointer authority", copy == p && copy[2] == 'a');
    char *moving[4] = {"ab", "cd", "ef", "gh"};
    answer("overlapping memmove snapshots pointers backward", memmove(moving + 1, moving, 3 * sizeof *moving) == moving + 1 && moving[0][1] == 'b' && moving[1][1] == 'b' && moving[2][1] == 'd' && moving[3][1] == 'f');
    answer("overlapping memmove snapshots pointers forward", memmove(moving, moving + 1, 3 * sizeof *moving) == moving && moving[0][1] == 'b' && moving[1][1] == 'd' && moving[2][1] == 'f' && moving[3][1] == 'f');
    char *end_slots[3] = {0, 0, "keep"};
    answer("mempcpy returns exact end and frames next pointer", mempcpy(end_slots, moving, 2 * sizeof *moving) == end_slots + 2 && end_slots[0][1] == 'b' && end_slots[1][1] == 'd' && end_slots[2][1] == 'e');
    answer("empty and complete self moves keep authority", memmove(moving, moving, sizeof *moving) == moving && memmove(moving + 4, moving + 4, 0) == moving + 4 && moving[0][1] == 'b');
    char dup_source[6] = {(char)128, (char)255, 0, 'z', 'q', 0};
    char *dup = strdup(dup_source), *dup_empty = strdup(dup_source + 2);
    answer("strdup fresh writable copy stops at first NUL", dup && dup != dup_source && memcmp(dup, dup_source, 3) == 0 && dup_empty && dup_empty[0] == 0);
    dup[1] = 'q';
    answer("strdup does not consume source ownership", (unsigned char)dup_source[1] == 255 && dup_source[3] == 'z');
    free(dup); free(dup_empty);
    char *saved = "retain";
    union { char *pointer; unsigned char bytes[32]; } dup_words;
    dup_words.pointer = saved;
    volatile unsigned char *raw = dup_words.bytes;
    for (unsigned i = 0; i < 16; ++i) raw[i] = 'A';
    raw[16] = 0;
    dup = strdup((char *)dup_words.bytes);
    for (unsigned i = 0; i < sizeof saved; ++i)
        ((volatile unsigned char *)dup)[i] = ((unsigned char *)&saved)[i];
    char *restored;
    memcpy(&restored, dup, sizeof restored);
    answer("strdup retains complete in-phase source capability", restored[2] == 't');
    free(dup);
    char *partial = saved;
    strcpy((char *)&partial, (const char *)&saved);
    answer("scalar strcpy retains partially overwritten destination authority", partial[2] == 't');
    union { char *pointer; unsigned char bytes[32]; } scalar_words;
    char scalar_source[32] = "ABCDEFGHIJKLMNOP";
    scalar_words.pointer = saved;
    char *scalar_return = strcpy((char *)scalar_words.bytes, scalar_source);
    int scalar_ok = scalar_return == (char *)scalar_words.bytes && memcmp(scalar_words.bytes, scalar_source, 17) == 0;
    for (unsigned i = 0; i < sizeof saved; ++i)
        ((volatile unsigned char *)scalar_words.bytes)[i] = ((unsigned char *)&saved)[i];
    answer("scalar strcpy retains old destination not source authority", scalar_ok && scalar_words.pointer[2] == 't');
    scalar_words.pointer = saved;
    scalar_return = stpcpy((char *)scalar_words.bytes, scalar_source);
    scalar_ok = scalar_return == (char *)scalar_words.bytes + 16 && memcmp(scalar_words.bytes, scalar_source, 17) == 0;
    for (unsigned i = 0; i < sizeof saved; ++i)
        ((volatile unsigned char *)scalar_words.bytes)[i] = ((unsigned char *)&saved)[i];
    answer("scalar stpcpy retains destination authority and returns NUL", scalar_ok && scalar_words.pointer[2] == 't');
    char scalar_boundary[5] = {'!', '!', '!', '!', '!'};
    answer("string copies frame neighbours and include final NUL", stpcpy(scalar_boundary + 1, "abc") == scalar_boundary + 4 && memcmp(scalar_boundary, "!abc", 5) == 0 && stpcpy(scalar_boundary + 2, "") == scalar_boundary + 2 && scalar_boundary[1] == 'a' && scalar_boundary[2] == 0 && scalar_boundary[3] == 'c');
    free(p);
    answer("unbounded scan needs in-object NUL", libc_traps(missing_nul));
    answer("copy needs entire writable destination", libc_traps(short_destination));
    answer("search result dies with source", libc_traps(freed_result));
    answer("memset clears touched word authority", libc_traps(cleared_capability));
    answer("partial pointer copy clears authority", libc_traps(copied_fragment));
    answer("out-of-phase pointer bytes do not compose authority", libc_traps(copied_out_of_phase));
    answer("strdup out-of-phase bytes do not import authority", libc_traps(strdup_out_of_phase));
    return 0;
}
