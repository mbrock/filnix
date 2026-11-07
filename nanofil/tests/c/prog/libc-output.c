// cflags: -D_GNU_SOURCE -fno-builtin
// puts is hi.c's sole libc call. I/O failure is a result, not panic;
// sprintf's count excludes its NUL, but the writable range includes it.
#include <errno.h>
#include <error.h>
#include <fcntl.h>
#include <stdio_ext.h>
#include <wchar.h>
#include "libc-probe.h"
static void puts_without_nul(void) {
    char *p = malloc(16); memset(p, 'x', 16); puts(p);
}
static void sprintf_short(void) {
    char *p = malloc(16); sprintf(p, "%s", "abcdefghijklmnop");
}
static void readonly_count(void) {
    static const int count = 0;
    printf("%n", (int *)&count);
}
int main(void) {
    puts("hello");
    char b[8] = "!!!!!!!";
    int n = -1;
    int rc = sprintf(b + 1, "%s:%d%n", "xy", 7, &n);
    answer("format writes NUL and percent-n count", rc == 4 && n == 4 && memcmp(b, "!xy:7\0!", 7) == 0);
    FILE *f = tmpfile();
    if (!f) return 1;
    setvbuf(f, 0, _IOFBF, 4096);
    int good = fputs("ab", f) >= 0 && fprintf(f, "%s/%d", "Z", 31) == 4;
    good = good && __fpending(f) == 6 && !ferror(f);
    fflush(f); rewind(f);
    char readback[7] = {0};
    good = good && fread(readback, 1, 6, f) == 6 && strcmp(readback, "abZ/31") == 0;
    answer("stream output changes stream state", good && fclose(f) == 0);
    f = fopen("/dev/full", "w");
    if (!f) return 1;
    setvbuf(f, 0, _IONBF, 0);
    answer("I/O errors are results not traps", fprintf(f, "%s", "abc") < 0 && ferror(f));
    fclose(f);
    f = tmpfile();
    if (!f) return 1;
    // A fresh stream can become wide-oriented; stdout already cannot.
    answer("wide stream formatting", fwprintf(f, L"%ls:%d", L"xy", 7) == 4 && fclose(f) == 0);
    // Exercise the actual stdout APIs as well, with fixed output.
    printf("printf:%s:%d\n", "xy", 7);
    program_invocation_name = "libc-probe";
    program_invocation_short_name = "libc-probe";
    error(0, 0, "probe");
    answer("puts needs in-object NUL", libc_traps(puts_without_nul));
    answer("sprintf needs room for NUL", libc_traps(sprintf_short));
    answer("percent-n needs writable destination", libc_traps(readonly_count));
    return 0;
}
