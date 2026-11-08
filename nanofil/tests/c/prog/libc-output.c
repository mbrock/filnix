// cflags: -D_GNU_SOURCE -fno-builtin
// puts is hi.c's sole libc call. I/O failure is a result, not panic;
// sprintf's count excludes its NUL, but the writable range includes it.
#include <errno.h>
#include <error.h>
#include <fcntl.h>
#include <stdio_ext.h>
#include <wchar.h>
#include <stddef.h>
#include <sys/stat.h>
#include "libc-probe.h"
// Libio.v's selected x86-64 Fil-C memory view depends on these offsets.
_Static_assert(sizeof(FILE) == 216 && _Alignof(FILE) == 8, "FILE layout");
_Static_assert(offsetof(FILE, _IO_buf_base) == 56 && offsetof(FILE, _IO_buf_end) == 64, "buffer slots");
_Static_assert(offsetof(FILE, _shortbuf) == 131 && offsetof(FILE, _lock) == 136, "embedded buffer and lock");
_Static_assert(sizeof(struct { FILE file; void *vtable; }) == 224, "FILE_plus layout");
_Static_assert(sizeof(struct { int lock; int cnt; void *owner; }) == 16, "NPTL lock layout");
_Static_assert(BUFSIZ == 8192 && sizeof(int) == 4, "capacity and errno cell");
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
    f = tmpfile();
    if (!f) return 1;
    struct stat st;
    if (fstat(fileno(f), &st)) return 1;
    size_t capacity = st.st_blksize > 0 && st.st_blksize < BUFSIZ ? st.st_blksize : BUFSIZ;
    good = fputc('Q', f) == 'Q' && __fbufsize(f) == capacity && __fpending(f) == 1;
    good = good && f->_IO_buf_end - f->_IO_buf_base == capacity && f->_IO_buf_base[0] == 'Q';
    answer("allocated stream buffer follows stat capacity", good && fclose(f) == 0);
    f = tmpfile();
    if (!f) return 1;
    good = setvbuf(f, 0, _IONBF, 0) == 0 && __fbufsize(f) == 1;
    good = good && f->_IO_buf_base == f->_shortbuf && f->_IO_buf_end == f->_shortbuf + 1;
    good = good && fputc('R', f) == 'R' && __fpending(f) == 0;
    rewind(f);
    answer("unbuffered stream uses embedded byte", good && fgetc(f) == 'R' && fclose(f) == 0);
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
