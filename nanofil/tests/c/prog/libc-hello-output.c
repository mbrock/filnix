// cflags: -D_GNU_SOURCE -fno-builtin
// Selected Formatting/Streams contracts: caller buffer ownership,
// physical pending, promoted varargs, and close even on I/O error.
#include <errno.h>
#include <error.h>
#include <stdio_ext.h>
#include "libc-probe.h"
static void missing_string_nul(void) {
    char *p = malloc(16);
    memset(p, 'x', 16);
    fprintf(stdout, "%s", p);
}
static void closed_heap_stream(void) {
    FILE *f = tmpfile();
    if (!f) _exit(2);
    fclose(f);
    ferror(f);
}
int main(void) {
    FILE *f = tmpfile();
    char *buffer = malloc(128);
    if (!f || !buffer || setvbuf(f, buffer, _IOFBF, 128)) return 1;
    int ok = fputs("ABC", f) >= 0 && fprintf(f, "%s:%d:%u%%", "xy", -7, 4294967295U) == 17;
    ok = ok && __fpending(f) == 20 && ferror(f) == 0;
    ok = ok && !memcmp(buffer, "ABCxy:-7:4294967295%", 20) && fclose(f) == 0;
    buffer[0] = 'Z';
    answer("format read frames and caller buffer survive close", ok && buffer[0] == 'Z');
    free(buffer);
    f = fopen("/dev/full", "w");
    if (!f || setvbuf(f, 0, _IOFBF, 4096)) return 1;
    ok = fputs("abc", f) >= 0 && __fpending(f) == 3 && !ferror(f);
    errno = 0;
    int result = fclose(f);
    answer("buffered acceptance can fail at close", ok && result == EOF && errno == ENOSPC);
    f = fopen("/dev/full", "w");
    if (!f || setvbuf(f, 0, _IONBF, 0)) return 1;
    ok = fprintf(f, "%s", "abc") < 0 && ferror(f) != 0 && __fpending(f) == 0;
    result = fclose(f);
    answer("close success does not erase earlier error", ok && result == 0);
    printf("plain:%s:%d\n", "hello", 2026);
    program_invocation_name = "hello-output";
    program_invocation_short_name = "hello-output";
    error(0, ENOSPC, "%s", "write error");
    answer("diagnostic flushes stdout without accepting there",
           __fpending(stdout) == 0 && error_message_count == 1);
    answer("formatted string needs its NUL", libc_traps(missing_string_nul));
    answer("close consumes heap FILE", libc_traps(closed_heap_stream));
    return 0;
}
