// cflags: -O2 -D_FORTIFY_SOURCE=2
// glibc's _FORTIFY_SOURCE headers, which gnulib's config.h turns on
// when optimizing (GNU sed): __builtin_object_size and the
// __builtin___*_chk calls their inline wrappers make, and clang's
// overloads of open by arity.
#include <fcntl.h>
#include <unistd.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

static int fmt(char *buf, size_t n, const char *f, ...) {
    va_list ap;
    va_start(ap, f);
    int r = vsnprintf(buf, n, f, ap);
    va_end(ap);
    return r;
}

// Out of line, so neither compiler knows what p points into.
__attribute__((noinline)) static size_t sizes(char *p) {
    return __builtin_object_size(p, 0) + __builtin_dynamic_object_size(p, 3);
}

int main(void) {
    char a[32], b[32];
    memset(a, 'x', sizeof a);
    strcpy(a, "fortified");
    memcpy(b, a, strlen(a) + 1);
    strcat(b, "!");
    __builtin___memcpy_chk(b + 1, "OR", 2, __builtin_object_size(b + 1, 0));
    __builtin___strcat_chk(b, "?", __builtin_object_size(b, 1));
    int r = sprintf(a + 4, "%d-%s", 42, b);
    printf("%s %d %d\n", a, r, fmt(b, 6, "%s/%d", "abcdef", 7));
    printf("%s %zu\n", b, sizes(b + r % 3));
    char *p = b;
    printf("%zu %s\n", __builtin_object_size(p++, 0) + 1, p);
    int fd = open("f.txt", O_CREAT | O_WRONLY | O_TRUNC, 0600);
    printf("%zd ", write(fd, "hello\n", 6));
    close(fd);
    fd = open("f.txt", O_RDONLY);
    printf("%zd %s", read(fd, a, sizeof a - 1), (a[6] = 0, a));
    printf("%d\n", close(fd));
    return 0;
}
