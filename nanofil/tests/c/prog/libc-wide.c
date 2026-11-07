// cflags: -D_GNU_SOURCE -fno-builtin
// stdout must be unoriented (unlike libc-output.c's byte stdout).
#include <stdio.h>
#include <wchar.h>
int main(void) {
    int count = -1;
    int rc = wprintf(L"wide:%ls:%d%n\n", L"xy", 7, &count);
    return rc != 10 || count != 9;
}
