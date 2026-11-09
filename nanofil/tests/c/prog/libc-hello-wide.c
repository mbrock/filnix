// cflags: -D_GNU_SOURCE -fno-builtin
// Hello's exact L"%ls\n" path; physical pending counts wide characters.
#include <locale.h>
#include <stdio.h>
#include <stdio_ext.h>
#include <wchar.h>
int main(void) {
    if (!setlocale(LC_ALL, "C.UTF-8")) return 1;
    if (wprintf(L"%ls\n", L"\u00e9\u03bb") != 3) return 2;
    if (__fpending(stdout) != 3 || ferror(stdout)) return 3;
    return fclose(stdout) != 0;
}
