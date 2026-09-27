#define _GNU_SOURCE
#include <langinfo.h>
#include <locale.h>
#include <stdio.h>
#include <stdlib.h>
#include <wchar.h>
#include <wctype.h>

int main(void) {
    const char *name = setlocale(LC_ALL, "C.UTF-8");
    if (!name) {
        fputs("C.UTF-8 is not installed\n", stderr);
        return 1;
    }
    printf("%s: %s\n", name, nl_langinfo(CODESET));

    /* U+00E9, U+20AC and U+1F600: two, three and four UTF-8 bytes. */
    wchar_t text[8];
    size_t length = mbstowcs(text, "h\xc3\xa9\xe2\x82\xac\xf0\x9f\x98\x80", 8);
    return !(length == 4 && text[1] == 0xE9 && text[2] == 0x20AC &&
             text[3] == 0x1F600 && wcwidth(text[3]) == 2 &&
             towupper(text[1]) == 0xC9);
}
