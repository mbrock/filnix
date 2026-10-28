// Source bytes in literals, as clang keeps them: a narrow string keeps
// the bytes written, valid UTF-8 or not (oniguruma's tests are EUC-JP),
// and a wide string decodes UTF-8. This file is not valid UTF-8. c_pp
// keeps u8"..." one preprocessing token, and a universal character name
// in a narrow string is UTF-8 (oniguruma's tests).
#include <stdio.h>
#include <wchar.h>
#include <uchar.h>

static void bytes(const char *s, size_t n) {
    for (size_t i = 0; i < n; i++) printf("%02x", (unsigned char)s[i]);
    printf(" %zu\n", n);
}

int main(void) {
    static const char euc[] = "����|��";
    const char *utf8 = "é世😀";
    bytes(euc, sizeof euc);
    bytes(utf8, 9);
    bytes(u8"éx", sizeof u8"éx");
    bytes("\u00e9\U0001F600\ufb00", sizeof "\u00e9\U0001F600\ufb00");
    const wchar_t *w = L"é世😀!";
    for (; *w; w++) printf("%x ", (unsigned)*w);
    const char16_t *u = u"世é";
    for (; *u; u++) printf("%x ", (unsigned)*u);
    printf("%x %x %zu\n", (unsigned)L'世', (unsigned)U'😀', sizeof U"é");
    return 0;
}
