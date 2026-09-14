#include <cassert>
#include <unicode/ucnv.h>
#include <unicode/ucol.h>
#include <unicode/unorm2.h>
#include <unicode/ustring.h>

int main() {
    UErrorCode status = U_ZERO_ERROR;
    const UNormalizer2* nfc = unorm2_getNFCInstance(&status);
    assert(U_SUCCESS(status));
    const UChar decomposed[] = {0x0065, 0x0301};
    UChar normalized[8] = {};
    auto length = unorm2_normalize(nfc, decomposed, 2, normalized, 8, &status);
    assert(U_SUCCESS(status) && length == 1 && normalized[0] == 0x00e9);

    UConverter* converter = ucnv_open("windows-1252", &status);
    assert(U_SUCCESS(status));
    const char euro[] = {char(0x80)};
    length = ucnv_toUChars(converter, normalized, 8, euro, 1, &status);
    assert(U_SUCCESS(status) && length == 1 && normalized[0] == 0x20ac);
    ucnv_close(converter);

    UCollator* collator = ucol_open("en_US", &status);
    assert(U_SUCCESS(status));
    const UChar first[] = {'a'}, second[] = {'b'};
    assert(ucol_strcoll(collator, first, 1, second, 1) == UCOL_LESS);
    ucol_close(collator);

    const UChar face[] = {0xd83d, 0xde00};
    char utf8[8] = {};
    u_strToUTF8(utf8, 8, &length, face, 2, &status);
    assert(U_SUCCESS(status) && length == 4);
    assert(static_cast<unsigned char>(utf8[0]) == 0xf0);
}
