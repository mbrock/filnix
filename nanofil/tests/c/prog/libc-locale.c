// cflags: -D_GNU_SOURCE -fno-builtin
// C locale makes expected values independent of installed locale data;
// this is not an entry-contract restriction. Conversion can be partial
// or invalid without a panic; it writes state even without a character.
#include <ctype.h>
#include <errno.h>
#include <langinfo.h>
#include <locale.h>
#include <stdint.h>
#include <stdfil.h>
#include <uchar.h>
#include <wchar.h>
#include <wctype.h>
#include "libc-probe.h"

// Test the actual capability base, including through an unaligned alias.
// The selected ABI has categories 0..12, with LC_ALL at 6.
static int locale_name_bases(void) {
    for (int category = 0; category <= 12; ++category) {
        char *name = setlocale(category, 0);
        if (!name || !*name) return 0;
        void *base = zgetlower(name);
        if (!base || (uintptr_t)base % 8 || zgetlower(name + 1) != base) return 0;
    }
    return 1;
}

// A positive conversion cannot consume the string's terminating byte.
// These checks use the input bytes and the ABI's bounds, not a decoder.
static int conversion_result(const char *s, size_t n, size_t r, wchar_t wc) {
    if (r == (size_t)-1) return errno == EILSEQ;
    if (r == (size_t)-2) return n < 16 && memchr(s, 0, n) == 0;
    if (r == 0) return wc == 0 && memchr(s, 0, n) != 0;
    if (r > n) return 0;
    for (size_t i = 0; i < r; ++i)
        if (s[i] == 0) return 0;
    return 1;
}

// The selected C converter is stateless, including its EILSEQ path.
// An initial count may have nonzero residual bytes. Do not reset after
// an error: gnulib's byte fallback reuses this exact state next time.
static int c_conversion_reuse(void) {
    if (!setlocale(LC_ALL, "C") || sizeof(mbstate_t) != 8) return 0;
    for (unsigned lead = 0; lead < 256; ++lead) {
        mbstate_t state;
        unsigned char initial[8] = {0, 0, 0, 0, 83, 167, 254, 19};
        memcpy(&state, initial, sizeof state);
        if (!mbsinit(&state)) return 0;
        char byte = (char)lead;
        wchar_t wc = 937;
        errno = 0;
        size_t r = mbrtowc(&wc, &byte, 1, &state);
        if (lead < 128) {
            if (r != (lead != 0) || wc != (wchar_t)lead) return 0;
        } else {
            if (r != (size_t)-1 || errno != EILSEQ || wc != 937 ||
                memcmp(&state, initial, sizeof state) != 0) return 0;
        }
        if (!mbsinit(&state) || mbrtowc(&wc, "Q", 1, &state) != 1 || wc != L'Q' ||
            !mbsinit(&state) || mbrtowc(&wc, "", 1, &state) != 0 || wc != 0 ||
            !mbsinit(&state)) return 0;
    }
    return 1;
}

static int conversion_boundaries(const char *locale, int utf8) {
    if (!setlocale(LC_ALL, locale) || sizeof(wchar_t) != 4 || sizeof(mbstate_t) != 8)
        return 0;
    int good = locale_name_bases(), saw_incomplete = 0;
    for (unsigned lead = 0; lead < 256; ++lead) {
        for (size_t n = 1; n <= 16; ++n) {
            char bytes[16];
            memset(bytes, 0x80, sizeof bytes);
            bytes[0] = (char)lead;
            mbstate_t state = {0};
            wchar_t wc = 99;
            errno = 0;
            size_t r = mbrtowc(&wc, bytes, n, &state);
            if (r == (size_t)-2) saw_incomplete = 1;
            good = conversion_result(bytes, n, r, wc) && good;
            if (r != (size_t)-1 && r != (size_t)-2) good = mbsinit(&state) && good;
            bytes[n - 1] = 0;
            memset(&state, 0, sizeof state);
            wc = 99;
            errno = 0;
            r = mbrtowc(&wc, bytes, n, &state);
            good = r != (size_t)-2 && conversion_result(bytes, n, r, wc) && good;
            if (r != (size_t)-1) good = mbsinit(&state) && good;
        }
    }
    if (utf8) {
        const char *samples[4] = {"A", "\xc2\xa2", "\xe2\x82\xac", "\xf0\x9f\x92\xa9"};
        const wchar_t expected[4] = {65, 162, 8364, 128169};
        for (unsigned i = 0; i < 4; ++i) {
            mbstate_t state = {0};
            wchar_t wc = 99;
            size_t n = strlen(samples[i]);
            size_t r = mbrtowc(&wc, samples[i], n + 1, &state);
            good = r == n && wc == expected[i] && mbsinit(&state) &&
                conversion_result(samples[i], n + 1, r, wc) && good;
        }
        for (size_t split = 1; split <= 3; ++split) {
            const char *character = samples[3];
            mbstate_t state = {0};
            wchar_t wc = 99;
            size_t r = mbrtowc(&wc, character, split, &state);
            good = r == (size_t)-2 && good;
            r = mbrtowc(&wc, character + split, 5 - split, &state);
            good = r == 4 - split && wc == expected[3] && mbsinit(&state) &&
                conversion_result(character + split, 5 - split, r, wc) && good;
            memset(&state, 0, sizeof state);
            good = mbrtowc(&wc, character, split, &state) == (size_t)-2 && good;
            errno = 0;
            r = mbrtowc(&wc, "", 1, &state);
            good = r == (size_t)-1 && conversion_result("", 1, r, wc) && good;
        }
        good = saw_incomplete && good;
    }
    return good;
}

int main(void) {
    int *error_cell = __errno_location();
    *error_cell = EILSEQ;
    answer("errno location is a writable aligned int", sizeof *error_cell == 4 &&
        (uintptr_t)error_cell % 4 == 0 && errno == EILSEQ);
    answer("locale query and refusal", setlocale(LC_ALL, "C") != 0 && strcmp(setlocale(LC_CTYPE, 0), "C") == 0 && setlocale(LC_ALL, "nanofil-no-such-locale") == 0);
    char *ctype_name = setlocale(LC_CTYPE, 0);
    char *messages_name = setlocale(LC_MESSAGES, 0);
    int stable = ctype_name && messages_name &&
        ctype_name == setlocale(LC_CTYPE, 0) && messages_name == setlocale(LC_MESSAGES, 0);
    stable = stable && setlocale(LC_ALL, "nanofil-no-such-locale") == 0 &&
        ctype_name == setlocale(LC_CTYPE, 0) && messages_name == setlocale(LC_MESSAGES, 0) &&
        strcmp(ctype_name, "C") == 0 && strcmp(messages_name, "C") == 0;
    answer("locale queries and refusal retain current borrowed names", stable);
    answer("C locale names and interior aliases have aligned capability bases", locale_name_bases());
    char *separate = malloc(6);
    char *canonical = 0;
    int canonical_ok = 0;
    if (separate) {
        memcpy(separate, "POSIX", 6);
        canonical = setlocale(LC_ALL, separate);
        canonical_ok = canonical && canonical != separate;
        free(separate);
    }
    answer("POSIX returns an independently readable canonical C name", canonical_ok && strcmp(canonical, "C") == 0);
    answer("empty locale input selects the represented environment", setenv("LC_ALL", "C", 1) == 0 &&
        setlocale(LC_ALL, "") != 0 && strcmp(setlocale(LC_CTYPE, 0), "C") == 0);
    char *borrowed = setlocale(LC_ALL, 0);
    char *selected = borrowed ? setlocale(LC_ALL, borrowed) : 0;
    answer("setter input may be a borrowed locale name", selected && strcmp(selected, "C") == 0);
    answer("langinfo returns readable string", strlen(nl_langinfo(CODESET)) > 0);
    const unsigned short *table = *__ctype_b_loc();
    volatile unsigned short low = table[-128], high = table[255];
    answer("ctype table includes negative indices", (table['A'] & _ISalpha) && !(table['!'] & _ISalpha) && table[-1] == 0);
    (void)low; (void)high;
    answer("wide character domains", iswalnum(L'A') && !iswalnum(L'!') && iswprint(L'!') && iswspace(L' ') && iswcntrl(L'\n') && !iswalnum(WEOF) && wcwidth(L'A') == 1 && wcwidth(L'\n') == -1 && MB_CUR_MAX == 1);
    mbstate_t state = {0};
    wchar_t wc = 99;
    char32_t c32 = 99;
    int good = mbsinit(0) && mbsinit(&state);
    good = good && mbrtowc(&wc, "Q", 1, &state) == 1 && wc == L'Q';
    good = good && mbrtoc32(&c32, "R", 1, &state) == 1 && c32 == U'R';
    good = good && mbrtowc(&wc, "", 1, &state) == 0 && wc == 0;
    answer("conversion writes output and state", good && mbsinit(&state));
    wc = 99;
    answer("empty input is incomplete not NUL", mbrtowc(&wc, "", 0, &state) == (size_t)-2 && wc == 99);
    errno = 0;
    answer("invalid byte is EILSEQ not panic", mbrtowc(&wc, "\xff", 1, &state) == (size_t)-1 && errno == EILSEQ);
    memset(&state, 0, sizeof state);
    answer("null conversion input resets", mbrtowc(0, 0, 0, &state) == 0 && mbrtoc32(0, 0, 0, &state) == 0 && mbsinit(&state));
    answer("C conversion preserves residual state on EILSEQ and reuses it without reset", c_conversion_reuse());
    answer("C conversion excludes incomplete at NUL or 16 bytes and positive NUL consumption", conversion_boundaries("C", 0));
    answer("UTF-8 conversion excludes incomplete at NUL or 16 bytes and positive NUL consumption", conversion_boundaries("C.UTF-8", 1));
    answer("UTF-8 locale names retain aligned capability bases after conversion", locale_name_bases());
    return 0;
}
