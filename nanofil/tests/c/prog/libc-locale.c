// cflags: -D_GNU_SOURCE -fno-builtin
// C locale makes expected values independent of installed locale data;
// this is not an entry-contract restriction. Conversion can be partial
// or invalid without a panic; it writes state even without a character.
#include <ctype.h>
#include <errno.h>
#include <langinfo.h>
#include <locale.h>
#include <stdint.h>
#include <uchar.h>
#include <wchar.h>
#include <wctype.h>
#include "libc-probe.h"
int main(void) {
    answer("locale query and refusal", setlocale(LC_ALL, "C") != 0 && strcmp(setlocale(LC_CTYPE, 0), "C") == 0 && setlocale(LC_ALL, "nanofil-no-such-locale") == 0);
    char *ctype_name = setlocale(LC_CTYPE, 0);
    char *messages_name = setlocale(LC_MESSAGES, 0);
    int stable = ctype_name && messages_name &&
        ctype_name == setlocale(LC_CTYPE, 0) && messages_name == setlocale(LC_MESSAGES, 0);
    stable = stable && setlocale(LC_ALL, "nanofil-no-such-locale") == 0 &&
        ctype_name == setlocale(LC_CTYPE, 0) && messages_name == setlocale(LC_MESSAGES, 0) &&
        strcmp(ctype_name, "C") == 0 && strcmp(messages_name, "C") == 0;
    answer("locale queries and refusal retain current borrowed names", stable);
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
    return 0;
}
