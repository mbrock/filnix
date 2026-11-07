// cflags: -D_GNU_SOURCE -fno-builtin
// iconv changes all four cursor/length cells on partial success. Neither
// E2BIG nor EILSEQ consumes the offending character. No terminator is
// appended. Reset is not the ordinary input path.
#include <errno.h>
#include <iconv.h>
#include "libc-probe.h"
int main(void) {
    errno = 0;
    iconv_t bad = iconv_open("nanofil-no-such-encoding", "UTF-8");
    answer("unknown encoding is EINVAL", bad == (iconv_t)-1 && errno == EINVAL);
    iconv_t cd = iconv_open("UTF-8", "ISO-8859-1");
    if (cd == (iconv_t)-1) return 1;
    char src[] = {'A', (char)0xe9}, dst[5] = {'!', '!', '!', '!', '!'};
    char *in = src, *out = dst + 1;
    size_t il = 2, ol = 1;
    errno = 0;
    size_t rc = iconv(cd, &in, &il, &out, &ol);
    answer("E2BIG preserves partial conversion", rc == (size_t)-1 && errno == E2BIG && in == src + 1 && il == 1 && out == dst + 2 && ol == 0 && dst[0] == '!' && dst[1] == 'A' && dst[2] == '!');
    ol = 2;
    rc = iconv(cd, &in, &il, &out, &ol);
    answer("conversion advances cursors without NUL", rc == 0 && il == 0 && ol == 0 && in == src + 2 && out == dst + 4 && (unsigned char)dst[2] == 0xc3 && (unsigned char)dst[3] == 0xa9 && dst[4] == '!');
    answer("null input resets descriptor", iconv(cd, 0, 0, 0, 0) == 0 && iconv_close(cd) == 0);
    cd = iconv_open("ASCII", "UTF-8");
    if (cd == (iconv_t)-1) return 1;
    char invalid[] = {(char)0xff}; in = invalid; il = 1; out = dst; ol = 5;
    errno = 0;
    rc = iconv(cd, &in, &il, &out, &ol);
    answer("EILSEQ leaves offending input", rc == (size_t)-1 && errno == EILSEQ && in == invalid && il == 1 && out == dst && ol == 5);
    char partial[] = {(char)0xc3}; in = partial;
    errno = 0;
    rc = iconv(cd, &in, &il, &out, &ol);
    answer("incomplete sequence is EINVAL", rc == (size_t)-1 && errno == EINVAL && in == partial && il == 1);
    return iconv_close(cd) != 0;
}
