/* Uses libraries from /opt/fil/lib and glibc's character sets and locales,
   whose compiled-in paths point into /opt/fil. */
#include <iconv.h>
#include <locale.h>
#include <openssl/sha.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <zlib.h>

int main(void) {
    const char *text = "memory safety out";

    unsigned char packed[64], unpacked[64];
    uLongf plen = sizeof packed, ulen = sizeof unpacked;
    if (compress(packed, &plen, (const Bytef *)text, strlen(text)) != Z_OK ||
        uncompress(unpacked, &ulen, packed, plen) != Z_OK ||
        ulen != strlen(text) || memcmp(unpacked, text, ulen) != 0) {
        puts("zlib round trip failed");
        return 1;
    }

    unsigned char digest[SHA256_DIGEST_LENGTH];
    SHA256((const unsigned char *)text, strlen(text), digest);
    printf("sha256 ");
    for (int i = 0; i < 4; i++)
        printf("%02x", digest[i]);
    printf("\n");

    /* Needs lib/gconv. */
    iconv_t cd = iconv_open("ISO-8859-1", "UTF-8");
    if (cd == (iconv_t)-1) {
        perror("iconv_open");
        return 1;
    }
    char in[] = "caf\xc3\xa9", out[8] = {0};
    char *ip = in, *op = out;
    size_t il = strlen(in), ol = sizeof out - 1;
    if (iconv(cd, &ip, &il, &op, &ol) == (size_t)-1 || strcmp(out, "caf\xe9") != 0) {
        perror("iconv");
        return 1;
    }
    iconv_close(cd);

    /* Needs lib/locale/C.utf8. */
    if (!setlocale(LC_ALL, "C.UTF-8")) {
        puts("setlocale C.UTF-8 failed");
        return 1;
    }
    if (mbstowcs(NULL, in, 0) != 4) {
        puts("mbstowcs failed");
        return 1;
    }
    puts("libs ok");
    return 0;
}
