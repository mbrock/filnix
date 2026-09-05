#include <assert.h>
#include <string.h>
#include <openssl/aes.h>

int main(int argc, char **argv)
{
    unsigned char key[16] = {0}, input[16] = {0}, output[16];
    const unsigned char expected[16] = {
        0x66, 0xe9, 0x4b, 0xd4, 0xef, 0x8a, 0x2c, 0x3b,
        0x88, 0x4c, 0xfa, 0x59, 0xca, 0x34, 0x2b, 0x2e
    };
    AES_KEY schedule;
    assert(AES_set_encrypt_key(key, 128, &schedule) == 0);
    AES_encrypt(input, output, &schedule);
    assert(memcmp(output, expected, 16) == 0);
    if (argc > 1)
        AES_encrypt(input, output + 1024, &schedule);
    return 0;
}
