/* OpenSSL 3.6.0, include/internal/constant_time.h.
 * Copyright 2014-2025 The OpenSSL Project Authors. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0
 * https://github.com/openssl/openssl/blob/openssl-3.6.0/include/internal/constant_time.h
 *
 * The two bodies are unchanged. Remove static ossl_inline so nanofil
 * emits both functions and the proof follows the direct helper call.
 */
unsigned int constant_time_msb(unsigned int a)
{
    return 0 - (a >> (sizeof(a) * 8 - 1));
}

unsigned int constant_time_lt(unsigned int a, unsigned int b)
{
    return constant_time_msb(a ^ ((a ^ b) | ((a - b) ^ b)));
}

/* This control has the same result, but exposes the comparison in a branch. */
unsigned int leaky_lt(unsigned int a, unsigned int b)
{
    if (a < b)
        return ~0U;
    return 0;
}

// run: $constant_time_lt 0 0
// run: $constant_time_lt 0 4294967295
// run: $constant_time_lt 4294967295 0
// run: $constant_time_lt 2147483647 2147483648
// run: $constant_time_lt 2147483648 2147483647
// run: $constant_time_lt 4294967295 4294967295
// run: $leaky_lt 0 0
// run: $leaky_lt 0 4294967295
// run: $leaky_lt 4294967295 0
// run: $leaky_lt 2147483647 2147483648
