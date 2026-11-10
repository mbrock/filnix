/* Print what rx.pl reads (see pcre2_rx_terms.h) for each pattern of
   pats.h and more.h: the opcode numbering, then what pcre2_compile made
   of the pattern. */
#include "config.h"
#define PCRE2_CODE_UNIT_WIDTH 8
#include "pcre2_internal.h"
#include <stdio.h>
#include <string.h>

#include "pcre2_rx_terms.h"

#include "pats.h"

#include "more.h"

static void dump(const struct pat *p)
{
    int err;
    PCRE2_SIZE eo;
    pcre2_code *code = pcre2_compile((PCRE2_SPTR)p->re, PCRE2_ZERO_TERMINATED, p->opts, &err, &eo, NULL);
    if (!code) {
        printf("%% %s: does not compile\n", p->name);
        return;
    }
    rx_write_pattern(stdout, p->name, (const pcre2_real_code *)code);
    pcre2_code_free(code);
}

int main(void)
{
    rx_write_ops(stdout);
    for (size_t i = 0; i < sizeof pats / sizeof pats[0]; i++)
        dump(&pats[i]);
    for (size_t i = 0; i < sizeof more / sizeof more[0]; i++)
        dump(&more[i]);
}
