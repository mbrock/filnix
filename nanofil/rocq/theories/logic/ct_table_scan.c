/* Constant-time table-and-window scan fixtures for Rocq verification.
 *
 * scan_indexed computes a public tail pointer after cancelling a secret
 * offset `skip`, then reads `tbl[i]` at a secret counter `i` that advances
 * across a 16-byte active window (also reading `tbl[16]` once `i` reaches 16).
 *
 * scan_ct performs the same comparison without secret-dependent indexing by
 * scanning all 16 entries of `tbl` on each outer iteration with a masked select.
 */

unsigned int scan_indexed(const unsigned char *buf, unsigned long len,
                          unsigned long win, unsigned long skip,
                          unsigned long start, const unsigned char *tbl)
{
    buf += skip;
    len -= skip;
    const unsigned char *p = buf + len - win - 16;
    unsigned int res = 0;
    unsigned long i = 0;
    for (unsigned long j = 0; j < win + 16; j++) {
        unsigned int c = p[j];
        unsigned int in_range = (unsigned int)((j >= start) & (j < start + 16));
        unsigned int mask = 0u - in_range;
        res |= (c ^ (unsigned int)tbl[i]) & mask;
        i += in_range;
    }
    return res;
}

unsigned int scan_ct(const unsigned char *buf, unsigned long len,
                     unsigned long win, unsigned long skip,
                     unsigned long start, const unsigned char *tbl)
{
    buf += skip;
    len -= skip;
    const unsigned char *p = buf + len - win - 16;
    unsigned int res = 0;
    unsigned long i = 0;
    for (unsigned long j = 0; j < win + 16; j++) {
        unsigned int c = p[j];
        unsigned int in_range = (unsigned int)((j >= start) & (j < start + 16));
        unsigned int mask = 0u - in_range;
        unsigned int expected = 0;
        for (unsigned long k = 0; k < 16; k++) {
            unsigned int eq_mask = 0u - (unsigned int)(k == i);
            expected |= (unsigned int)tbl[k] & eq_mask;
        }
        res |= (c ^ expected) & mask;
        i += in_range;
    }
    return res;
}
