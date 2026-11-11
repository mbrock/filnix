#include <string.h>
#include <stdio.h>
#include <stdint.h>

static void fill (unsigned char *p, size_t n, unsigned seed)
{
  for (size_t i = 0; i < n; i++)
    p[i] = (unsigned char) (seed + i * 7);
}

/* Independent oracle: compare byte by byte.  POSIX fixes the sign of a
   nonzero result to the sign of the first differing unsigned char pair.  */
static int bytes_differ (const unsigned char *a, const unsigned char *b, size_t n)
{
  for (size_t i = 0; i < n; i++)
    if (a[i] != b[i])
      return a[i] < b[i] ? -1 : 1;
  return 0;
}

static int failures = 0;

static void check_memcmp (void)
{
  unsigned char a[64], b[64];
  for (size_t len = 16; len <= 48; len += 8)
    for (size_t off1 = 0; off1 < 8; off1++)
      for (size_t off2 = 0; off2 < 8; off2++)
	{
	  int expect, got;
	  fill (a, 64, 1); fill (b, 64, 1);
	  expect = bytes_differ (a + off1, b + off2, len);
	  got = memcmp (a + off1, b + off2, len);
	  if ((expect == 0) != (got == 0) || (expect < 0) != (got < 0))
	    { printf ("memcmp wrong: len=%zu off1=%zu off2=%zu expect=%d got=%d\n",
	      len, off1, off2, expect, got); failures++; }
	  /* The same slice with the last byte changed: the result must
	     come from that byte.  */
	  fill (a, 64, 1); fill (b, 64, 1);
	  a[off1 + len - 1] ^= 0x20;
	  expect = bytes_differ (a + off1, b + off2, len);
	  got = memcmp (a + off1, b + off2, len);
	  if ((expect == 0) != (got == 0) || (expect < 0) != (got < 0))
	    { printf ("memcmp last-byte wrong: len=%zu off1=%zu off2=%zu expect=%d got=%d\n",
	      len, off1, off2, expect, got); failures++; }
	}
}

static void check_memcpy (void)
{
  unsigned char src[80], dst[80];
  static const size_t lens[] = { 16, 24, 32, 40, 63 };
  for (size_t li = 0; li < sizeof lens / sizeof lens[0]; li++)
    for (size_t soff = 0; soff < 16; soff++)
      for (size_t doff = 0; doff < 16; doff++)
	{
	  size_t len = lens[li];
	  fill (src, 80, 3);
	  memset (dst, 0, 80);
	  memcpy (dst + doff, src + soff, len);
	  if (bytes_differ (dst + doff, src + soff, len) != 0)
	    { printf ("memcpy wrong: len=%zu soff=%zu doff=%zu\n", len, soff, doff); failures++; }
	  fill (src, 80, 4);
	  memset (dst, 0xAA, 80);
	  memmove (dst + doff, src + soff, len);
	  if (bytes_differ (dst + doff, src + soff, len) != 0)
	    { printf ("memmove wrong: len=%zu soff=%zu doff=%zu\n", len, soff, doff); failures++; }
	}
}

/* wordcopy units.  The patched signatures pass block pointers as op_t *;
   calling them with pointer arguments against the unpatched long int
   parameters is exactly what the real callers do, so the unpatched unit
   traps the same way.  Contracts, from wordcopy.c: the _fwd_ units copy
   LEN op_t words starting at SRCP/DSTP; the _bwd_ units copy the LEN
   words finishing right before SRCP/DSTP.  The _dest_aligned units
   require DSTP aligned and SRCP not aligned; the plain units require
   both aligned.  */

typedef unsigned long int op_t;
#define OPSIZ (sizeof (op_t))

void _wordcopy_fwd_aligned (op_t *, const op_t *, size_t);
void _wordcopy_fwd_dest_aligned (op_t *, const op_t *, size_t);
void _wordcopy_bwd_aligned (op_t *, const op_t *, size_t);
void _wordcopy_bwd_dest_aligned (op_t *, const op_t *, size_t);

static void check_wordcopy (void)
{
  enum { WORDS = 20 };		/* headroom: units read one word past */
  static const size_t lens[] = { 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 17 };
  unsigned char sbuf[(WORDS + 4) * OPSIZ], dbuf[(WORDS + 4) * OPSIZ];
  unsigned char snap[(WORDS + 4) * OPSIZ];
  for (size_t li = 0; li < sizeof lens / sizeof lens[0]; li++)
    for (size_t shift = 0; shift < 8; shift += 2)
      {
	size_t len = lens[li];
	size_t bytes = len * OPSIZ;
	size_t head = 2 * OPSIZ;	/* rounds down into this */
	/* off is deliberately not op-aligned: the _dest_aligned units
	   require an unaligned source (they merge across word boundaries,
	   and the shift is undefined at alignment 0).  */
	size_t off = head + 3 + shift;

	/* fwd_aligned: both aligned.  */
	fill (sbuf, sizeof sbuf, 5); memset (dbuf, 0x77, sizeof dbuf);
	memcpy (snap, sbuf + head, bytes);
	_wordcopy_fwd_aligned ((op_t *) (dbuf + head), (const op_t *) (sbuf + head), len);
	if (bytes_differ (dbuf + head, snap, bytes) != 0
	    || dbuf[head - 1] != 0x77 || dbuf[head + bytes] != 0x77)
	  { printf ("fwd_aligned wrong: len=%zu\n", len); failures++; }

	/* fwd_dest_aligned: dst aligned, src not.  */
	fill (sbuf, sizeof sbuf, 6); memset (dbuf, 0x77, sizeof dbuf);
	memcpy (snap, sbuf + head + off, bytes);
	_wordcopy_fwd_dest_aligned ((op_t *) (dbuf + head), (const op_t *) (sbuf + head + off), len);
	if (bytes_differ (dbuf + head, snap, bytes) != 0
	    || dbuf[head - 1] != 0x77 || dbuf[head + bytes] != 0x77)
	  { printf ("fwd_dest_aligned wrong: len=%zu shift=%zu\n", len, shift); failures++; }

	/* bwd_aligned: block finishes right before the end pointers.  */
	fill (sbuf, sizeof sbuf, 7); memset (dbuf, 0x77, sizeof dbuf);
	memcpy (snap, sbuf + head, bytes);
	_wordcopy_bwd_aligned ((op_t *) (dbuf + head + bytes), (const op_t *) (sbuf + head + bytes), len);
	if (bytes_differ (dbuf + head, snap, bytes) != 0
	    || dbuf[head - 1] != 0x77 || dbuf[head + bytes] != 0x77)
	  { printf ("bwd_aligned wrong: len=%zu\n", len); failures++; }

	/* bwd_dest_aligned: dst end aligned, src end not.  */
	fill (sbuf, sizeof sbuf, 8); memset (dbuf, 0x77, sizeof dbuf);
	memcpy (snap, sbuf + head + off, bytes);
	_wordcopy_bwd_dest_aligned ((op_t *) (dbuf + head + bytes), (const op_t *) (sbuf + head + off + bytes), len);
	if (bytes_differ (dbuf + head, snap, bytes) != 0
	    || dbuf[head - 1] != 0x77 || dbuf[head + bytes] != 0x77)
	  { printf ("bwd_dest_aligned wrong: len=%zu shift=%zu\n", len, shift); failures++; }
      }
}

int main (void)
{
  check_memcmp ();
  check_memcpy ();
  check_wordcopy ();
  if (failures) { printf ("%d failures\n", failures); return 1; }
  printf ("all checks passed\n");
  return 0;
}
