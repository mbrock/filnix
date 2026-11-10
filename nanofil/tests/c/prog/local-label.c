/* GNU local labels: __label__ at the start of a block declares labels
   of that block alone, as glibc's strptime_l declares do_normal in the
   statement expression of a macro it expands in many cases. Two
   expansions on one line, an inner declaration that shadows an outer
   one, &&label of a local label, and a goto from inside to a label of
   the function must each reach the right label. */
#include <stdio.h>

#define PICK(x) ({ __label__ big, done; int r_; \
    if ((x) > 10) goto big; r_ = (x); goto done; \
  big: r_ = 100 + (x); \
  done: r_; })

static int nest(int x)
{
    __label__ out;
    int r = 0;
    {
        __label__ out;
        if (x & 1) goto out;
        r += 10;
      out:
        r += 1;
    }
    if (x & 2) goto out;
    r += 1000;
  out:
    return r;
}

static int computed(int x)
{
    __label__ even, odd;
    void *to = (x & 1) ? &&odd : &&even;
    goto *to;
  even: return x * 2;
  odd: return x * 3;
}

static int escape(int x)
{
    int r = ({ __label__ skip; if (x < 0) goto fail; if (x == 0) goto skip; x; skip: x + 1; });
    return r;
  fail:
    return -1;
}

int main(void)
{
    int a = PICK(3) + PICK(30), b = PICK(12);
    printf("%d %d\n", a, b);
    printf("%d %d %d %d\n", nest(0), nest(1), nest(2), nest(3));
    printf("%d %d %d %d %d\n", computed(4), computed(5), escape(-2), escape(0), escape(7));
    return 0;
}
