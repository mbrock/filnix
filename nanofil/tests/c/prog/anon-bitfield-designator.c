/* A designator may name a bit-field of an anonymous struct, past
   unnamed bit-fields: libxkbcommon's KeycodeMatch is a union of an
   anonymous struct and two named ones, initialized as
   (KeycodeMatch){ .found = false }. */
#include <stdbool.h>
#include <stdio.h>

typedef union {
    struct {
        bool found:1;
        bool:1;
        bool is_alias:1;
        unsigned:29;
    };
    struct {
        bool found:1;
        bool low:1;
        bool is_alias:1;
        unsigned index:29;
    } key;
    unsigned raw;
} Match;

struct outer {
    int tag;
    struct {
        unsigned lo:4, :4, hi:4;
    };
};

static Match lookup(int k)
{
    if (k > 1)
        return (Match){ .key = { .found = true, .low = true, .index = k } };
    if (k == 1)
        return (Match){ .found = true, .is_alias = true };
    return (Match){ .found = false };
}

static const struct outer o = { .tag = 1, .hi = 9, .lo = 3 };

int main(void)
{
    for (int k = 0; k < 4; k++) {
        Match m = lookup(k);
        printf("%d %d %d %u %#x\n", m.found, m.is_alias, m.key.low, m.key.index, m.raw);
    }
    struct outer p = { .lo = 5, .hi = 6 };
    printf("%d %u %u %u %u\n", o.tag, o.lo, o.hi, p.lo, p.hi);
    return 0;
}
