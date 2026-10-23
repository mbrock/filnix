/* Calls between clang-built Fil-C code and nanofil's interop.ssa. Each
   case runs in its own process (run-c.sh), since a trap ends it, and must
   print the line in interop.expected. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Fil-C's malloc rounds sizes up to 16 bytes, so the test buffer is
   exactly 16 bytes and the overruns below start at byte 16. */

long sumbytes(char *buf, long n);
void setslot(char **slot, char *v);
char *offset(char *p, long off);
void poke(char *p, unsigned v);
long five(char *a, char *b, char *c, char *d, char *e);
long callc(char *s);

long c_len(const char *s) { return (long)strlen(s); }
char *c_mid(char *s) { return s + 2; }
long c_five(char *s) { return five(s, s + 1, s + 2, s + 3, s + 4); }

static char *heap(const char *s)
{
    char *p = calloc(16, 1);
    strcpy(p, s);
    return p;
}

#define CASE(k, name) case k: fputs(name " = ", stdout); fflush(stdout);

int main(int argc, char **argv)
{
    char *b = heap("\x01\x02\x03\x04\x05\x06");
    char *slot[1] = { 0 };
    switch (atoi(argv[1])) {
    CASE(0, "sumbytes") printf("%ld\n", sumbytes(b, 6)); break;
    CASE(1, "sumbytes past end") printf("%ld\n", sumbytes(b, 17)); break;
    /* The capability nanofil stores is the one C reads back. */
    CASE(2, "setslot") setslot(slot, b + 1); printf("%d\n", slot[0][2]); break;
    CASE(3, "setslot then overrun") setslot(slot, b); printf("%d\n", slot[0][16]); break;
    /* A pointer nanofil returns keeps its capability in C. */
    CASE(4, "offset") printf("%d\n", *offset(b, 5)); break;
    CASE(5, "offset past end") printf("%d\n", *offset(b, 100)); break;
    CASE(6, "poke heap") poke(b, 9); printf("%d\n", b[0]); break;
    CASE(7, "poke literal") poke((char *)"literal", 9); printf("unreachable\n"); break;
    CASE(8, "use after free") free(b); printf("%ld\n", sumbytes(b, 1)); break;
    CASE(9, "null zero length") printf("%ld\n", sumbytes(NULL, 0)); break;
    CASE(10, "null") printf("%ld\n", sumbytes(NULL, 1)); break;
    CASE(11, "five") printf("%ld\n", five(b, b + 1, b + 2, b + 3, b + 4)); break;
    CASE(12, "five overrun") printf("%ld\n", five(b, b + 1, b + 2, b + 3, b + 16)); break;
    CASE(13, "callc") printf("%ld\n", callc(b)); break;
    /* Through a function pointer: the getter and function object. */
    CASE(14, "indirect") {
        long (*volatile fp)(char *, long) = sumbytes;
        printf("%ld\n", fp(b, 3));
        break;
    }
    /* Wrong signature: the generic entry rejects the short argument list. */
    CASE(15, "wrong signature") {
        long (*volatile bad)(char *) = (long (*)(char *))(void *)sumbytes;
        printf("%ld\n", bad(b));
        break;
    }
    }
    return 0;
}
