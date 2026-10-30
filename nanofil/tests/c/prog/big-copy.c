/* A struct of more than 40 bytes is copied by the runtime, as filcc
   copies it (FilPizlonator's InlineMemmoveDstSizeLimit), not a word at
   a time: by assignment, initialization, argument, return and compound
   literal. Each pointer keeps its capability. A partial overlap copies
   as memmove does, and a place in a packed struct may be misaligned
   (a word-at-a-time copy would trap on its pointer load). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

struct big { int *p; long n[5]; const char *s; };   /* 56 bytes */
struct flat { long w[6]; };                          /* 48 bytes */
struct __attribute__((packed)) outer { char c; struct big in; };

static int x = 42, y = 7;

static struct big make(int *p, long k) {
    struct big b = { p, { k, k + 1, k + 2, k + 3, k + 4 }, "made" };
    return b;
}

static long sum(struct big b) {
    long t = *b.p;
    for (int i = 0; i < 5; i++) t += b.n[i];
    return t + (long)strlen(b.s);
}

static void show(const char *what, struct big b) {
    printf("%s: %d %ld %ld %s\n", what, *b.p, b.n[0], b.n[4], b.s);
}

int main(void) {
    struct big a = make(&x, 10);
    show("return", a);
    struct big b = a;
    show("init", b);
    struct big *h = malloc(sizeof *h);
    *h = b;
    show("heap", *h);
    printf("arg: %ld\n", sum(*h));
    b = (struct big){ &y, { 1, 2, 3, 4, 5 }, "literal" };
    show("literal", b);
    *h = *h;
    show("self", *h);

    /* Partial overlap: memmove's result, not a smear. */
    struct flat f[2] = { { { 1, 2, 3, 4, 5, 6 } } };
    struct flat *src = &f[0], *dst = (struct flat *)&f[0].w[1];
    *dst = *src;
    for (int i = 0; i < 7; i++) printf("%ld ", f[0].w[i]);
    printf("\n");

    /* A place in a packed struct: at raw + 8 the pointers keep their
       capabilities; at raw + 137 the copy keeps the integers. */
    char *raw = calloc(256, 1);
    struct outer *o = (struct outer *)(raw + 7);
    o->in = a;
    struct big c = o->in;
    printf("packed: %ld %ld %s\n", c.n[0], c.n[4], c.s);
    struct outer *o2 = (struct outer *)(raw + 136);
    o2->in = a;
    c = o2->in;
    printf("misaligned: %ld %ld\n", c.n[0], c.n[4]);
    return 0;
}
