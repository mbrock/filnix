/* Fil-C's pointer-as-int laundering: a pointer cast to an integer, put
   through integer arithmetic and cast back keeps the original
   pointer's capability when it is the only pointer the integer came
   from (gimso_semantics.md, Inttoptr). CPython tags pointers this way
   (_elementtree's JOIN_OBJ and JOIN_SET) and aligns them
   (_Py_ALIGN_DOWN in its string search). A cast of an integer with
   two different pointer sources, or none, has no capability:
   dereferencing it traps, last, in both builds. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define JOIN_GET(p) ((uintptr_t)(p) & 1)
#define JOIN_SET(p, flag) ((void *)((uintptr_t)(JOIN_OBJ(p)) | (flag)))
#define JOIN_OBJ(p) ((long *)((uintptr_t)(p) & ~(uintptr_t)1))
#define ALIGN_DOWN(p, a) ((void *)((uintptr_t)(p) & ~(uintptr_t)((a) - 1)))
static int calls;
static int offset(void) { return ++calls; }
struct node { void *tagged; };
int main(void)
{
    long *x = malloc(4 * sizeof *x);
    for (int i = 0; i < 4; i++) x[i] = 10 * i + 1;
    struct node n = { JOIN_SET(x, 1) };
    printf("tagged %d %ld\n", (int)JOIN_GET(n.tagged), *JOIN_OBJ(n.tagged));
    n.tagged = JOIN_SET(n.tagged, 0);
    printf("untagged %d %ld\n", (int)JOIN_GET(n.tagged), JOIN_OBJ(n.tagged)[3]);
    const char *str = "hello";
    printf("%s\n", (const char *)((uintptr_t)str ^ 1));
    short *s = malloc(64);
    for (int i = 0; i < 32; i++) s[i] = (short)(i * 3);
    char *mid = (char *)&s[7] + 1;
    short *down = ALIGN_DOWN(mid, sizeof(short));
    printf("aligned %d %d\n", *down, (int)((char *)down - (char *)s));
    long *up = (long *)(((uintptr_t)x + 15) & ~(uintptr_t)15);
    printf("rounded %d\n", up == x || up == x + 1);
    long *third = (long *)(((uintptr_t)x & ~(uintptr_t)7) + (offset() ? 2 * sizeof(long) : 0));
    printf("third %ld %d\n", *third, calls);
    unsigned char *bytes = (unsigned char *)(uintptr_t)(-(-(intptr_t)(uintptr_t)s));
    printf("negated twice %d\n", bytes[2]);
    long *back = (long *)(uintptr_t)(uint64_t)(uintptr_t)x;
    printf("round trip %ld\n", back[2]);
    /* The same pointer named twice is one source (one SSA value in
       Fil-C): allocators align down and up so. */
    short *down2 = (short *)((uintptr_t)mid - ((uintptr_t)mid & 1));
    short *up2 = (short *)((uintptr_t)mid + (-(uintptr_t)mid & 1));
    struct node *pn = &n;
    long *via = (long *)((uintptr_t)pn->tagged - ((uintptr_t)pn->tagged & 1));
    printf("named twice %d %d %ld\n", *down2, *up2, via[1]);
    fflush(stdout);
    char *two = (char *)(((uintptr_t)str & ~(uintptr_t)0xfff) | ((uintptr_t)x & 0xfff));
    printf("%c\n", *two);
    return 0;
}
