/* Transparent unions shared by transparent-union.c (nanofil) and
   lib/transparent-union.c (clang). */
#include <stddef.h>

/* All pointers: passed as a pointer, the first member. */
typedef union {
    int *ip;
    long *lp;
    const char *cp;
} __attribute__((__transparent_union__)) PtrArg;

/* A pointer first and an integer member: an integer argument goes into
   n, and the callee's p then has no capability. The attribute is on
   the union's definition, as in GLib's G_DEFINE_BOXED_TYPE. */
typedef union __attribute__((__transparent_union__)) {
    void *p;
    long n;
} WordArg;

/* Integers: passed as an int. */
union __attribute__((__transparent_union__)) IntArg {
    int i;
    unsigned u;
};

/* Members of different sizes: clang warns and drops the transparency,
   so this is an ordinary union passed by value. */
typedef union {
    int i;
    long l;
} __attribute__((__transparent_union__)) Mixed;

long c_ptr(PtrArg a);
long c_word(WordArg w);
int c_int(union IntArg a);
long c_mixed(Mixed m);
long c_calls(void);

long n_ptr(PtrArg a);
long n_word(WordArg w);
int n_int(union IntArg a);
long n_mixed(Mixed m);
