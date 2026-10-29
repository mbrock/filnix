// error: :7: Fil-C cannot initialize this object: a pointer in its initializer is not word-aligned
/* The offset is the pointer's in the whole object: at 8 + 1 here. */
struct __attribute__((packed)) mis { char c; int *p; };
struct outer { long l; struct mis in; };
static int x;
struct outer ok = { 1, { 2, 0 } };
struct outer bad = { 1, { 2, &x } };
