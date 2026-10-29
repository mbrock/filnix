// error: :10: Fil-C cannot initialize this object: a pointer in its initializer is not word-aligned
/* Fil-C keeps a capability only at an 8-aligned address, so a static
   initializer cannot put a pointer at 1 in a packed struct; filcc
   refuses it alike ("Fil-C cannot initialize 'm': ..."). A null pointer
   there is fine (prog/packed-pointer.c has the accesses). */
struct __attribute__((packed)) mis { char c; int *p; };
static int x;
struct mis z = { 1, 0 };

struct mis m = { 1, &x };
