struct ptrs { const char *s; int *p; };
struct member { char c; int v __attribute__((aligned(32))); };
typedef struct { unsigned char b[64]; } line64 __attribute__((aligned(64)));
int clang_misaligned(const void *p, unsigned n);
int clang_local(int (*check)(const void *, unsigned));
extern int c64 __attribute__((aligned(64)));
extern struct ptrs cps __attribute__((aligned(64)));
