// error: :5: Fil-C cannot initialize this object: a pointer in its initializer is not word-aligned
/* A non-null integer pointer constant at a misaligned offset is refused
   as an address is, as filcc refuses it. */
struct __attribute__((packed)) mis { char c; int *p; };
struct mis g = { 1, (int *)8 };
