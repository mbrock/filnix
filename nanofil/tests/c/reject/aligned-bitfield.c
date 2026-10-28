// error: alignment attributes
/* clang starts an aligned bit-field at a boundary of its alignment, even
   one its type already has (x at byte 4, sizeof 8); nanofil refuses
   alignment requests on bit-fields rather than lay them out. */
struct B { char c; int x : 3 __attribute__((aligned(4))); int y : 5; } b;
