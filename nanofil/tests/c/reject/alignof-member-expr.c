// error: __alignof__ of a member
/* clang takes a member's alignment from its declaration (here 1, for
   packed), which nanofil's member types do not carry. */
struct s { char c; int x __attribute__((packed)); } v;
unsigned long f(void) { return __alignof__ (v.x); }
