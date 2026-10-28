// error: an atomic read-modify-write of x, a member of a packed struct or union, may be misaligned; clang calls libatomic for it, which nanofil does not have
struct __attribute__((packed)) s { char c; int x; } ps;
int add(void) { return __atomic_fetch_add(&ps.x, 1, __ATOMIC_SEQ_CST); }
