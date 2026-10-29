// error: the C23 attribute [[gnu::constructor]] is not supported
// A C23 spelling of an attribute nanofil honors was once read and dropped:
// clang runs this constructor.
[[gnu::constructor]] static void init(void) { }
