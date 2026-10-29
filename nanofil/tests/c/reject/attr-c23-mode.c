// error: the C23 attribute [[gnu::mode]] is not supported
// Dropped, x had 4 bytes; clang gives it 8.
[[gnu::mode(DI)]] int x;
