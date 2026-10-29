// error: attribute frobnicate is not supported
/* Not even clang knows it; nanofil refuses what it does not list. */
int x __attribute__((frobnicate));
