// error: underaligned pointers
/* Fil-C keeps a pointer's capability only at an 8-aligned address, so
   nanofil refuses a pointer member aligned below 8 (as packed pointers). */
typedef int *up __attribute__((aligned(1)));
struct S { char c; up p; } s;
