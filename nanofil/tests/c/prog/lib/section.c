/* clang's half of section.c: sectioned objects nanofil reads, and a
   sectioned function calling nanofil's sectioned one. */
extern int counter;
extern const int table[3];
int bump(int);
int lib_value __attribute__((section("libsec"))) = 7;
int *lib_ptr __attribute__((section("libsec"))) = &counter;
__attribute__((section(".text.lib"))) int lib_call(int k) { return bump(k) + table[0]; }
