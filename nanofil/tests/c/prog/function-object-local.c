// asm-lines: ^[[:space:]]*\.quad[[:space:]]+\.?L?pizlonatedFIP
/* A function object names its fast entry by a local alias,
   .L<entry>.local, for exported and weak functions, as clang's do
   (docs/abi-findings.md, *Function objects name a local alias*): the
   global entry symbol is preemptible, so in a shared object the
   dynamic linker bound the word to the first definition of that name it
   had loaded. netcdf opens every HDF5 plugin with RTLD_GLOBAL, and each
   defines H5PLget_plugin_info; all of nanofil's answered with the first
   plugin's filter. A static function's entry is already local. */
#include <stdio.h>
int get_type(void) { return 7; }
const char *get_info(void) { return "info"; }
__attribute__((weak)) int weak_entry(int x) { return x + 1; }
static int local_entry(int x) { return x * 3; }
int (*pick(int k))(int) { return k ? weak_entry : local_entry; }
int main(void) {
    int (*t)(void) = get_type;
    const char *(*i)(void) = get_info;
    printf("%d %s %d %d\n", t(), i(), pick(1)(4), pick(0)(4));
    return 0;
}
