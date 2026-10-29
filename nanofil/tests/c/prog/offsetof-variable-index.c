/* offsetof with variable array indexes, as libseccomp computes
   offsetof(struct seccomp_data, args[x]); GCC and clang accept it and
   compute it at run time. */
#include <stddef.h>
#include <stdio.h>
#include <stdint.h>
struct seccomp_data { int nr; uint32_t arch; uint64_t ip; uint64_t args[6]; struct { short s[3]; } m[4]; };
#define default_arg_offset(x) (offsetof(struct seccomp_data, args[x]))
static int lo(unsigned arg, int big) { return big ? default_arg_offset(arg) + 4 : default_arg_offset(arg); }
int main(int argc, char **argv) {
  (void)argv;
  unsigned i = (unsigned)argc + 1, j = (unsigned)argc;
  printf("%d %d %zu %zu %zu\n", lo(0, 0), lo(5, 1), offsetof(struct seccomp_data, m[i].s[j]),
         offsetof(struct seccomp_data, args[2]), offsetof(struct seccomp_data, m[1].s[2]));
  return 0;
}
