// link: lib/common-symbols.c
/* GCC's common attribute (redis redismodule.h's function pointers): a
   tentative definition with it is a common symbol, which filcc emits
   weak, so the same name tentatively defined in both objects is one
   object, and a strong definition in the other object replaces it. An
   initializer, a later tentative definition that the attribute does not
   reach, or static or thread-local storage keeps the definition strong
   or local, as in clang. */
#include <stdio.h>
#include "lib/common-symbols.h"
int shared __attribute__((common));
int (*hook)(int) __attribute__((__common__));
extern int later __attribute__((common));
int later;
long overridden __attribute__((common));
int initialized __attribute__((common)) = 3;
int plain;
extern int plain __attribute__((common));
static int local __attribute__((common));
__thread int per_thread __attribute__((common));
void ignored(void) __attribute__((common));
void ignored(void) { local++; per_thread += 2; }
static int twice(int x) { return 2 * x; }
int main(void) {
    shared = 7; hook = twice; later = 4;
    companion_set();
    ignored();
    printf("%d %d %d %ld %d %d %d %d\n", shared, hook(5), later, overridden,
           initialized, plain, local, per_thread);
    printf("%d\n", companion_same(&shared, &later, &overridden));
    return 0;
}
