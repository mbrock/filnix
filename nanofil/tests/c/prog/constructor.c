// link: lib/constructor.c
/* GNU constructor and destructor attributes: the functions run before
   main and after it returns, constructors in priority order (lower
   first, then those without one), as clang's Fil-C runs them, through
   the runtime (filc_defer_or_run_global_ctor). xz sets its CRC
   function pointers in a static constructor. A constructor attribute
   on a function this unit only declares registers nothing, as in clang
   (libgpg-error's header declares gpg_err_init so in every unit); the
   companion defines c_declared without it, so it runs only when
   called. */
#include <stdio.h>
#include <stdlib.h>
char trace[64];
int ntrace;
static int (*fn)(int);
static int twice(int x) { return 2 * x; }
__attribute__((constructor)) static void late(void) { trace[ntrace++] = 'L'; fn = twice; }
__attribute__((constructor(101))) void early(void) { trace[ntrace++] = 'e'; }
static void mid(void) __attribute__((constructor(200)));
static void mid(void) { trace[ntrace++] = 'm'; trace[ntrace++] = fn ? 'F' : '-'; }
__attribute__((destructor)) static void bye(void) { printf("destructor %s\n", trace); }
__attribute__((destructor(300))) static void bye2(void) { puts("destructor 300"); }
void c_declared(void) __attribute__((constructor));
void c_declared_dtor(void) __attribute__((destructor(400)));
int main(void) {
    printf("main %s %d\n", trace, fn(21));
    c_declared();
    printf("called %s\n", trace);
    return 0;
}
