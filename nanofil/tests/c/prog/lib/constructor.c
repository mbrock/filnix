/* The clang side of constructor.c: its own constructor runs in the
   same priority order as nanofil's. */
#include <stdio.h>
extern char trace[64];
extern int ntrace;
__attribute__((constructor(150))) static void c_init(void) { trace[ntrace++] = 'c'; }
__attribute__((destructor)) static void c_fini(void) { puts("clang destructor"); }
void c_declared(void) { trace[ntrace++] = 'D'; }
void c_declared_dtor(void) { puts("not registered"); }
