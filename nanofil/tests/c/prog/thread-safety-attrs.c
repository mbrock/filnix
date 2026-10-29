// TSA attributes (perl.h PERL_TSA_*) are static checks only.
#include <stdio.h>
typedef int __attribute__((capability("mutex"))) mutex_t;
static mutex_t m;
static int counter __attribute__((guarded_by(m)));
static void lock(mutex_t *p) __attribute__((acquire_capability(*p))) { (void)p; }
static void unlock(mutex_t *p) __attribute__((release_capability(*p))) { (void)p; }
static int bump(void) __attribute__((no_thread_safety_analysis)) { lock(&m); int r = ++counter; unlock(&m); return r; }
int main(void) { bump(); printf("%d\n", bump()); return 0; }
