/* Aliases of objects and of variadic functions (fontconfig, gettext and
   gtk2 alias objects; glibc-style code aliases variadic functions), and
   a function alias's address seen from another unit. Each is the IR's
   alias(Name, Linkage, Target), whose getter is the target's, so clang's
   unit (lib/alias-objects.c) reads and writes the same object through
   the alias and sees one address for alias and target. */
// link: lib/alias-objects.c
#include <stdarg.h>
#include <stdio.h>

int counter = 5;
extern int counter_alias __attribute__((alias("counter")));
static int table[4] = {1, 2, 3, 4};
extern int table_alias[4] __attribute__((alias("table")));
const char *greeting = "hi";
extern const char *greeting_alias __attribute__((alias("greeting")));
int weak_obj = 7;
extern int weak_obj_alias __attribute__((weak, alias("weak_obj")));

int sum(int n, ...) {
    va_list ap;
    va_start(ap, n);
    int s = 0;
    for (int i = 0; i < n; i++) s += va_arg(ap, int);
    va_end(ap);
    return s;
}
int sum_alias(int n, ...) __attribute__((alias("sum")));
int sum_weak(int n, ...) __attribute__((weak, alias("sum")));
static int triple(int a) { return a * 3; }
int triple_alias(int) __attribute__((alias("triple")));
int target(int a) { return a + 100; }
int target_alias(int) __attribute__((alias("target")));

int from_clang(void);
int same_from_clang(int (*f)(int), int *p);

int main(void) {
    counter_alias += 1;
    table_alias[2] = 9;
    printf("%d %d %d %d %s %d\n", counter, counter_alias, table[2], table_alias[2],
           greeting_alias, weak_obj_alias);
    printf("%d %d %d %d\n", sum_alias(3, 1, 2, 3), sum_weak(2, 5, 6), triple_alias(4),
           &counter_alias == &counter);
    printf("%d\n", from_clang());
    printf("%d %d\n", same_from_clang(target, &counter), counter);
    return 0;
}
