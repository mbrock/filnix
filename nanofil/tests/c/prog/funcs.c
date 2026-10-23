// Function pointers in structs and globals, callbacks from libc, getenv
// and a static table of strings.
// args: x
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
struct op { const char *name; long (*fn)(long, long); };
static long add(long a, long b) { return a + b; }
static long sub(long a, long b) { return a - b; }
static long mul(long a, long b) { return a * b; }
static struct op ops[] = { {"add", add}, {"sub", sub}, {"mul", mul} };
static const char *words[] = { "pear", "apple", "fig", "banana" };
static int by_len(const void *a, const void *b) {
    const char *x = *(const char *const *)a, *y = *(const char *const *)b;
    return (int)strlen(x) - (int)strlen(y);
}
long fold(long (*f)(long, long), long init, int n) {
    long acc = init;
    for (int i = 1; i <= n; i++) acc = f(acc, i);
    return acc;
}
int main(int argc, char **argv) {
    for (unsigned i = 0; i < sizeof ops / sizeof ops[0]; i++)
        printf("%s: %ld %ld\n", ops[i].name, ops[i].fn(7, 3), fold(ops[i].fn, 1, 5));
    const char *ws[4];
    memcpy(ws, words, sizeof ws);
    qsort(ws, 4, sizeof ws[0], by_len);
    for (int i = 0; i < 4; i++) printf("%s%s", ws[i], i < 3 ? "," : "\n");
    char line[64];
    snprintf(line, sizeof line, "%s-%d-%c", argv[1], argc, 'z');
    puts(line);
    return (int)fold(add, 0, 10) & 0x7f;
}
