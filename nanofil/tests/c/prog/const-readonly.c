/* A static object whose type is const has a read-only capability, as
   filcc gives it (clang marks the global constant): reads see its
   initializer, pointers included (a relocated object stays in .data),
   and a store through a cast traps. Here the store goes into a
   relocated pointer table. A struct that only has const members is
   writable. */
// trap-reason
#include <stdio.h>
#include <string.h>
static const char *const names[] = { "zero", "one", "two" };
const struct { const char *n; int v; } tab[] = { { "x", 1 }, { "y", 2 } };
static const int nums[4] = { 1, 2, 3, 4 };
const int *pick = &nums[2];
static int writes(int which) {
    switch (which) {
    case 0: *(int *)&nums[1] = 9; break;
    case 1: *(const char **)&names[0] = "w"; break;
    case 2: ((int *)&tab[1].v)[0] = 7; break;
    case 3: memcpy((void *)nums, "abcd", 4); break;
    }
    return 0;
}
int main(int argc, char **argv) {
    (void)argv;
    printf("%s %s %d %d %d\n", names[2], tab[1].n, tab[0].v, *pick, nums[3]);
    fflush(stdout);
    struct { const int a; int b; } m = { 1, 2 }; static struct { const int a; int b; } sm = { 1, 2 }; sm.b = 5; m.b = sm.b; printf("%d\n", m.b); fflush(stdout);
    return writes(argc);
}
