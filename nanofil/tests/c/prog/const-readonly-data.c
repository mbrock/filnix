/* A const object without pointers is in .data.rel.ro with a read-only
   capability, as filcc lays it out: a store into it through a cast
   traps (prog/const-readonly covers a relocated pointer table, which
   stays in .data). */
// trap-reason
#include <stdio.h>
static const int nums[4] = { 1, 2, 3, 4 };
const struct { int a; short b[2]; } cs = { 5, { 6, 7 } };
int main(void)
{
    printf("%d %d %d\n", nums[3], cs.a, cs.b[1]);
    fflush(stdout);
    *(int *)&nums[1] = 9;
    return 0;
}
