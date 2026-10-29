/* GNU cast to a union type: (union U) x, with x of a member's type,
   is the union with that member initialized. mailutils casts a
   function to its sieve_op_t this way. */
#include <stdio.h>

typedef union {
    void (*instr)(int);
    long num;
    const char *str;
} op_t;

static int total;
static void add(int n) { total += n; }

static void run(op_t *prog, int n)
{
    for (int i = 0; i < n; i += 2)
        prog[i].instr((int)prog[i + 1].num);
}

int main(void)
{
    op_t prog[4];
    prog[0] = (op_t)add;
    prog[1] = (op_t)5L;
    prog[2] = (op_t)&add;
    prog[3] = (op_t)37L;
    run(prog, 4);
    const char *str = "str";
    op_t s = (op_t)str;
    printf("%d %s %ld\n", total, s.str, ((op_t)12L).num);
    return 0;
}
