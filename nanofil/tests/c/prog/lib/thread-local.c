/* clang's side of tests/c/prog/thread-local.c: thread-locals defined by
   clang and used by nanofil, and nanofil's used by clang. */
#include <stdlib.h>
#include "thread-local.h"

_Thread_local long cl_count;
_Thread_local struct node *cl_list;
_Thread_local int cl_init = 200;
_Thread_local struct pairs cl_pairs = { { 1, 2, 3, 4 }, "clang" };

/* One round on clang's side: count in both modules' thread-locals, one
   of them through a pointer nanofil passed, and push a node on each
   list. */
long clang_round(int id, int i, long *nf_count_ptr)
{
    struct node *n = malloc(sizeof *n);
    n->value = id * 100000 + i;
    n->next = cl_list;
    cl_list = n;
    struct node *m = malloc(sizeof *m);
    m->value = -(id * 100000 + i);
    m->next = nf_list;
    nf_list = m;
    cl_count++;
    (*nf_count_ptr)++;
    cl_pairs.a[i % 4] += id;
    return nf_count + cl_count;
}

/* The thread's own sums, read by clang. */
long clang_check(int id)
{
    long sum = 0, len = 0;
    for (struct node *n = cl_list; n; n = n->next) {
        sum += n->value;
        len++;
    }
    return sum + len + cl_init + nf_init + nf_name[0] + cl_pairs.s[0] + id;
}

long *clang_counter_address(void) { return &cl_count; }

int clang_static_local(void)
{
    static _Thread_local int calls = 50;
    return calls++;
}
