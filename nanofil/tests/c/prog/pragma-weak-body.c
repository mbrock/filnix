/* #pragma weak inside a function body applies to the file-scope name,
   as GCC and clang apply it, and as glibc's td_ta_map_lwp2thr writes
   #pragma weak ps_get_thread_area in a case: an undefined weak function
   is null, and this unit's later definition of late is weak and gives
   way to clang's strong one (lib/pragma-weak-body.c). (clang ignores a
   #pragma weak after the definition, so none comes after one here.) */
// link: lib/pragma-weak-body.c
#include <stdio.h>

extern int absent(int);
int late(void);

static int probe(int how)
{
    switch (how) {
    case 0:
#pragma weak absent
        if (&absent == NULL)
            return -1;
        return absent(how);
    default: {
#pragma weak late
        return late();
    }
    }
}

int late(void) { return 1; }

int main(void)
{
    printf("%d %d\n", probe(0), probe(1));
    return 0;
}
