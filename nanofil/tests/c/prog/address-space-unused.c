/* An address_space type is refused only where it is used: Fil-C code
   has one address space, and filcc itself cannot compile an access
   through another. glibc's rseq-internal.h casts to address_space(257)
   in a static inline function that dl-support.c and its neighbours
   never call, so clang never emits it and nanofil never lowers it. */
#include <stdio.h>
struct area { unsigned cpu_id; };
extern long area_offset;
static inline void set_cpu(unsigned v)
{
    ((struct area __attribute__((address_space(257))) *)area_offset)->cpu_id = v;
}
int main(void)
{
    printf("%d\n", 257);
    return 0;
}
