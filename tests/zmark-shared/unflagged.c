/* Compiled WITHOUT -fzmark-shared and linked into zmark (see run.sh's callers in zmark.c).
   Code that does not know the shared flag must fail safe on a marked mapping: loads give no
   capability, pointer stores panic. */
#include <string.h>

void *unflagged_load(void **slot)
{
    return *slot;
}

void unflagged_store(void **slot, void *value)
{
    *slot = value;
}

void unflagged_copy_out(void **dst, void **src, unsigned long n)
{
    memcpy(dst, src, n * sizeof(void *));
}
