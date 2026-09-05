#include <assert.h>
#include <stdlib.h>

extern unsigned asm_load(const unsigned *);
extern unsigned *asm_identity(unsigned *);

int main(int argc, char **argv)
{
    unsigned *value = malloc(sizeof(*value));
    *value = 42;
    unsigned *alias = asm_identity(value);
    assert(alias == value);
    assert(asm_load(alias) == 42);
    /* Go beyond allocator rounding as well as the requested allocation. */
    if (argc > 1)
        return asm_load(alias + 1024);
    free(value);
    return 0;
}
