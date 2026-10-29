/* __func__ is one static array per function (C11 6.4.2.2p1): its size
   counts the name and the null, every use names the same object, and
   its address is an address constant in a block-scope static's
   initializer, as ell's L_DEBUG_SYMBOL uses it. */
#include <stdio.h>
struct desc { const char *file, *func; unsigned flags; };
static const char *probe(void)
{
    static struct desc d = { .file = "x.c", .func = __func__ };
    static const char *tail = __func__ + 2;
    return tail == d.func + 2 && d.func == __func__ ? d.func : "split";
}
int main(void)
{
    static const char *name = __FUNCTION__;
    printf("%s %s %zu %zu %d\n", probe(), name, sizeof __func__,
           sizeof __FUNCTION__, __func__ == __func__);
    return 0;
}
