// error: setjmp requires a direct call
#include <setjmp.h>
int main(void)
{
    int (*p)(struct __jmp_buf_tag *) = _setjmp;
    return p(0);
}
