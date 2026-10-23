#include <setjmp.h>
#include <stdfil.h>

static jmp_buf saved;

static void gone(void)
{
    if (_setjmp(saved))
        return;
}

int main(void)
{
    gone();
    zgc_request_and_wait();
    _longjmp(saved, 1); /* Both compilers must reject a returned frame. */
}
