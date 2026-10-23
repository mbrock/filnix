/* Keep OS signal-set manipulation outside the compiler under test. */
#include <signal.h>
#include <stdlib.h>

void mask_set(int blocked)
{
    sigset_t mask;
    if (sigemptyset(&mask) || sigaddset(&mask, SIGUSR1) ||
        sigprocmask(blocked ? SIG_BLOCK : SIG_UNBLOCK, &mask, 0))
        abort();
}

int mask_is_set(void)
{
    sigset_t mask;
    if (sigprocmask(SIG_BLOCK, 0, &mask))
        abort();
    return sigismember(&mask, SIGUSR1);
}
