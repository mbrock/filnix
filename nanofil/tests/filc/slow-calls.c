#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

long signal_poll(void);
long signal_store(void);
int signal_catch(void);
static volatile sig_atomic_t seen, jumping;
static sigjmp_buf target;
static long **destination;

static void handler(int sig)
{
    if (sig != SIGUSR1)
        abort();
    ++seen;
    if (jumping)
        siglongjmp(target, 7);
}

void *signal_buffer(void) { return target; }
void *signal_large(void) { return destination = malloc(65536); }
void *signal_value(void)
{
    long *p = malloc(sizeof(*p));
    *p = 80;
    return p;
}

int main(void)
{
    if (signal(SIGUSR1, handler) == SIG_ERR)
        abort();
    if (signal_poll() != 97 || seen != 1)
        abort();
    zscavenger_suspend();
    int aux_callbacks = 0;
    for (int i = 0; i < 20; ++i) {
        seen = 0;
        if (signal_store() != 100 || **destination != 80)
            abort();
        /* Read before any exit-capable call: only the store's helper
           can have consumed this signal. Zero-mode aux may not exit. */
        aux_callbacks += seen != 0;
        destination = NULL;
        zgc_request_and_wait();
        zgc_request_and_wait();
    }
    if (!aux_callbacks)
        abort();
    seen = 0;
    jumping = 1;
    if (signal_catch() != 7 || seen != 1)
        abort();
    jumping = 0;
    zgc_request_and_wait();
    zgc_request_and_wait();
    seen = 0;
    if (signal_poll() != 97 || seen != 1)
        abort();
    puts("slow calls: poll, aux, abandoning jump and subsequent GC intact");
    return 0;
}
