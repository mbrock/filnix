#include <errno.h>
#include <pthread.h>
#include <stdio.h>

/* glibc probes for kernel PI futex support with FUTEX_UNLOCK_PI, which
   Linux answers with EPERM. */
int main(void) {
    pthread_mutexattr_t attr;
    pthread_mutex_t mutex;
    if (pthread_mutexattr_init(&attr) ||
        pthread_mutexattr_setprotocol(&attr, PTHREAD_PRIO_INHERIT))
        return 1;
    int err = pthread_mutex_init(&mutex, &attr);
    if (err == ENOTSUP) {
        puts("priority inheritance unsupported");
        return 0;
    }
    if (err || pthread_mutex_lock(&mutex) || pthread_mutex_unlock(&mutex) ||
        pthread_mutex_destroy(&mutex))
        return 1;
    puts("priority-inheritance mutex ok");
    return 0;
}
