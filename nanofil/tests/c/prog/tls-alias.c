/* An alias of thread-local data, as glibc's errno.c defines
   __libc_errno for errno: the alias is the target's object, so in each
   thread a write through one name is read through the other, and
   another thread sees its own instance. clang (lib/tls-alias.c)
   reaches the target through the alias's getter. (clang cannot
   compile an alias of a static thread-local, so only an exported
   target is compared.) */
// link: lib/tls-alias.c
#include <pthread.h>
#include <stdio.h>

__thread int errno2 = 5;
extern __thread int lerr __attribute__((alias("errno2")));

int clang_side(int v);

static void *work(void *arg)
{
    int *out = arg;
    out[0] = lerr;              /* this thread's fresh instance: 5 */
    lerr = 70;
    out[1] = errno2;            /* 70 */
    out[2] = clang_side(9);     /* lerr was 70; now 9 */
    out[3] = errno2;            /* 9 */
    return 0;
}

int main(void)
{
    errno2 = 1;
    lerr += 2;
    int r[4];
    pthread_t t;
    pthread_create(&t, 0, work, r);
    pthread_join(t, 0);
    printf("main %d %d\n", errno2, lerr);
    printf("thread %d %d %d %d\n", r[0], r[1], r[2], r[3]);
    printf("main after %d %d %d\n", clang_side(4), errno2, lerr);
    return 0;
}
