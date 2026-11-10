/* Exit paths: atexit handlers in reverse order, a flushed stdout, and the
   status, chosen by the argument. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

static void first(void) { puts("first registered, last run"); }
static void second(void) { puts("second registered, first run"); }

int main(int argc, char **argv)
{
    atexit(first); atexit(second);
    errno = 0;
    FILE *f = fopen("/nonexistent/x", "r");
    printf("fopen %p errno %d %s\n", (void *) f, errno, strerror(errno));
    printf("buffered, no newline");
    if (argc > 1 && argv[1][0] == 'a') abort();
    if (argc > 1 && argv[1][0] == 'q') _Exit(5);
    exit(argc > 1 ? atoi(argv[1]) : 0);
}
