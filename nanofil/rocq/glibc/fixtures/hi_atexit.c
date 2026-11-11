#include <stdio.h>
#include <stdio_ext.h>
#include <stdlib.h>
#include <unistd.h>

/* Save the stream's error before fclose invalidates it. As in gnulib's
   close-stream, a prior error matters only if there was pending output. */
static void close_stdout_hi(void)
{
    size_t pending = __fpending(stdout);
    int failed = ferror(stdout);
    int closed = fclose(stdout);
    if ((pending && failed) || closed != 0)
        _exit(1);
}

int main(void)
{
    if (atexit(close_stdout_hi) != 0)
        _exit(1);
    puts("hello");
    /* The proof linker starts at main, not the native CRT's caller. */
    exit(0);
}
