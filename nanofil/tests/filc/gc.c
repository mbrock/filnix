/* GC stress for gc.ir; run-c.sh runs it with and without
   FUGC_SCRIBBLE=1 FUGC_VERIFY=1. */
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

void *build(long n);
long sum(void *list);

static void *volatile sink;

void c_gc(long i)
{
    sink = malloc(64 + i % 64);
    if (i % 2000 == 0)
        zgc_request_and_wait();
    else if (i % 97 == 0)
        zgc_request_fresh();
}

#define CASE(k, name) case k: fputs(name " = ", stdout); fflush(stdout);

int main(int argc, char **argv)
{
    switch (atoi(argv[1])) {
    CASE(0, "list") {
        void *l = build(20000);
        zgc_request_and_wait();
        zgc_request_and_wait();
        printf("%ld\n", sum(l));
        break;
    }
    }
    return 0;
}
