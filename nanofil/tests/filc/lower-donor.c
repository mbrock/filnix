#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

long lower_donor(void);

void *c_value(void)
{
    long *p = malloc(sizeof(*p));
    *p = 73;
    return p;
}

void c_collect(void)
{
    zgc_request_and_wait();
    zgc_request_and_wait();
}

int main(void)
{
    printf("lower donor = %ld\n", lower_donor());
    return 0;
}
