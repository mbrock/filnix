#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

long probe_reg(void);
long probe_buffer(void);

int main(int argc, char **argv)
{
    int buffered = atoi(argv[1]);
    long ok = buffered ? probe_buffer() : probe_reg();
    /* This also traverses the restored real parent frame. */
    zgc_request_and_wait();
    printf("%s exception = %ld\n", buffered ? "buffered" : "register", ok);
    return 0;
}
