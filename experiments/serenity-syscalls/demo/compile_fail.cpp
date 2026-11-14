// Each CASE must fail to compile: the typed syscall macro turns these
// mistakes into errors at the call site.

#include "serenity_on_linux.h"

int f(int dynamic_number)
{
    SC_open_params op {};
    SC_readlink_params rl {};
    char buf[8];
    (void)op;
    (void)rl;
    (void)buf;
    (void)dynamic_number;
#if CASE == 1
    return syscall(SC_open, &rl); // wrong params struct
#elif CASE == 2
    return syscall(SC_write, 1, buf); // missing length argument
#elif CASE == 3
    return syscall((Function)dynamic_number, &op); // syscall number not a constant
#elif CASE == 4
    return syscall(SC_read, 0, 0x1000, 8); // integer where the kernel takes a buffer
#elif CASE == 5
    return syscall(SC_chown, &op); // syscall with no native declared here
#else
    return 0;
#endif
}
