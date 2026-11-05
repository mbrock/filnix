/* settimeofday(NULL, &tz) must reach the kernel (glibc's __settimezone made
   a raw inline-asm syscall, which stops a Fil-C program). systemd PID 1
   calls it from clock_reset_timewarp() right after switch-root. A zero
   offset never moves the clock; without CAP_SYS_TIME the kernel says EPERM. */
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/time.h>

int main(void)
{
    struct timezone tz = { 0, 0 };
    errno = 0;
    int r = settimeofday(NULL, &tz);
    printf("settimeofday(NULL, {0,0}) = %d (%s)\n", r, r ? strerror(errno) : "ok");
    if (!(r == 0 || (r == -1 && errno == EPERM)))
        return 1;

    struct timeval tv = { 0, 0 };
    errno = 0;
    r = settimeofday(&tv, &tz);
    printf("settimeofday(&tv, &tz) = %d (%s)\n", r, r ? strerror(errno) : "ok");
    return !(r == -1 && errno == EINVAL);
}
