/* GNU's sign builtins, as glibc's libm defines fabs and copysign with
   them: __builtin_fabs, __builtin_copysign and their f and l forms only
   change the sign bit, so -0, NaNs and infinities keep their other
   bits. Bits are printed, since printf of a NaN hides its sign.
   __builtin_trap stops the program, here in a child. */
#include <stdio.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>

static unsigned long dbits(double x) { unsigned long b; memcpy(&b, &x, 8); return b; }
static unsigned fbits(float x) { unsigned b; memcpy(&b, &x, 4); return b; }
static void lbits(long double x, char *out)
{
    unsigned char b[10];
    memcpy(b, &x, 10);
    for (int i = 9; i >= 0; i--) sprintf(out + 2 * (9 - i), "%02x", b[i]);
}

static double dnan(unsigned long b) { double x; memcpy(&x, &b, 8); return x; }
static float fnan(unsigned b) { float x; memcpy(&x, &b, 4); return x; }

int main(void)
{
    volatile double d[] = { -2.5, 3.0, -0.0, 0.0, -1.0 / 0.0, dnan(0xfff8000000000123ul) };
    volatile float f[] = { -2.5f, 3.0f, -0.0f, fnan(0xffc00042u) };
    volatile long double l[] = { -2.5L, 3.0L, -0.0L, -1.0L / 0.0L };
    for (int i = 0; i < 6; i++)
        printf("d %016lx %016lx %016lx\n", dbits(__builtin_fabs(d[i])),
               dbits(__builtin_copysign(d[i], -1.0)),
               dbits(__builtin_copysign(d[i], d[(i + 1) % 6])));
    for (int i = 0; i < 4; i++)
        printf("f %08x %08x %08x\n", fbits(__builtin_fabsf(f[i])),
               fbits(__builtin_copysignf(f[i], -0.0f)),
               fbits(__builtin_copysignf(2.0f, f[i])));
    for (int i = 0; i < 4; i++) {
        char a[21], b[21], c[21];
        lbits(__builtin_fabsl(l[i]), a);
        lbits(__builtin_copysignl(l[i], -7.0L), b);
        lbits(__builtin_copysignl(1.5L, l[i]), c);
        printf("l %s %s %s\n", a, b, c);
    }
    /* An integer argument converts first, as to a prototyped double. */
    printf("i %016lx %08x\n", dbits(__builtin_fabs(-3)), fbits(__builtin_copysignf(4, -1)));
    fflush(stdout);
    pid_t p = fork();
    if (p == 0) {
        close(2);
        __builtin_trap();
        _exit(0);
    }
    int st;
    waitpid(p, &st, 0);
    printf("trap %d\n", WIFSIGNALED(st) || (WIFEXITED(st) && WEXITSTATUS(st) != 0));
    return 0;
}
