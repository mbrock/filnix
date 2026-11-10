/* An asm whose template is blank (spaces, tabs or newlines) emits no
   instruction; filcc passes it through when no operand is a pointer.
   libgcrypt's CT_DEOPTIMIZE_VAR (asm volatile("\n" : "+r"(var) ::
   "memory")) and xxhash's XXH_COMPILER_GUARD (__asm__("" : "+r"(v)))
   hide a value from the optimizer; "=r" writes an unspecified value;
   "i" and "r" inputs are only read. Before, nanofil refused all of
   these but the operand-less barrier. Memory-class operands ("=m",
   "+m", "=mr", "g", input "m") of any complete type mean nothing either
   (elfutils' barriers), and "+r" gives a pointer back with its
   capability; each operand's lvalue is still evaluated, so pick() is
   called twice. An "=r" output with an input of its type tied to it
   ("0") receives the input's value: ell's DO_NOT_OPTIMIZE(var),
   asm("" : "=r"(var) : "0"(var)). A pointer "r" input is evaluated and
   nothing else, as filcc passes it: libgcrypt's wipememory barrier,
   asm volatile("\n" :: "r"(ptr) : "memory"), after a memset. "x" (SSE)
   and "t" and "f" (x87) operands of floating type are registers like
   "r": glibc's x86 math_opt_barrier and math_force_eval, whose branch
   that sizeof rules out names the other constraint. */
#include <stdio.h>
#include <string.h>

struct S { int a; long b; };
static int picks;
static struct S *pick(struct S *s) { picks++; return s; }

static void memory_operands(void) {
    struct S s = {1, 2};
    int x = 5, arr[3] = {7, 8, 9};
    char *p = "hi";
    asm volatile("" : "=m"(*pick(&s)));
    asm volatile("" : "=mr"(x));
    asm volatile("" : "+m"(arr));
    asm volatile("" : "+g"(x), "=g"(s) : "m"(arr[1]), "g"(p), "m"(*pick(&s)), "g"(s));
    asm("" : "+r"(p));
    printf("%d %ld %d %d %d %s %d\n", s.a, s.b, x, arr[0], arr[2], p, picks);
}

static unsigned long mask_for(unsigned long op) {
    unsigned long mask = -op;
    asm volatile ("\n" : "+r" (mask) :: "memory");
    return mask;
}

static unsigned guard(unsigned v) { __asm__("" : "+r"(v)); return v * 2; }
static double dguard(double d) { __asm__ __volatile__("\t" : "+g"(d) :: "memory", "cc"); return d + 1; }

static int counter;
static int bump(void) { return ++counter; }

#define DO_NOT_OPTIMIZE(var) __asm__ ("" : "=r" (var) : "0" (var))
static void tied_inputs(void) {
    unsigned diff = 0, out = 7;
    unsigned char b = 200;
    double d = 1.5;
    long a[3] = {1, 2, 3};
    int i = 0;
    for (int k = 0; k < 4; k++) { diff |= (unsigned)k << k; DO_NOT_OPTIMIZE(diff); }
    DO_NOT_OPTIMIZE(b);
    DO_NOT_OPTIMIZE(d);
    __asm__ ("" : "=r" (out) : "0" ((unsigned)bump() + 40));
    __asm__ ("" : "=r" (a[i++]) : "0" (a[2]));
    printf("%u %u %g %u %ld %ld %d\n", diff, b, d, out, a[0], a[1], i);
}

#define opt_barrier(x) ({ __typeof (x) __x; \
    if (sizeof (x) <= sizeof (double)) __asm ("" : "=x" (__x) : "0" (x)); \
    else __asm ("" : "=t" (__x) : "0" (x)); __x; })
#define force_eval(x) do { if (sizeof (x) <= sizeof (double)) \
    __asm __volatile ("" : : "x" (x)); else __asm __volatile ("" : : "f" (x)); } while (0)
static void float_barriers(void) {
    float f = opt_barrier(2.5f);
    double d = opt_barrier(-0.25);
    long double l = opt_barrier(3.0L);
    force_eval(f * 2);
    force_eval(d);
    force_eval(l + 1);
    double y = 1.5;
    __asm__ ("" : "+x" (y));
    long double z = 4.0L;
    __asm__ ("" : "+t" (z));
    printf("%g %g %Lg %g %Lg\n", f, d, l, y, z);
}

int main(void) {
    float_barriers();
    memory_operands();
    tied_inputs();
    int k = 3, junk = 0;
    __asm__ volatile("" : : "r"(k), "i"(5), "n"(sizeof(int)), "g"(bump()));
    __asm__ volatile("" : "=r"(junk));          /* unspecified: not printed */
    (void)junk;
    static char secret[8] = "secret";
    memset(secret, 0, sizeof secret);
    asm volatile("\n" :: "r"(secret) : "memory");
    asm volatile("" :: "r"((char *)pick(0)), "r"(&k));
    printf("%d %d\n", secret[0], picks);
    unsigned long a = 0x1234, b = 0x5678;
    unsigned long sel = (mask_for(1) & a) | (~mask_for(1) & b);
    printf("%u %g %d %lx %lx\n", guard(21), dguard(1.5), counter, sel,
           (mask_for(0) & a) | (~mask_for(0) & b));
    return 0;
}
