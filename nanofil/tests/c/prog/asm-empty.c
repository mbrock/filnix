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
   called twice. */
#include <stdio.h>

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

int main(void) {
    memory_operands();
    int k = 3, junk = 0;
    __asm__ volatile("" : : "r"(k), "i"(5), "n"(sizeof(int)), "g"(bump()));
    __asm__ volatile("" : "=r"(junk));          /* unspecified: not printed */
    (void)junk;
    unsigned long a = 0x1234, b = 0x5678;
    unsigned long sel = (mask_for(1) & a) | (~mask_for(1) & b);
    printf("%u %g %d %lx %lx\n", guard(21), dguard(1.5), counter, sel,
           (mask_for(0) & a) | (~mask_for(0) & b));
    return 0;
}
