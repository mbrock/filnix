// The <fenv.h> functions, which used memory-operand inline asm in user
// glibc and stopped the program when called.
#include <assert.h>
#include <fenv.h>
#include <float.h>
#include <stdio.h>

static volatile double one = 1.0, three = 3.0, zero = 0.0;
static volatile long double lone = 1.0L, lthree = 3.0L;

static double quotient(int mode) {
  assert(fesetround(mode) == 0);
  assert(fegetround() == mode);
  return one / three;
}

static long double lquotient(int mode) {
  assert(fesetround(mode) == 0);
  return lone / lthree;
}

int main(void) {
  assert(fegetround() == FE_TONEAREST);
  // SSE (double) and x87 (long double) arithmetic follow the mode.
  assert(quotient(FE_UPWARD) > quotient(FE_DOWNWARD));
  assert(quotient(FE_TOWARDZERO) == quotient(FE_DOWNWARD));
  assert(lquotient(FE_UPWARD) > lquotient(FE_DOWNWARD));
  assert(lquotient(FE_TOWARDZERO) == lquotient(FE_DOWNWARD));
  assert(fesetround(12345) != 0);
  assert(fesetround(FE_TONEAREST) == 0);

  assert(feclearexcept(FE_ALL_EXCEPT) == 0);
  assert(!fetestexcept(FE_ALL_EXCEPT));
  volatile double r = one / zero;
  (void)r;
  assert(fetestexcept(FE_DIVBYZERO));
  assert(feclearexcept(FE_DIVBYZERO) == 0);
  assert(!fetestexcept(FE_DIVBYZERO));

  // x87 exceptions are reported too.
  volatile long double lr = lone / lthree;
  (void)lr;
  assert(fetestexcept(FE_INEXACT));
  assert(feclearexcept(FE_ALL_EXCEPT) == 0);
  assert(!fetestexcept(FE_ALL_EXCEPT));

  assert(feraiseexcept(FE_OVERFLOW | FE_UNDERFLOW | FE_INEXACT) == 0);
  assert(fetestexcept(FE_ALL_EXCEPT) ==
         (FE_OVERFLOW | FE_UNDERFLOW | FE_INEXACT));

  fexcept_t flags;
  assert(fegetexceptflag(&flags, FE_OVERFLOW | FE_INVALID) == 0);
  assert(feclearexcept(FE_ALL_EXCEPT) == 0);
  assert(fesetexceptflag(&flags, FE_OVERFLOW | FE_INVALID) == 0);
  assert(fetestexcept(FE_ALL_EXCEPT) == FE_OVERFLOW);

  fenv_t env;
  assert(fesetround(FE_UPWARD) == 0);
  assert(fegetenv(&env) == 0);
  assert(fesetenv(FE_DFL_ENV) == 0);
  assert(fegetround() == FE_TONEAREST);
  assert(!fetestexcept(FE_ALL_EXCEPT));
  assert(fesetenv(&env) == 0);
  assert(fegetround() == FE_UPWARD);
  assert(fetestexcept(FE_ALL_EXCEPT) == FE_OVERFLOW);

  assert(feholdexcept(&env) == 0);
  assert(!fetestexcept(FE_ALL_EXCEPT));
  r = one / zero;
  assert(feupdateenv(&env) == 0);
  assert(fetestexcept(FE_ALL_EXCEPT) == (FE_OVERFLOW | FE_DIVBYZERO));
  assert(fegetround() == FE_UPWARD);

  femode_t mode;
  assert(fegetmode(&mode) == 0);
  assert(fesetmode(FE_DFL_MODE) == 0);
  assert(fegetround() == FE_TONEAREST);
  assert(fesetmode(&mode) == 0);
  assert(fegetround() == FE_UPWARD);

  assert(fegetexcept() == 0);
  assert(feenableexcept(FE_DIVBYZERO) == 0);
  assert(fegetexcept() == FE_DIVBYZERO);
  assert(fedisableexcept(FE_DIVBYZERO) == FE_DIVBYZERO);
  assert(fegetexcept() == 0);

  puts("ok");
  return 0;
}
