/* Shared by ldouble.c (built by nanofil in one build) and
   lib/ldouble.c (always built by clang): long double, the x87 80-bit
   format, as a scalar, in structs and through varargs. */
struct ld1 { long double v; };
struct ld2 { long double a, b; };
struct ldp { long double v; char *p; };

long double c_scale(long double x, int n);
long double c_mix(int i, long double a, double d, struct ld1 s, int j, struct ld2 t);
struct ld1 c_ld1(long double x);
struct ld2 c_ld2(long double a, long double b);
struct ldp c_ldp(char *p, long double v);
long double c_vsum(int n, ...);
long double c_calls_back(char *buf);
long double c_generic(void);

long double n_scale(long double x, int n);
long double n_mix(int i, long double a, double d, struct ld1 s, int j, struct ld2 t);
struct ld1 n_ld1(long double x);
struct ld2 n_ld2(long double a, long double b);
struct ldp n_ldp(char *p, long double v);
long double n_vsum(int n, ...);
