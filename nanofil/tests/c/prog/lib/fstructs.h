/* Shared by fstructs.c (built by nanofil in one build) and
   lib/fstructs.c (always built by clang): structs of 16 bytes or less
   with float members, which SysV passes in SSE registers. */
struct f1 { float a; };
struct f2 { float a, b; };
struct f3 { float a, b, c; };
struct d1 { double a; };
struct d2 { double a, b; };
struct ld { long a; double b; };
struct dl { double a; long b; };
struct dp { double a; char *p; };
struct pd { char *p; double a; };
struct fi { float a; int b; };
struct df { double a; float b; };

struct f1 c_f1(float x);
struct f2 c_f2(float x);
struct f3 c_f3(float x);
struct d1 c_d1(double x);
struct d2 c_d2(double x);
struct ld c_ld(long n, double x);
struct dl c_dl(long n, double x);
struct dp c_dp(char *p, double x);
struct pd c_pd(char *p, double x);
struct fi c_fi(float x, int n);
struct df c_df(double x);
double c_take(struct f1 a, struct f2 b, struct f3 c, struct d2 e,
              struct dl g, struct dp h, struct pd i, struct fi j, struct df k);
double c_vtake(int n, ...);
double c_calls_back(char *buf);
double c_generic(char *buf);

struct f1 n_f1(float x);
struct f2 n_f2(float x);
struct f3 n_f3(float x);
struct d1 n_d1(double x);
struct d2 n_d2(double x);
struct ld n_ld(long n, double x);
struct dl n_dl(long n, double x);
struct dp n_dp(char *p, double x);
struct pd n_pd(char *p, double x);
struct fi n_fi(float x, int n);
struct df n_df(double x);
double n_take(struct f1 a, struct f2 b, struct f3 c, struct d2 e,
              struct dl g, struct dp h, struct pd i, struct fi j, struct df k);
double n_vtake(int n, ...);
