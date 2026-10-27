/* Shared by byval.c (built by nanofil in one build) and lib/byval.c
   (always built by clang). These structs are larger than 16 bytes, so
   both compilers pass them byval: generic convention only. */
struct trio { long a; char *p; long c; };
struct text { char x[17]; };
struct mix { int i, j, k; char *p; float v; };
struct wide { char *p[6]; long n[6]; };
struct __attribute__((packed)) tight { char c; long n; };
struct reals { double d[3]; float f; };
struct huge { long a[40]; char *p; };

long c_trio(long x, struct trio t, long y);
int c_text(struct text s);
long c_mix(struct mix m, struct mix *q, int n);
long c_wide(struct wide w);
long c_tight(struct tight t);
long c_vsum(int n, ...);
struct trio c_mk(struct trio t, long d);
struct reals c_reals(struct reals r, double k);
long c_huge(struct huge h, long k);
long c_calls_back(char *buf);
long c_generic(char *buf);

long n_trio(long x, struct trio t, long y);
int n_text(struct text s);
long n_mix(struct mix m, struct mix *q, int n);
long n_wide(struct wide w);
long n_tight(struct tight t);
struct trio n_mk(struct trio t, long d);
struct reals n_reals(struct reals r, double k);
long n_huge(struct huge h, long k);
