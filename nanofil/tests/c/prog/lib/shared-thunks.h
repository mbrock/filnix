/* Calls that nanofil and clang objects both make through one weak
   thunk, pizlonatedFI<Sig>_<f>: the linker keeps one per name, so it
   serves every caller with that signature. The fast signature has one
   digit per word (integer, float, double, pointer), so a 32-bit and a
   64-bit integer argument share it. */
#include <stdint.h>
long c_isum(int n, ...);           /* defined by clang, variadic */
double c_mix(int n, ...);
struct two { long a, b; };
struct two c_two(long a, long b);   /* defined by clang, fixed */
long c_calls(void);                 /* clang's calls of the three */
long n_isum(int n, ...);           /* defined by nanofil */
/* More than 16 words: clang names its call thunk and nanofil's entry
   pizlonatedFI0_<f> (generic), nanofil its own calls' thunk FIN..._<f>. */
#define BIG_PARAMS long a, long b, long c, long d, long e, long f, long g, \
    long h, long i, long j, long k, long l, long m, long n, long o,        \
    long p, int q, long r
long c_big(BIG_PARAMS);
long n_big(BIG_PARAMS);
extern long (*n_big_ptr)(BIG_PARAMS);
