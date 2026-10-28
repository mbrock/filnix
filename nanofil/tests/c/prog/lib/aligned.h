/* Structs and unions whose definition carries GNU's aligned attribute,
   as xz's io_buf does: alignment max(N, natural), size rounded up. */
#include <stdint.h>
struct __attribute__((aligned(16))) a16 { int x; };
union __attribute__((aligned(16))) buf { uint8_t u8[20]; uint32_t u32[5]; };
struct outer { char c; union buf u; short s; };
struct __attribute__((packed, aligned(4))) pa { char a; int b; };
struct __attribute__((aligned)) bare { char c; };
struct a16 c_a16(struct a16 a, int k);
struct a16 n_a16(struct a16 a, int k);
long c_outer_sum(struct outer o);
long n_outer_sum(struct outer o);
struct pa c_pa(struct pa p);
/* An eightbyte with no member data in it (alignment padding, or only
   unnamed bit-fields) is SysV class NO_CLASS, and clang passes the
   struct without it: struct a16 and struct ub as one word, struct lo as
   the one word at offset 8. */
struct ub { long a; int :32; };
struct lo { int :32; int :32; long b; };
struct ub c_ub(struct ub u, int k);
struct ub n_ub(struct ub u, int k);
long c_lo(struct lo l, int k);
long n_lo(struct lo l, int k);
/* Past a prototype clang passes them byval, every eightbyte. */
long c_va(int n, ...);
long n_va(int n, ...);
