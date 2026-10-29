/* GCC's mode attribute sets an integer or floating type's width (gmp's
   longlong.h: UQItype, USItype, UDItype); nanofil ignored it, so a
   DImode int had four bytes. */
#include <stdio.h>
typedef int QItype __attribute__((mode(QI)));
typedef unsigned int UQItype __attribute__((mode(QI)));
typedef int HItype __attribute__((mode(HI)));
typedef int SItype __attribute__((mode(SI)));
typedef unsigned int USItype __attribute__((__mode__(__SI__)));
typedef int DItype __attribute__((mode(DI)));
typedef unsigned int UDItype __attribute__((mode(DI)));
typedef int Wtype __attribute__((mode(word)));
typedef float DFtype __attribute__((mode(DF)));

struct s { char c; DItype d; };

int main(void) {
    printf("%zu %zu %zu %zu %zu %zu %zu %zu %zu\n", sizeof(QItype), sizeof(UQItype),
           sizeof(HItype), sizeof(SItype), sizeof(USItype), sizeof(DItype),
           sizeof(UDItype), sizeof(Wtype), sizeof(DFtype));
    QItype q = 200; UQItype uq = 200; HItype h = 70000;
    UDItype big = 1; big <<= 40;
    DItype neg = -1;
    UDItype hi = (UDItype)neg >> 1;
    DFtype f = 1.0 / 3;
    printf("%d %d %d %llu %llu %.17g %zu\n", q, uq, h, (unsigned long long)big,
           (unsigned long long)hi, f, __builtin_offsetof(struct s, d));
    return 0;
}
