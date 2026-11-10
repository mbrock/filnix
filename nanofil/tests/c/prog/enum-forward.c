/* GNU C lets a declaration name an enum before its definition, as
   glibc's nss_files.h declares functions returning enum nss_status
   before nss.h defines it with negative constants. Both declarations
   name the one enum, whose type is then int, so a call's value
   sign-extends; read as the placeholder uint it would not. */
#include <stdio.h>

extern enum status lookup(int);
enum status { TRYAGAIN = -2, UNAVAIL, NOTFOUND, SUCCESS };
typedef enum status lookup_fn(int);
extern lookup_fn lookup;
enum status lookup(int k) { return k > 0 ? SUCCESS : TRYAGAIN; }

int main(void)
{
    long a = lookup(0), b = lookup(3);
    printf("%ld %ld %d\n", a, b, lookup(-1) < 0);
    return 0;
}
