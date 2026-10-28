// error: conflicting types for 'strerror_r'
/* gnulib's probe for the POSIX strerror_r: under _GNU_SOURCE glibc
   declares it returning char *, so clang refuses this and configure
   picks the GNU signature. */
#define _GNU_SOURCE
#include <string.h>
extern int strerror_r(int, char *, size_t);
