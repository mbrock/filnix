// link: lib/shared-thunks.c
// link-first
/* shared-thunks.c with clang's object linked first, so clang's weak
   thunks serve nanofil's calls. */
#include "shared-thunks.c"
