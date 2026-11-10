/* A null zreturn returns no words, so a call that reads a result fails
   the generic entry's return size check. (filcc's verifier rejects
   zreturn of a constant null, so this one is null only at run time.) */
#include <stdfil.h>
#include <stdlib.h>

void nothing(void) { zreturn(getenv("NANOFIL_ZRETURN_UNSET")); }

int main(void)
{
    int (*z)(void) = (void *) nothing;
    return z();
}
