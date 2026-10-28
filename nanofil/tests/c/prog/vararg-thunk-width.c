// link: lib/vararg-thunk-width.c
/* A 32-bit and a 64-bit integer passed past the prototype give the
   same fast signature (both are one integer word), so calls with
   either go through one weak thunk, whichever object file the linker
   took it from (in xz, message.c's served list.c). The thunk must copy
   the whole word: nanofil's, emitted here for the 32-bit call, kept
   only the low half of clang's 64-bit one (lib/vararg-thunk-width.c)
   when the word went on the stack. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
void c_print64(char *out, uint64_t v);
static char out[40];
int main(void) {
    uint32_t u = 0x01bc3f1a;
    snprintf(out, sizeof out, "%08" PRIx32, u);
    puts(out);
    c_print64(out, 0x9a7ff1b101bc3f1aULL);
    puts(out);
    return 0;
}
