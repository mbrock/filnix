/* libnanofil: nanofil's Gallina backend (rocq/backend) as a Fil-C shared
 * library, compiled through CertiRocq's λANF, anf/lower/AnfLower.v and
 * `nanofil-backend compile-allocated` over the arena of nanofil/anf
 * (docs/lambda-anf.md, M4).
 *
 * A program hands it the IR text of a module and gets back what
 * `nanofil-backend COMMAND FILE.ir` would print, in the process.
 *
 * The library keeps one private arena per process. The first call
 * makes it and runs the program's entry once. Each call after that
 * starts from the state the entry left: its nursery is empty, its
 * major heap is cut back to the entry's constants, and pages above
 * those are given back to the kernel once they pass a threshold. A
 * mutex serializes the calls, so any thread may call. */
#ifndef NANOFIL_H
#define NANOFIL_H

#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* The compilers of `nanofil-backend`, for nanofil_compile_ir's command. */
enum {
    NANOFIL_COMPILE = 0,           /* `compile`: no optimization, stack homes */
    NANOFIL_COMPILE_PROMOTED = 1,  /* `compile-promoted` */
    NANOFIL_COMPILE_ALLOCATED = 2, /* `compile-allocated`: registers too */
};

/* What nanofil_compile_ir returns. */
enum {
    NANOFIL_OK = 0,        /* *out is the assembly */
    NANOFIL_REFUSED = 1,   /* not a valid module, or not IR text; *out says why */
    NANOFIL_OUTSIDE = 3,   /* valid, perhaps, but outside the compiler; *out says why */
    NANOFIL_NOMEMORY = -1, /* the arena or the output could not be made; *out is NULL */
};

/* Compiles the IR text ir[0 .. ir_len) with command, which is one of
 * NANOFIL_COMPILE*. The status is the one `nanofil-backend` exits with.
 * On NANOFIL_OK, *out is the assembly and *out_len its length; on
 * NANOFIL_REFUSED and NANOFIL_OUTSIDE, *out is the reason, without the
 * "nanofil-backend: " that the command prints before it. Either way the
 * text is followed by a NUL byte that *out_len does not count, and the
 * caller frees it with free(). */
int nanofil_compile_ir(int command, const char *ir, size_t ir_len, char **out, size_t *out_len);

#ifdef __cplusplus
}
#endif

#endif
