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

/* The commands of `nanofil-backend`, for nanofil_compile_ir's command. */
enum {
    NANOFIL_COMPILE = 0,           /* `compile`: no optimization, stack homes */
    NANOFIL_COMPILE_PROMOTED = 1,  /* `compile-promoted` */
    NANOFIL_COMPILE_ALLOCATED = 2, /* `compile-allocated`: registers too */
    NANOFIL_SHARED_ALLOCATED = 3,  /* `shared-allocated`: the assembly of
                                      compile-allocated, assembled (Encode.v)
                                      and linked (Elf.v): *out is the bytes
                                      of a shared object, for nanofil_load */
    NANOFIL_OBJECT_ALLOCATED = 4,  /* `object-allocated`: the object as text,
                                      for the gate */
    NANOFIL_REGEX = 5,             /* the text is not IR but the terms of
                                      experiments/regex-nanofil/pcre2_rx_terms.h:
                                      what PCRE2's pcre2_compile made of
                                      patterns. *out is the shared object
                                      of their functions (anf/rx/Rx.v, then
                                      as NANOFIL_SHARED_ALLOCATED) */
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

/* nanofil_compile_ir(NANOFIL_REGEX, terms, terms_len, out, out_len): a
 * PCRE2 pattern's bytecode, as pcre2_rx_terms.h writes it, compiled to
 * a shared object whose function rx_NAME matches it. NANOFIL_REFUSED
 * when a pattern is not compiled: *out is then the comment rx.pl prints
 * for it ("% m: unsupported: ..."), or says that the terms are not
 * read. */
int nanofil_compile_regex(const char *terms, size_t terms_len, char **out, size_t *out_len);

/* Loads the shared object image[0 .. len), as nanofil_compile_ir gives
 * it for NANOFIL_SHARED_ALLOCATED and NANOFIL_REGEX, into the process:
 * it writes the bytes to an anonymous file (memfd_create) and opens that
 * with dlopen(RTLD_NOW | RTLD_LOCAL), so no file is written anywhere.
 * Each image is a new object, even when an earlier one had the same
 * bytes. Gives dlopen's handle, for dlsym and dlclose, or NULL: then
 * dlerror() says why, or, when it says nothing, errno does. Fil-C's
 * dlclose leaves an object loaded, so the memory of each image stays
 * mapped until the process exits. */
void *nanofil_load(const void *image, size_t len);

#ifdef __cplusplus
}
#endif

#endif
