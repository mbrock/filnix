/* libnanofil's entry points (nanofil.h) around the program that
 * anf/backend/Drive.v's [run] is, as anf/backend/driver.c runs it, but
 * in the caller's process, and many times over one arena.
 *
 * The program's value is the closure of [run] (anf_main, on a fresh
 * arena, which also copies the constants' pool to the bottom of the
 * major heap). The first call makes the arena, runs anf_main and
 * collects once with the closure as a root, so that the closure is in
 * the major heap too, and keeps the length of the major heap then as
 * the mark that every later call rewinds to (anf_arena_rewind). A call
 * copies the text into the arena as pieces of ANF_PIECE bytes, applies
 * [run] to the command and the pieces, and copies each chunk of the
 * stream it gives into one malloc'd buffer.
 *
 * nanofil_load writes a shared object to a memfd and dlopens it by a
 * /proc/self/fd path of its own; the mapping keeps the file alive after
 * the descriptor is closed.
 *
 * ANF_SLAB, ANF_NURSERY and ANF_ROOTS size the arena as for driver.c;
 * ANF_RELEASE (default 2^22 words, 16 MiB) is how far past the mark the
 * major heap may have grown before a call gives its pages back. */
#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>
#include <ucontext.h>
#include <unistd.h>
#include <stdlib.h>
#include <string.h>
#include "../anf_arena.h"
#include "nanofil.h"

uint32_t anf_main(uint32_t *arena, struct anf_state *st);
uint32_t anf_apply2(uint32_t *arena, struct anf_state *st, uint32_t fid, uint32_t a, uint32_t b);
const uint8_t *anf_str_bytes(const uint32_t *arena, uint32_t s, uint32_t *len);

static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static int made; /* 0 not yet, 1 made, -1 could not be made */
static uint32_t *arena;
static struct anf_state *st;
static uint32_t run_closure, mark, release_words, piece_bytes;

static uint32_t env_words(const char *name, uint32_t dflt)
{
    const char *s = getenv(name);
    return s ? (uint32_t)strtoul(s, NULL, 0) : dflt;
}

static int make(void)
{
    if (anf_arena_init(&arena, &st, env_words("ANF_SLAB", 1U << 28),
                       env_words("ANF_NURSERY", ANF_DEFAULT_NURSERY), env_words("ANF_ROOTS", 1U << 24)))
        return -1;
    anf_root_push(st, anf_main(arena, st));
    anf_minor_gc(arena, anf_roots(st), st);
    run_closure = anf_root_pop(st);
    mark = st->major_idx;
    release_words = env_words("ANF_RELEASE", 1U << 22);
    piece_bytes = env_words("ANF_PIECE", 1U << 20);
    return 1;
}

static uint32_t apply(uint32_t clo, uint32_t arg)
{
    uint32_t idx = ANF_IDX(clo);
    return anf_apply2(arena, st, arena[idx + 1U], arena[idx + 2U], arg);
}

/* A block of two scanned fields, the ordinal ord, from the values on top
 * of the shadow roots (a under b), which it pops. */
static uint32_t pair(uint32_t ord)
{
    uint32_t idx = anf_alloc_words(arena, st, 3U);
    uint32_t b = anf_root_pop(st), a = anf_root_pop(st);
    arena[idx] = ANF_HDR(2U, ANF_ST_SCAN, ord);
    arena[idx + 1U] = a;
    arena[idx + 2U] = b;
    return ANF_BOX(idx);
}

/* A growing buffer for the output. */
struct buf {
    char *b;
    size_t n, cap;
    int failed;
};

static void put(struct buf *o, const uint8_t *p, size_t n)
{
    if (o->failed)
        return;
    if (o->cap - o->n < n + 1U) {
        size_t cap = o->cap ? o->cap : 1U << 16;
        while (cap - o->n < n + 1U)
            cap *= 2U;
        char *b = realloc(o->b, cap);
        if (!b) {
            o->failed = 1;
            return;
        }
        o->b = b;
        o->cap = cap;
    }
    if (n)
        memcpy(o->b + o->n, p, n);
    o->n += n;
    o->b[o->n] = 0;
}

static int compile_locked(int command, const char *ir, size_t ir_len, struct buf *o)
{
    if (made == 0)
        made = make();
    if (made < 0 || ir_len > 0xFFFFFFFFULL)
        return NANOFIL_NOMEMORY;
    if (anf_arena_rewind(arena, st, mark, release_words))
        return NANOFIL_NOMEMORY;

    /* The pieces, last first, consed onto nil. */
    anf_root_push(st, ANF_IMM(0U));
    for (size_t end = ir_len; end > 0;) {
        size_t start = (end - 1U) / piece_bytes * piece_bytes;
        uint32_t s = anf_bytes_from_buf(arena, st, (const uint8_t *)ir + start, (uint32_t)(end - start));
        uint32_t l = anf_root_pop(st);
        anf_root_push(st, s);
        anf_root_push(st, l);
        anf_root_push(st, pair(0U));
        end = start;
    }
    uint32_t input = anf_root_pop(st);
    anf_root_push(st, ANF_IMM((uint32_t)command));
    anf_root_push(st, input);
    uint32_t out = apply(run_closure, pair(0U));

    /* Done (ordinal 0) or Chunk (ordinal 1). */
    while (ANF_HDR_ORD(arena[ANF_IDX(out)]) == 1U) {
        for (uint32_t ps = arena[ANF_IDX(out) + 1U]; !ANF_IS_IMM(ps); ps = arena[ANF_IDX(ps) + 2U]) {
            uint32_t len;
            const uint8_t *b = anf_str_bytes(arena, arena[ANF_IDX(ps) + 1U], &len);
            put(o, b, len);
        }
        out = apply(arena[ANF_IDX(out) + 2U], ANF_IMM(0U));
    }
    uint32_t code = ANF_IMM_U31(arena[ANF_IDX(out) + 1U]);
    if (code != 0U) {
        uint32_t len;
        const uint8_t *b = anf_str_bytes(arena, arena[ANF_IDX(out) + 2U], &len);
        o->n = 0;
        put(o, b, len);
    }
    put(o, NULL, 0);
    return o->failed ? NANOFIL_NOMEMORY : (int)code;
}

/* The compile in progress, which runs on a fiber of its own: the lowered
 * program is as deep as the Gallina's recursion over the input, and a
 * caller's stack, whose size Fil-C fixes when the process starts, may
 * be 2 MB. Fil-C's makecontext allocates the size it is given and
 * checks the fiber's own stack limit, so a compile too deep for its
 * fiber stops with a stack overflow, as it would on a thread. The fiber
 * is made for each call, under the lock, because a Fil-C fiber belongs
 * to the thread that made it. */
static ucontext_t caller, fiber;
static struct {
    int command, code;
    const char *ir;
    size_t ir_len;
    struct buf *o;
} job;

static void run_job(void)
{
    job.code = compile_locked(job.command, job.ir, job.ir_len, job.o);
}

/* The fiber's stack size: ANF_FIBER_MB megabytes when that is set, or
 * 64 MB plus 16 bytes for each byte of the input. lvm.ir, 4.4 MB of IR,
 * needs 12 MB; the largest regex function within the block cap needs
 * under 10 MB from a few kilobytes of terms. The size costs address
 * space, not time: the kernel backs only the pages the compile touches. */
static size_t fiber_bytes(size_t ir_len)
{
    size_t mb = env_words("ANF_FIBER_MB", 0U);
    return mb ? mb << 20 : ((size_t)64 << 20) + 16U * ir_len;
}

/* Fil-C's makecontext passes only uc_stack.ss_size to the runtime
 * (zfiber_context_makecontext), which allocates the stack itself and
 * frees it when the collector reclaims the context, so no stack buffer
 * is given here. */
static int compile_on_fiber(int command, const char *ir, size_t ir_len, struct buf *o)
{
    if (getcontext(&fiber) != 0)
        return NANOFIL_NOMEMORY;
    job.command = command;
    job.ir = ir;
    job.ir_len = ir_len;
    job.o = o;
    job.code = NANOFIL_NOMEMORY;
    fiber.uc_stack.ss_sp = NULL;
    fiber.uc_stack.ss_size = fiber_bytes(ir_len);
    fiber.uc_link = &caller;
    makecontext(&fiber, run_job, 0);
    if (swapcontext(&caller, &fiber) != 0)
        job.code = NANOFIL_NOMEMORY;
    return job.code;
}

int nanofil_compile_ir(int command, const char *ir, size_t ir_len, char **out, size_t *out_len)
{
    struct buf o = {NULL, 0, 0, 0};
    int code;
    *out = NULL;
    *out_len = 0;
    if (command < NANOFIL_COMPILE || command > NANOFIL_REGEX) {
        static const char why[] = "no such command";
        put(&o, (const uint8_t *)why, sizeof why - 1U);
        code = o.failed ? NANOFIL_NOMEMORY : NANOFIL_REFUSED;
    } else {
        pthread_mutex_lock(&lock);
        code = compile_on_fiber(command, ir, ir_len, &o);
        pthread_mutex_unlock(&lock);
    }
    if (code == NANOFIL_NOMEMORY) {
        free(o.b);
        return code;
    }
    *out = o.b;
    *out_len = o.n;
    return code;
}

int nanofil_compile_regex(const char *terms, size_t terms_len, char **out, size_t *out_len)
{
    return nanofil_compile_ir(NANOFIL_REGEX, terms, terms_len, out, out_len);
}

/* The number of shared objects loaded so far. dlopen gives the object
 * already loaded under a name instead of opening another, and Fil-C's
 * dlclose leaves an object loaded, so a descriptor's /proc/self/fd path
 * names a new image only once: the number of a closed descriptor comes
 * back. Each image is opened under a name no other has had, its
 * descriptor's path with the number of the load written in the
 * directory part, "/." for a 0 bit and "//" for a 1, lowest first, which
 * the kernel reads as /proc/self/fd itself. */
static pthread_mutex_t load_lock = PTHREAD_MUTEX_INITIALIZER;
static unsigned long long loads;

void *nanofil_load(const void *image, size_t len)
{
    int fd = memfd_create("nanofil", MFD_CLOEXEC);
    if (fd < 0)
        return NULL;
    for (size_t at = 0; at < len;) {
        ssize_t n = write(fd, (const char *)image + at, len - at);
        if (n < 0 && errno == EINTR)
            continue;
        if (n <= 0) {
            int e = n < 0 ? errno : EIO;
            close(fd);
            errno = e;
            return NULL;
        }
        at += (size_t)n;
    }
    char path[256] = "/proc/self/fd";
    size_t at = strlen(path);
    pthread_mutex_lock(&load_lock);
    for (unsigned long long k = loads++; k; k >>= 1, at += 2)
        memcpy(path + at, k & 1U ? "//" : "/.", 2);
    pthread_mutex_unlock(&load_lock);
    snprintf(path + at, sizeof path - at, "/%d", fd);
    void *h = dlopen(path, RTLD_NOW | RTLD_LOCAL);
    int e = errno;
    close(fd);
    errno = e;
    return h;
}
