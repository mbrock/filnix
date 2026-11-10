/* PCRE2's JIT interface on Fil-C, served by the regex compiler of rx.pl
   and nanofil instead of sljit. pcre2_jit_compile.c includes this when
   the library is built for Fil-C without sljit (SUPPORT_FILC_RX, see
   pcre2-rx-hook.patch), and its pcre2_jit_compile, pcre2_jit_match and
   the two internal helpers call the functions below.

   pcre2_jit_compile(code, PCRE2_JIT_COMPLETE) writes the pattern's
   bytecode as the terms of pcre2_rx_terms.h and looks in a cache
   directory for the shared object made from exactly that text:

       KEY.pl   the terms; KEY is a hash of them
       KEY.so   one function, rx_m, as rx.pl describes it
       KEY.no   instead of KEY.so: rx.pl does not compile this pattern
       KEY.log  what the compiler printed

   On a miss it runs the compiler, `COMPILER KEY.pl OUTPUT`, which exits
   0 having written the shared object, or 1 having written why not; any
   other status caches nothing. The shared object is loaded with dlopen
   and its function kept in the code's executable_jit, where pcre2_match
   finds it. A pattern without one is matched by the interpreter.

   Two environment variables switch it on, read with secure_getenv so a
   set-id program ignores them:

       PCRE2_RX_CACHE      the cache directory, an absolute path. It must
                           belong to the effective user or to root and
                           be writable by nobody else, since what is in
                           it is loaded as code.
       PCRE2_RX_COMPILER   the compiler to run on a miss. Without it the
                           cache is only read.

   Without PCRE2_RX_CACHE the library behaves as one built with
   --disable-jit. A cache directory belongs to one compiler: the key
   covers the bytecode and this file's interface, not the version of
   rx.pl or nanofil. */

#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <spawn.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#include "pcre2_rx_terms.h"

/* Bump when the terms or the function's contract change. */
#define RX_INTERFACE 2

/* The first backtrack stack of a match data block, in longs. It doubles
   when the function reports that it was too small. */
#define RX_STACK_START 1024

extern char **environ;

typedef int rx_function(const uint8_t *subject, long length, long start, long *ovector, long *stack, long slimit,
                        long budget);

typedef struct rx_executable {
    void *handle; /* from dlopen */
    rx_function *match;
    size_t size; /* of the shared object, for PCRE2_INFO_JITSIZE */
} rx_executable;

/* The cache directory, or NULL when there is none to trust. */
static const char *rx_cache(void)
{
    const char *dir = secure_getenv("PCRE2_RX_CACHE");
    struct stat st;
    if (dir == NULL || dir[0] != '/' || stat(dir, &st) != 0 || !S_ISDIR(st.st_mode))
        return NULL;
    if ((st.st_uid != geteuid() && st.st_uid != 0) || (st.st_mode & (S_IWGRP | S_IWOTH)) != 0)
        return NULL;
    return dir;
}

/* Two FNV-1a hashes of the text. A collision cannot load the wrong
   function, because KEY.pl holds the text and is compared. */
static void rx_key(const char *text, size_t length, char key[33])
{
    uint64_t a = 0xcbf29ce484222325u, b = 0x84222325cbf29ce4u;
    for (size_t i = 0; i < length; i++) {
        a = (a ^ (uint8_t)text[i]) * 0x100000001b3u;
        b = (b ^ (uint8_t)text[length - 1 - i]) * 0x100000001b3u;
    }
    snprintf(key, 33, "%016llx%016llx", (unsigned long long)a, (unsigned long long)b);
}

/* 1 when the file holds exactly the text, 0 when it holds something
   else, -1 when it cannot be read. */
static int rx_holds(const char *path, const char *text, size_t length)
{
    char buffer[4096];
    size_t at = 0;
    ssize_t n;
    int fd = open(path, O_RDONLY | O_CLOEXEC);
    if (fd < 0)
        return -1;
    while ((n = read(fd, buffer, sizeof buffer)) > 0) {
        if ((size_t)n > length - at || memcmp(buffer, text + at, (size_t)n) != 0)
            break;
        at += (size_t)n;
    }
    close(fd);
    return n < 0 ? -1 : n == 0 && at == length;
}

/* A new empty file in the cache directory, to be renamed into place. */
static int rx_temporary(const char *dir, char path[PATH_MAX])
{
    if (snprintf(path, PATH_MAX, "%s/tmp.XXXXXX", dir) >= PATH_MAX)
        return -1;
    return mkstemp(path);
}

static BOOL rx_store(const char *dir, const char *path, const char *text, size_t length)
{
    char temporary[PATH_MAX];
    int fd = rx_temporary(dir, temporary);
    BOOL ok;
    if (fd < 0)
        return FALSE;
    ok = write(fd, text, length) == (ssize_t)length;
    ok = fchmod(fd, 0644) == 0 && ok;
    ok = close(fd) == 0 && ok;
    ok = ok && rename(temporary, path) == 0;
    if (!ok)
        unlink(temporary);
    return ok;
}

/* Run `compiler terms output` with its output in the log: its exit
   status, or -1. */
static int rx_run(const char *compiler, const char *terms, const char *output, const char *log)
{
    char *argv[] = { (char *)compiler, (char *)terms, (char *)output, NULL };
    posix_spawn_file_actions_t actions;
    pid_t pid;
    int status, failed;
    if (posix_spawn_file_actions_init(&actions) != 0)
        return -1;
    failed = posix_spawn_file_actions_addopen(&actions, 0, "/dev/null", O_RDONLY, 0) ||
             posix_spawn_file_actions_addopen(&actions, 1, log, O_WRONLY | O_CREAT | O_TRUNC, 0644) ||
             posix_spawn_file_actions_adddup2(&actions, 1, 2) || posix_spawn(&pid, compiler, &actions, NULL, argv, environ);
    posix_spawn_file_actions_destroy(&actions);
    if (failed)
        return -1;
    while (waitpid(pid, &status, 0) < 0)
        if (errno != EINTR)
            return -1; /* someone else reaped it */
    return WIFEXITED(status) ? WEXITSTATUS(status) : -1;
}

static rx_executable *rx_load(const char *path, pcre2_memctl *memctl)
{
    struct stat st;
    rx_executable *rx;
    rx_function *match;
    void *handle;
    if (stat(path, &st) != 0 || (handle = dlopen(path, RTLD_NOW | RTLD_LOCAL)) == NULL)
        return NULL;
    match = (rx_function *)dlsym(handle, "rx_m");
    rx = match == NULL ? NULL : memctl->malloc(sizeof *rx, memctl->memory_data);
    if (rx == NULL) {
        dlclose(handle);
        return NULL;
    }
    rx->handle = handle;
    rx->match = match;
    rx->size = (size_t)st.st_size;
    return rx;
}

/* The function for these terms: from the cache, or compiled into it. */
static rx_executable *rx_find(const char *dir, const char *text, size_t length, pcre2_memctl *memctl)
{
    char key[33], terms[PATH_MAX], so[PATH_MAX], no[PATH_MAX], log[PATH_MAX], temporary[PATH_MAX];
    const char *compiler = secure_getenv("PCRE2_RX_COMPILER");
    int fd, status;
    rx_key(text, length, key);
    if (snprintf(terms, PATH_MAX, "%s/%s.pl", dir, key) >= PATH_MAX)
        return NULL;
    snprintf(so, PATH_MAX, "%s/%s.so", dir, key);
    snprintf(no, PATH_MAX, "%s/%s.no", dir, key);
    snprintf(log, PATH_MAX, "%s/%s.log", dir, key);
    switch (rx_holds(terms, text, length)) {
    case 0:
        return NULL; /* another pattern has this key */
    case 1:
        if (access(no, F_OK) == 0)
            return NULL;
        if (access(so, F_OK) == 0)
            return rx_load(so, memctl);
        break;
    default:
        if (compiler == NULL || !rx_store(dir, terms, text, length))
            return NULL;
    }
    if (compiler == NULL || (fd = rx_temporary(dir, temporary)) < 0)
        return NULL;
    close(fd);
    status = rx_run(compiler, terms, temporary, log);
    if (status == 0 && chmod(temporary, 0755) == 0 && rename(temporary, so) == 0)
        return rx_load(so, memctl);
    if (status != 1 || chmod(temporary, 0644) != 0 || rename(temporary, no) != 0)
        unlink(temporary);
    return NULL;
}

/* pcre2_jit_compile, after it has checked its arguments. As with sljit
   and a pattern that says (*NO_JIT), 0 does not promise a function. */
static int rx_compile(pcre2_real_code *re, uint32_t options)
{
    const char *dir = rx_cache();
    char *text = NULL;
    size_t length = 0;
    FILE *f;
    if (dir == NULL)
        return PCRE2_ERROR_JIT_BADOPTION;
    if ((re->flags & PCRE2_NOJIT) != 0 || (options & PCRE2_JIT_COMPLETE) == 0 || re->executable_jit != NULL ||
        rx_unsupported(NULL, re) != 0)
        return 0;
    if ((f = open_memstream(&text, &length)) == NULL)
        return PCRE2_ERROR_NOMEMORY;
    fprintf(f, "%% PCRE2 %d.%d, rx interface %d\n", PCRE2_MAJOR, PCRE2_MINOR, RX_INTERFACE);
    rx_write_ops(f);
    rx_write_pattern(f, "m", re);
    if (fclose(f) != 0) {
        free(text);
        return PCRE2_ERROR_NOMEMORY;
    }
    re->executable_jit = rx_find(dir, text, length, &re->memctl);
    free(text);
    return 0;
}

static void rx_free(void *executable, pcre2_memctl *memctl)
{
    rx_executable *rx = executable;
    dlclose(rx->handle);
    memctl->free(rx, memctl->memory_data);
}

/* pcre2_jit_match. The function matches with no match options and no
   offset limit: PCRE2_ERROR_JIT_BADOPTION says the call asks for more.
   PCRE2_ERROR_JIT_STACKLIMIT says its backtrack stack would pass the
   heap limit, and PCRE2_ERROR_MATCHLIMIT that it backtracked more often
   than the match limit, which it counts in its own units as sljit's
   code does. After any of the three pcre2_match uses the interpreter,
   so its callers get the interpreter's answer and its errors. */
static int rx_match(const pcre2_real_code *re, PCRE2_SPTR subject, PCRE2_SIZE length, PCRE2_SIZE start_offset,
                    uint32_t options, pcre2_match_data *match_data, pcre2_match_context *mcontext)
{
    const rx_executable *rx = re->executable_jit;
    /* The function writes every group's pair; a smaller ovector gets its
       share of them from the front of the stack block. */
    size_t pairs = (size_t)re->top_bracket + 1;
    size_t scratch = match_data->oveccount < pairs ? 2 * pairs : 0;
    size_t want = scratch + RX_STACK_START;
    size_t limit = mcontext == NULL ? HEAP_LIMIT : mcontext->heap_limit; /* kibibytes */
    uint32_t budget = mcontext == NULL ? MATCH_LIMIT : mcontext->match_limit;
    long *ovector;
    int rc;

    if (rx == NULL || (options & ~(PCRE2_NO_UTF_CHECK | PCRE2_COPY_MATCHED_SUBJECT)) != 0 ||
        (mcontext != NULL && mcontext->offset_limit != PCRE2_UNSET))
        return match_data->rc = PCRE2_ERROR_JIT_BADOPTION;
    if ((match_data->flags & PCRE2_MD_COPIED_SUBJECT) != 0) {
        match_data->memctl.free((void *)match_data->subject, match_data->memctl.memory_data);
        match_data->flags &= ~PCRE2_MD_COPIED_SUBJECT;
    }
    if (re->limit_heap < limit)
        limit = re->limit_heap;
    limit = limit * 1024 / sizeof(long);
    if (re->limit_match < budget)
        budget = re->limit_match;

    for (;;) {
        if (match_data->filc_rx_size < want) {
            long *stack;
            if (want > limit)
                return match_data->rc = PCRE2_ERROR_JIT_STACKLIMIT;
            stack = match_data->memctl.malloc(want * sizeof(long), match_data->memctl.memory_data);
            if (stack == NULL)
                return match_data->rc = PCRE2_ERROR_NOMEMORY;
            if (match_data->filc_rx_stack != NULL)
                match_data->memctl.free(match_data->filc_rx_stack, match_data->memctl.memory_data);
            match_data->filc_rx_stack = stack;
            match_data->filc_rx_size = want;
        }
        ovector = scratch != 0 ? match_data->filc_rx_stack : (long *)match_data->ovector;
        rc = rx->match(subject, (long)length, (long)start_offset, ovector, match_data->filc_rx_stack + scratch,
                       (long)(match_data->filc_rx_size - scratch), (long)budget);
        if (rc >= 0)
            break;
        if (rc == -2)
            return match_data->rc = PCRE2_ERROR_MATCHLIMIT;
        want = scratch + 2 * (match_data->filc_rx_size - scratch);
    }

    if (rc == 0)
        rc = PCRE2_ERROR_NOMATCH;
    else {
        /* One more than the highest group that is set, or 0 when the
           ovector has no room for it. */
        size_t top = pairs;
        while (top > 1 && ovector[2 * top - 2] == -1)
            top--;
        rc = top > match_data->oveccount ? 0 : (int)top;
        if (scratch != 0)
            memcpy(match_data->ovector, ovector, 2 * match_data->oveccount * sizeof(PCRE2_SIZE));
    }
    match_data->code = re;
    match_data->subject = subject;
    match_data->subject_length = length;
    match_data->start_offset = start_offset;
    match_data->rc = rc;
    match_data->startchar = rc >= 0 ? match_data->ovector[0] : 0;
    match_data->leftchar = 0;
    match_data->rightchar = 0;
    match_data->mark = NULL;
    match_data->matchedby = PCRE2_MATCHEDBY_JIT;
    match_data->options = options;
    return rc;
}
