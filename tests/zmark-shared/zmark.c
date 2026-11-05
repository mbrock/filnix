/* Regressions for zmark_shared (docs/zmark-shared.md). Each subcommand is one
   case; zmark-shared.sh runs them and checks the outcome, including the
   cases that must panic. */
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdfil.h>

#define NPROC 8
#define PER 2000

struct node {
    struct node *next;
    long owner;
    long value;
};

struct seg {
    volatile int phase;
    char *p;
    char *q;
    void (*fp)(void);
    struct node *_Atomic top;
    char *_Atomic last;
    _Atomic long count;
    char *words[64];
    char *copy[64];
    struct node nodes[NPROC * PER];
    char data[4096];
};

static void fail(const char *what)
{
    fprintf(stderr, "FAIL: %s\n", what);
    exit(1);
}

#define CHECK(c) do { if (!(c)) fail(#c); } while (0)

static struct seg *map_seg(int mark)
{
    struct seg *s = mmap(NULL, sizeof *s, PROT_READ | PROT_WRITE,
                         MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    CHECK(s != MAP_FAILED);
    if (mark)
        zmark_shared(s);
    return s;
}

static int wait_child(pid_t pid)
{
    int st;
    CHECK(waitpid(pid, &st, 0) == pid);
    return WIFEXITED(st) ? WEXITSTATUS(st) : 128 + WTERMSIG(st);
}

static void hello(void) { }

/* Keep the compiler from seeing which object a pointer came from. */
static __attribute__((noinline)) void *launder(void *p)
{
    void *volatile v = p;
    return v;
}

/* The repro from the report: the parent stores pointers into the segment
   after fork; the child reads them. With "nomark" this is today's behavior,
   and the child traps on the post-fork pointer. */
static int postfork(int mark)
{
    struct seg *s = map_seg(mark);
    strcpy(s->data, "pre");
    strcpy(s->data + 100, "post");
    strcpy(s->data + 200, "moved");
    s->q = s->data;
    pid_t pid = fork();
    if (!pid) {
        while (s->phase != 1)
            usleep(1000);
        char *q = s->q;
        printf("child: q -> %s\n", q);
        CHECK(!strcmp(q, "moved"));
        char *p = s->p;
        printf("child: p hasvalidcap=%d\n", (int)zhasvalidcap(p));
        fflush(stdout);
        printf("child: p -> %s\n", p);
        CHECK(!strcmp(p, "post"));
        CHECK(zgetlower(p) == (void *)s);
        CHECK(zgetupper(p) >= (void *)(s + 1));
        /* The child stores too; the parent reads it after we exit. */
        s->p = s->data + 200;
        s->q = NULL;
        fflush(stdout);
        _exit(0);
    }
    s->p = s->data + 100;
    s->q = s->data + 200;
    s->phase = 1;
    int st = wait_child(pid);
    if (st)
        return st;
    CHECK(!s->q);
    CHECK(!strcmp(s->p, "moved"));
    puts("postfork ok");
    return 0;
}

/* Today's behavior on an unmarked segment, in one process: pointers of any
   kind may be stored and read back, and pre-fork pointers work in a child. */
static int unmarked(void)
{
    struct seg *s = map_seg(0);
    char *priv = malloc(16);
    strcpy(priv, "private");
    s->p = priv;
    s->fp = hello;
    s->q = s->data;
    strcpy(s->data, "seg");
    CHECK(!strcmp(s->p, "private"));
    s->fp();
    char *buf[2];
    memcpy(buf, &s->p, sizeof buf);
    CHECK(!strcmp(buf[0], "private") && !strcmp(buf[1], "seg"));
    pid_t pid = fork();
    if (!pid) {
        CHECK(!strcmp(s->p, "private"));
        CHECK(!strcmp(s->q, "seg"));
        _exit(0);
    }
    CHECK(!wait_child(pid));
    puts("unmarked ok");
    return 0;
}

static int store_private(void)
{
    struct seg *s = map_seg(1);
    char *priv = malloc(16);
    s->p = launder(priv);
    puts("store-private stored");
    return 0;
}

static int store_func(void)
{
    struct seg *s = map_seg(1);
    s->fp = (void (*)(void))launder((void *)hello);
    puts("store-func stored");
    return 0;
}

static int store_other(void)
{
    struct seg *a = map_seg(1);
    struct seg *b = map_seg(1);
    a->p = launder(b->data);
    puts("store-other stored");
    return 0;
}

static int store_atomic_private(void)
{
    struct seg *s = map_seg(1);
    char *priv = malloc(16);
    atomic_store(&s->last, (char *)launder(priv));
    puts("store-atomic-private stored");
    return 0;
}

static int cas_private(void)
{
    struct seg *s = map_seg(1);
    char *priv = malloc(16);
    char *expected = NULL;
    atomic_compare_exchange_strong(&s->last, &expected, (char *)launder(priv));
    puts("cas-private stored");
    return 0;
}

/* A Treiber stack of nodes inside the segment, pushed and popped by NPROC
   processes with CAS, plus exchange and atomic loads of pointers that other
   processes stored. */
static int atomics(void)
{
    struct seg *s = map_seg(1);
    pid_t pids[NPROC];
    for (int i = 0; i < NPROC; i++) {
        pids[i] = fork();
        if (!pids[i]) {
            for (int k = 0; k < PER; k++) {
                struct node *n = &s->nodes[i * PER + k];
                n->owner = i;
                n->value = k;
                struct node *old = atomic_load(&s->top);
                do
                    n->next = old;
                while (!atomic_compare_exchange_weak(&s->top, &old, n));
                char *prev = atomic_exchange(&s->last, (char *)&n->value);
                if (prev)
                    CHECK(zgetlower(prev) == (void *)s && *(long *)prev >= 0);
                atomic_fetch_add(&s->count, 1);
            }
            _exit(0);
        }
    }
    for (int i = 0; i < NPROC; i++)
        CHECK(!wait_child(pids[i]));
    long seen = 0;
    for (struct node *n = atomic_load(&s->top); n; n = n->next) {
        CHECK(zgetlower(n) == (void *)s);
        CHECK(n->owner >= 0 && n->owner < NPROC && n->value >= 0 && n->value < PER);
        seen++;
    }
    CHECK(seen == NPROC * PER && atomic_load(&s->count) == NPROC * PER);
    /* Now pop them all concurrently; nothing is pushed again, so no ABA. */
    for (int i = 0; i < NPROC; i++) {
        pids[i] = fork();
        if (!pids[i]) {
            for (;;) {
                struct node *old = atomic_load(&s->top);
                if (!old)
                    break;
                struct node *next = old->next;
                if (atomic_compare_exchange_strong(&s->top, &old, next)) {
                    old->owner = -1;
                    atomic_fetch_sub(&s->count, 1);
                } else if (old)
                    CHECK(zgetlower(old) == (void *)s);
            }
            _exit(0);
        }
    }
    for (int i = 0; i < NPROC; i++)
        CHECK(!wait_child(pids[i]));
    CHECK(!atomic_load(&s->top) && atomic_load(&s->count) == 0);
    for (int i = 0; i < NPROC * PER; i++)
        CHECK(s->nodes[i].owner == -1);
    puts("atomics ok");
    return 0;
}

/* A writer flips a slot between null and an address in the segment while
   the reader does plain loads: every non-null address it reads must carry
   the segment's capability, and every null none. */
static int race(void)
{
    struct seg *s = map_seg(1);
    pid_t pid = fork();
    if (!pid) {
        while (s->phase != 1)
            ;
        char *volatile *wslot = &s->p;
        while (s->phase == 1) {
            *wslot = s->data + 128;
            *wslot = NULL;
        }
        _exit(0);
    }
    s->phase = 1;
    long seen = 0, bad = 0;
    for (long i = 0; i < 20000000; i++) {
        /* A plain load (the inline path), reloaded each time. */
        atomic_signal_fence(memory_order_seq_cst);
        char *p = s->p;
        if (p) {
            seen++;
            if (zgetlower(p) != (void *)s)
                bad++;
        } else if (zhasvalidcap(p))
            bad++;
    }
    s->phase = 2;
    CHECK(!wait_child(pid));
    printf("race: %ld non-null loads, %ld without the right capability\n", seen, bad);
    CHECK(!bad && seen);
    return 0;
}

struct pair {
    char *a;
    char *b;
};

/* Copies out of the segment give each word the segment's capability, small
   (inline) and large (runtime), into heap and stack; copies within the
   segment and of in-segment pointers into it are allowed. */
static int memmove_out(void)
{
    struct seg *s = map_seg(1);
    pid_t pid = fork();
    if (!pid) {
        for (int i = 0; i < 64; i++) {
            snprintf(s->data + 64 * i, 64, "w%d", i);
            s->words[i] = s->data + 64 * i;
        }
        s->phase = 1;
        _exit(0);
    }
    CHECK(!wait_child(pid));
    char *one;
    memcpy(&one, &s->words[3], sizeof one);
    CHECK(!strcmp(one, "w3"));
    struct pair pr;
    memcpy(&pr, &s->words[5], sizeof pr);
    CHECK(!strcmp(pr.a, "w5") && !strcmp(pr.b, "w6"));
    struct pair *hp = malloc(sizeof *hp);
    memcpy(hp, launder(&s->words[7]), sizeof *hp);
    CHECK(!strcmp(hp->a, "w7") && !strcmp(hp->b, "w8"));
    char **big = malloc(sizeof s->words);
    memcpy(big, launder(s->words), sizeof s->words);
    for (int i = 0; i < 64; i++) {
        char want[8];
        snprintf(want, sizeof want, "w%d", i);
        CHECK(!strcmp(big[i], want));
    }
    /* Within the segment, and in-segment pointers into it. */
    memmove(s->copy, s->words, sizeof s->words);
    CHECK(!strcmp(s->copy[63], "w63"));
    memcpy(&s->copy[0], &pr, sizeof pr);
    CHECK(!strcmp(s->copy[1], "w6"));
    memcpy(&s->copy[2], big, 8 * sizeof(char *));
    CHECK(!strcmp(s->copy[9], "w7"));
    pid = fork();
    if (!pid) {
        CHECK(!strcmp(s->copy[0], "w5") && !strcmp(s->copy[2], "w0"));
        _exit(0);
    }
    CHECK(!wait_child(pid));
    puts("memmove ok");
    return 0;
}

/* memcpy into the segment copies bytes only: a private pointer comes back with the segment's
   capability, which does not cover it, and integer data with a stale capability (a word that once
   held a pointer) copies in without complaint. */
static int memmove_in_private(int mode)
{
    struct seg *s = map_seg(1);
    char **priv = malloc(64 * sizeof(char *));
    for (int i = 0; i < 64; i++)
        priv[i] = (char *)priv;
    ((unsigned *)&priv[1])[0] = 1;  /* integer stores leave priv's capability on the word */
    ((unsigned *)&priv[1])[1] = 0;
    CHECK(zhasvalidcap(priv[1]));
    memcpy(launder(s->copy), priv, mode == 1 ? 64 * sizeof(char *) : 2 * sizeof(char *));
    char **copy = ((struct seg *volatile)s)->copy;
    CHECK(copy[0] == (char *)priv && zgetlower(copy[0]) == (void *)s);
    CHECK((unsigned long)copy[1] == 1 && zgetlower(copy[1]) == (void *)s);
    if (mode == 2)
        printf("%p\n", *(void **)copy[0]);
    puts("memmove-in ok");
    return 0;
}

static int unmap_then_access(int which)
{
    struct seg *s = map_seg(1);
    s->p = s->data;
    char *p = s->p;
    CHECK(zhasvalidcap(p));
    CHECK(!munmap(s, sizeof *s));
    if (which == 0)
        printf("%d\n", *p);
    else
        printf("%p\n", (void *)((struct seg *volatile)s)->p);
    puts("munmap accessed");
    return 0;
}

static int mark_with_aux(void)
{
    struct seg *s = map_seg(0);
    s->p = s->data;
    zmark_shared(s);
    puts("mark-aux marked");
    return 0;
}

static int mark_private(void)
{
    void *m = mmap(NULL, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    CHECK(m != MAP_FAILED);
    zmark_shared(m);
    puts("mark-private marked");
    return 0;
}

static int mark_malloc(void)
{
    zmark_shared(malloc(4096));
    puts("mark-malloc marked");
    return 0;
}

static int mark_interior(void)
{
    struct seg *s = map_seg(0);
    zmark_shared(s->data);
    puts("mark-interior marked");
    return 0;
}

/* Whatever integers land in the segment, a loaded pointer can reach the
   segment and nothing else: any nonzero address gets the segment's
   capability, so an address outside it traps on access. */
static int hostile(int deref)
{
    struct seg *s = map_seg(1);
    char *priv = malloc(16);
    strcpy(priv, "secret");
    strcpy(s->data, "seg");
    uintptr_t *w = (uintptr_t *)s->words;
    w[0] = (uintptr_t)priv;
    w[1] = (uintptr_t)(s + 1) + 4096;
    w[2] = (uintptr_t)s - 16;
    w[3] = (uintptr_t)(void *)hello;
    w[4] = (uintptr_t)s->data;
    w[5] = (uintptr_t)zgetupper(s); /* one past the mapping's end */
    w[6] = 0;
    for (int i = 0; i < 6; i++)
        CHECK(zgetlower(s->words[i]) == (void *)s && zgetupper(s->words[i]) == zgetupper(s));
    for (int i = 0; i < 4; i++)
        CHECK(!zinbounds(s->words[i]));
    CHECK(!zhasvalidcap(s->words[6]));
    CHECK(!strcmp(s->words[4], "seg"));
    /* A tagged pointer keeps the segment's capability and works untagged. */
    w[7] = (uintptr_t)s->data | (1ul << 60);
    CHECK(!strcmp((char *)((uintptr_t)s->words[7] & ~(1ul << 60)), "seg"));
    switch (deref) {
    case 1:
        printf("%c\n", *s->words[0]);
        break;
    case 2:
        printf("%c\n", *s->words[5]);
        break;
    case 3:
        ((void (*)(void))s->words[3])();
        break;
    }
    puts("hostile ok");
    return 0;
}

/* A native process writes addresses into a file mapping that this process
   marked: the Fil-C reader gets the segment's capability for addresses in
   the segment and none otherwise. */
static int native(const char *writer)
{
    char path[] = "zmark-native-XXXXXX";
    int fd = mkstemp(path);
    CHECK(fd >= 0);
    CHECK(!ftruncate(fd, sizeof(struct seg)));
    struct seg *s = mmap(NULL, sizeof *s, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
    CHECK(s != MAP_FAILED);
    zmark_shared(s);
    char *priv = malloc(16);
    strcpy(priv, "secret");
    strcpy(s->data + 8, "from native");
    char cmd[512];
    snprintf(cmd, sizeof cmd, "%s %s %zu %lu %lu %zu", writer, path,
             (size_t)((char *)s->words - (char *)s), (unsigned long)(uintptr_t)s,
             (unsigned long)(uintptr_t)priv, (size_t)(s->data - (char *)s));
    CHECK(!system(cmd));
    for (int i = 0; i < 3; i++)
        CHECK(zgetlower(s->words[i]) == (void *)s);
    CHECK(!zinbounds(s->words[0]) && !zinbounds(s->words[2]));
    CHECK(!strcmp(s->words[1], "from native"));
    unlink(path);
    puts("native ok");
    return 0;
}

int main(int argc, char **argv)
{
    if (argc < 2)
        return 2;
    const char *c = argv[1];
    if (!strcmp(c, "postfork")) return postfork(1);
    if (!strcmp(c, "postfork-nomark")) return postfork(0);
    if (!strcmp(c, "unmarked")) return unmarked();
    if (!strcmp(c, "store-private")) return store_private();
    if (!strcmp(c, "store-func")) return store_func();
    if (!strcmp(c, "store-other")) return store_other();
    if (!strcmp(c, "store-atomic-private")) return store_atomic_private();
    if (!strcmp(c, "cas-private")) return cas_private();
    if (!strcmp(c, "atomics")) return atomics();
    if (!strcmp(c, "memmove")) return memmove_out();
    if (!strcmp(c, "race")) return race();
    if (!strcmp(c, "memmove-in-small")) return memmove_in_private(0);
    if (!strcmp(c, "memmove-in-big")) return memmove_in_private(1);
    if (!strcmp(c, "memmove-in-deref")) return memmove_in_private(2);
    if (!strcmp(c, "munmap-deref")) return unmap_then_access(0);
    if (!strcmp(c, "munmap-load")) return unmap_then_access(1);
    if (!strcmp(c, "mark-aux")) return mark_with_aux();
    if (!strcmp(c, "mark-private")) return mark_private();
    if (!strcmp(c, "mark-malloc")) return mark_malloc();
    if (!strcmp(c, "mark-interior")) return mark_interior();
    if (!strcmp(c, "hostile")) return hostile(0);
    if (!strcmp(c, "hostile-private")) return hostile(1);
    if (!strcmp(c, "hostile-end")) return hostile(2);
    if (!strcmp(c, "hostile-call")) return hostile(3);
    if (!strcmp(c, "native")) return native(argv[2]);
    return 2;
}
