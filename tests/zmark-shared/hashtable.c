/* A chained hash table in a zmark_shared mapping, shared by several
   processes that insert and delete under a process-shared mutex. Buckets,
   chains and the free list are ordinary pointers stored after fork. Each
   process tracks which of its keys are present; at the end the parent checks
   the table against every process's record. Usage: hashtable NPROC OPS */
#include <pthread.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>
#include <stdfil.h>

#define NBUCKETS 257
#define MAXPROC 16
#define KEYS 512 /* keys per process */

struct entry {
    struct entry *next;
    struct entry **pprev; /* address of the pointer that points to us */
    long key;
    char value[24];
};

struct table {
    pthread_mutex_t lock;
    struct entry *free;
    struct entry *buckets[NBUCKETS];
    long count;
    unsigned char present[MAXPROC][KEYS];
    struct entry entries[MAXPROC * KEYS];
};

static struct table *t;

static void fail(const char *what, long key)
{
    fprintf(stderr, "FAIL: %s (key %ld, pid %d)\n", what, key, getpid());
    exit(1);
}

static unsigned bucket(long key)
{
    return (unsigned)((uint64_t)key * 0x9e3779b97f4a7c15ull >> 40) % NBUCKETS;
}

static struct entry *find(long key)
{
    for (struct entry *e = t->buckets[bucket(key)]; e; e = e->next)
        if (e->key == key)
            return e;
    return NULL;
}

static void insert(long key)
{
    struct entry *e = t->free;
    if (!e)
        fail("free list empty", key);
    t->free = e->next;
    e->key = key;
    snprintf(e->value, sizeof e->value, "v%ld", key);
    struct entry **head = &t->buckets[bucket(key)];
    e->next = *head;
    e->pprev = head;
    if (e->next)
        e->next->pprev = &e->next;
    *head = e;
    t->count++;
}

static void delete(struct entry *e)
{
    *e->pprev = e->next;
    if (e->next)
        e->next->pprev = e->pprev;
    e->pprev = NULL;
    e->key = -1;
    e->next = t->free;
    t->free = e;
    t->count--;
}

static void worker(int me, long ops)
{
    unsigned seed = 1234 + me;
    for (long i = 0; i < ops; i++) {
        int k = rand_r(&seed) % KEYS;
        long key = (long)me * KEYS + k;
        pthread_mutex_lock(&t->lock);
        struct entry *e = find(key);
        if (!!e != t->present[me][k])
            fail("presence mismatch", key);
        if (e) {
            char want[24];
            snprintf(want, sizeof want, "v%ld", key);
            if (strcmp(e->value, want) || zgetlower(e) != (void *)t)
                fail("bad entry", key);
            delete(e);
            t->present[me][k] = 0;
        } else {
            insert(key);
            t->present[me][k] = 1;
        }
        pthread_mutex_unlock(&t->lock);
    }
}

int main(int argc, char **argv)
{
    int nproc = argc > 1 ? atoi(argv[1]) : 8;
    long ops = argc > 2 ? atol(argv[2]) : 20000;
    if (nproc < 1 || nproc > MAXPROC)
        return 2;
    t = mmap(NULL, sizeof *t, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    if (t == MAP_FAILED)
        return 1;
    zmark_shared(t);
    pthread_mutexattr_t attr;
    pthread_mutexattr_init(&attr);
    pthread_mutexattr_setpshared(&attr, PTHREAD_PROCESS_SHARED);
    pthread_mutex_init(&t->lock, &attr);
    for (int i = MAXPROC * KEYS; i--;) {
        t->entries[i].next = t->free;
        t->free = &t->entries[i];
    }
    pid_t pids[MAXPROC];
    for (int i = 0; i < nproc; i++) {
        pids[i] = fork();
        if (!pids[i]) {
            worker(i, ops);
            _exit(0);
        }
    }
    for (int i = 0; i < nproc; i++) {
        int st;
        if (waitpid(pids[i], &st, 0) != pids[i] || !WIFEXITED(st) || WEXITSTATUS(st))
            fail("worker failed", i);
    }
    long expected = 0, seen = 0, free_count = 0;
    for (int p = 0; p < nproc; p++)
        for (int k = 0; k < KEYS; k++) {
            long key = (long)p * KEYS + k;
            if (!!find(key) != t->present[p][k])
                fail("final presence mismatch", key);
            expected += t->present[p][k];
        }
    for (int b = 0; b < NBUCKETS; b++)
        for (struct entry **pp = &t->buckets[b]; *pp; pp = &(*pp)->next) {
            if ((*pp)->pprev != pp || bucket((*pp)->key) != (unsigned)b)
                fail("broken chain", (*pp)->key);
            seen++;
        }
    for (struct entry *e = t->free; e; e = e->next)
        free_count++;
    if (seen != expected || t->count != expected || seen + free_count != MAXPROC * KEYS)
        fail("counts", seen);
    printf("hashtable ok: %d processes, %ld ops each, %ld entries live\n", nproc, ops, seen);
    return 0;
}
