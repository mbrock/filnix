/* M1 RSS and reservation limit measurements for zsys_mmap(MAP_NORESERVE) and
 * zsys_madvise(MADV_DONTNEED) under fugc_destructor_heap.
 */
#include "anf_arena.h"

#include <signal.h>
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

void *zsys_mmap(void *addr, size_t len, int prot, int flags, int fd, long off);
int zsys_munmap(void *addr, size_t len);

struct mem_snap {
    long vm_size_kb;
    long vm_rss_kb;
    long rss_anon_kb;
    long private_dirty_kb;
};

static long parse_kb_line(const char *buf, const char *key) {
    const char *p = strstr(buf, key);
    if (!p)
        return -1;
    p += strlen(key);
    while (*p == ' ' || *p == '\t')
        p++;
    return strtol(p, NULL, 10);
}

static struct mem_snap read_mem(void) {
    struct mem_snap m = { -1, -1, -1, -1 };
    char buf[16384];
    FILE *f = fopen("/proc/self/status", "r");
    if (f) {
        size_t n = fread(buf, 1, sizeof(buf) - 1, f);
        buf[n] = '\0';
        fclose(f);
        m.vm_size_kb = parse_kb_line(buf, "VmSize:");
        m.vm_rss_kb = parse_kb_line(buf, "VmRSS:");
        m.rss_anon_kb = parse_kb_line(buf, "RssAnon:");
    }
    f = fopen("/proc/self/smaps_rollup", "r");
    if (f) {
        size_t n = fread(buf, 1, sizeof(buf) - 1, f);
        buf[n] = '\0';
        fclose(f);
        m.private_dirty_kb = parse_kb_line(buf, "Private_Dirty:");
    }
    return m;
}

static void print_snap(const char *stage, struct mem_snap base, struct mem_snap cur) {
    printf("%-42s VmSize=%9.1f MiB  VmRSS=%7.2f MiB (%+7.2f MiB)  AnonDirty=%7.2f MiB\n",
           stage,
           (double)cur.vm_size_kb / 1024.0,
           (double)cur.vm_rss_kb / 1024.0,
           (double)(cur.vm_rss_kb - base.vm_rss_kb) / 1024.0,
           (double)cur.private_dirty_kb / 1024.0);
}

/* Probe a single raw zsys_mmap(MAP_NORESERVE) size in a child so OOM/panic is isolated. */
static void probe_size_child(size_t bytes) {
    fflush(stdout);
    int fd[2];
    if (pipe(fd) != 0)
        exit(1);
    pid_t pid = fork();
    if (pid == 0) {
        close(fd[0]);
        dup2(fd[1], 1);
        dup2(fd[1], 2);
        close(fd[1]);
        struct mem_snap b0 = read_mem();
        void *p = zsys_mmap(NULL, bytes, 0x3, 0x02 | 0x20 | 0x4000, -1, 0);
        if (p == (void *)(intptr_t)-1) {
            printf("MAP_FAILED\n");
            fflush(stdout);
            _exit(2);
        }
        struct mem_snap b1 = read_mem();
        ((volatile uint32_t *)p)[0] = 0x55AA55AAU;
        ((volatile uint32_t *)p)[(bytes / 4ULL) - 1ULL] = 0xAA55AA55U;
        struct mem_snap b2 = read_mem();
        printf("OK rss_delta=%+.2f MiB dirty_delta=%+.2f MiB after_2_end_pages=%+.2f MiB\n",
               (double)(b1.vm_rss_kb - b0.vm_rss_kb) / 1024.0,
               (double)(b1.private_dirty_kb - b0.private_dirty_kb) / 1024.0,
               (double)(b2.vm_rss_kb - b0.vm_rss_kb) / 1024.0);
        fflush(stdout);
        _exit(0);
    }
    close(fd[1]);
    char out[1024];
    size_t n = 0;
    ssize_t r;
    while (n < sizeof(out) - 1 && (r = read(fd[0], out + n, sizeof(out) - 1 - n)) > 0)
        n += (size_t)r;
    out[n] = '\0';
    close(fd[0]);
    for (size_t i = 0; i < n; i++)
        if (out[i] == '\n') out[i] = ' ';
    int st = 0;
    waitpid(pid, &st, 0);
    printf("  reserve %9.2f GiB (%13zu B): ", (double)bytes / (1024.0 * 1024.0 * 1024.0), bytes);
    if (WIFEXITED(st) && WEXITSTATUS(st) == 0)
        printf("%s\n", out);
    else if (WIFSIGNALED(st))
        printf("SIGNAL %d (%s)\n", WTERMSIG(st), out);
    else
        printf("EXIT %d (%s)\n", WEXITSTATUS(st), out);
}

static void fault_words(uint32_t *arena, uint32_t start_idx, uint32_t words) {
    for (uint32_t i = 0U; i < words; i += 256U)
        arena[start_idx + i] = 0xA0000000U ^ i;
    if (words > 0U)
        arena[start_idx + words - 1U] = 0xDEADBEEFU;
}

int main(void) {
    printf("=== 1. zsys_mmap(MAP_NORESERVE) reservation sweep (fugc_destructor_heap) ===\n");
    static const size_t sizes[] = {
        512ULL << 20,
        2ULL << 30,
        (8ULL << 30) + 4096ULL,
        16ULL << 30,
        64ULL << 30,
        256ULL << 30,
        1024ULL << 30,
        4096ULL << 30
    };
    for (size_t i = 0; i < sizeof(sizes) / sizeof(sizes[0]); i++)
        probe_size_child(sizes[i]);

    printf("\n=== 2. Full 8 GiB + 4 KiB arena RSS lifecycle & zsys_madvise(MADV_DONTNEED) ===\n");
    struct mem_snap base = read_mem();
    print_snap("0. process baseline", base, base);

    uint32_t *arena = NULL;
    struct anf_state *st = NULL;
    if (anf_arena_init(&arena, &st, ANF_MAX_SLAB_WORDS, ANF_DEFAULT_NURSERY,
                       ANF_DEFAULT_ROOT_CAP) != 0) {
        fprintf(stderr, "8 GiB anf_arena_init failed\n");
        return 1;
    }
    struct mem_snap s_init = read_mem();
    print_snap("1. after 8 GiB + 4 KiB anf_arena_init", base, s_init);

    /* Fault the 4 MiB nursery + 4 KiB guard tail */
    fault_words(arena, st->nursery_base, ANF_DEFAULT_NURSERY + ANF_GUARD_WORDS);
    struct mem_snap s_nurs = read_mem();
    print_snap("2. after faulting 4 MiB nursery", base, s_nurs);

    /* Simulate promoting 64 MiB (16,777,216 words) into major */
    uint32_t words_64m = 16U << 20;
    fault_words(arena, 1U, words_64m);
    st->major_idx = 1U + words_64m;
    st->major_hwm = st->major_idx;
    struct mem_snap s_maj64 = read_mem();
    print_snap("3. after faulting 64 MiB in major", base, s_maj64);

    if (anf_arena_reset(arena, st, 0U) != 0) {
        fprintf(stderr, "anf_arena_reset (64 MiB) failed\n");
        return 1;
    }
    struct mem_snap s_rst64 = read_mem();
    print_snap("4. after MADV_DONTNEED reset (64 MiB)", base, s_rst64);
    if (arena[1] != 0U || arena[words_64m] != 0U) {
        fprintf(stderr, "MADV_DONTNEED did not zero major pages\n");
        return 1;
    }

    /* Simulate promoting 256 MiB (67,108,864 words) into major */
    uint32_t words_256m = 64U << 20;
    fault_words(arena, 1U, words_256m);
    st->major_idx = 1U + words_256m;
    st->major_hwm = st->major_idx;
    struct mem_snap s_maj256 = read_mem();
    print_snap("5. after faulting 256 MiB in major", base, s_maj256);

    if (anf_arena_reset(arena, st, 0U) != 0) {
        fprintf(stderr, "anf_arena_reset (256 MiB) failed\n");
        return 1;
    }
    struct mem_snap s_rst256 = read_mem();
    print_snap("6. after MADV_DONTNEED reset (256 MiB)", base, s_rst256);
    if (arena[1] != 0U || arena[words_256m] != 0U) {
        fprintf(stderr, "MADV_DONTNEED did not zero 256 MiB major pages\n");
        return 1;
    }

    /* Run 5 full FUGC cycles while the 8 GiB arena remains live */
    for (int c = 0; c < 5; c++) {
        void *tmp = malloc(65536);
        ((volatile char *)tmp)[0] = (char)c;
        free(tmp);
        zgc_request_and_wait();
    }
    struct mem_snap s_fugc = read_mem();
    print_snap("7. after 5 FUGC cycles (live 8 GiB arena)", base, s_fugc);

    if (!getenv("FUGC_SCRIBBLE"))
        (void)anf_arena_destroy(arena, st);
    return 0;
}
