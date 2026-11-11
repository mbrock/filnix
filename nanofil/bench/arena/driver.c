// Fil-C driver for nanofil/bench/arena/kernels.ir (compiled by
// nanofil-backend compile-allocated, both checked and check-erased).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>

#define SLAB_BYTES ((1ULL << 33) + 4096ULL)
#define DEFAULT_NURSERY_WORDS (262144U)
#define ROOT_CAP 65536U

struct anf_state {
    uint32_t young_idx;
    uint32_t major_idx;
    uint32_t nursery_base;
    uint32_t nursery_end;
    uint32_t major_limit;
    uint32_t root_sp;
    uint32_t gc_count;
};

extern uint64_t bench_list(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                           uint32_t len, uint32_t rounds);
extern uint64_t bench_term(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                           uint32_t depth, uint32_t rounds);
extern uint64_t bench_avl(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                          uint32_t nkeys, uint32_t rounds);

static void arena_reset(uint32_t *arena, struct anf_state *st, uint32_t nursery_words) {
    if (st->major_idx > 1U) {
        size_t bytes = ((size_t)st->major_idx * 4ULL + 4095ULL) & ~4095ULL;
        madvise(arena, bytes, MADV_DONTNEED);
    }
    st->nursery_end = 1U << 30;
    st->nursery_base = st->nursery_end - nursery_words;
    st->major_limit = st->nursery_base;
    st->young_idx = st->nursery_base;
    st->major_idx = 1U;
    st->root_sp = 0U;
    st->gc_count = 0U;
}

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

int main(int argc, char **argv) {
    const char *which = (argc > 1) ? argv[1] : "all";
    uint32_t scale = (argc > 2) ? (uint32_t)strtoul(argv[2], NULL, 10) : 1U;
    uint32_t nursery_words = (argc > 3) ? (uint32_t)strtoul(argv[3], NULL, 10) : DEFAULT_NURSERY_WORDS;

    uint32_t *arena = mmap(NULL, SLAB_BYTES, PROT_READ | PROT_WRITE,
                           MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (arena == MAP_FAILED) {
        perror("mmap");
        return 1;
    }
    uint32_t *roots = calloc(ROOT_CAP, sizeof(uint32_t));
    struct anf_state st = {0};

    // Entry boundary capability check: touch first & last bytes of arena, roots, st
    // so even in check-erased mode, any invalid/undersized capability passed to
    // the FFI boundary traps before entering the arena kernels.
    arena[0] = 0U;
    arena[(SLAB_BYTES / 4ULL) - 1ULL] = 0U;
    roots[0] = 0U;
    roots[ROOT_CAP - 1U] = 0U;

    if (strcmp(which, "all") == 0 || strcmp(which, "list") == 0) {
        arena_reset(arena, &st, nursery_words);
        uint64_t t0 = now_ns();
        uint64_t res = bench_list(arena, roots, &st, 4096U, 2000U * scale);
        double ms = (double)(now_ns() - t0) / 1e6;
        printf("list_sum\t%llu\t%.3f\tgc=%u\n", (unsigned long long)res, ms, st.gc_count);
    }
    if (strcmp(which, "all") == 0 || strcmp(which, "term") == 0) {
        arena_reset(arena, &st, nursery_words);
        uint64_t t0 = now_ns();
        uint64_t res = bench_term(arena, roots, &st, 8U, 200U * scale);
        double ms = (double)(now_ns() - t0) / 1e6;
        printf("term_eqb\t%llu\t%.3f\tgc=%u\n", (unsigned long long)res, ms, st.gc_count);
    }
    if (strcmp(which, "all") == 0 || strcmp(which, "avl") == 0) {
        arena_reset(arena, &st, nursery_words);
        uint64_t t0 = now_ns();
        uint64_t res = bench_avl(arena, roots, &st, 2048U, 100U * scale);
        double ms = (double)(now_ns() - t0) / 1e6;
        printf("avl\t%llu\t%.3f\tgc=%u\n", (unsigned long long)res, ms, st.gc_count);
    }
    free(roots);
    munmap(arena, SLAB_BYTES);
    return 0;
}
