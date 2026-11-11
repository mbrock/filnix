// C reference over the 32-bit w arena (compiled by both native clang -O2
// and filcc -O2 to measure LLVM+FilPizlonator on 32-bit arena C code).
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <time.h>

#define SLAB_BYTES ((1ULL << 33) + 4096ULL)
#define DEFAULT_NURSERY_WORDS (262144U) // 1 MiB nursery window
#define MAJOR_LIMIT_WORDS ((1U << 31) - DEFAULT_NURSERY_WORDS - 1024U)
#define ROOT_CAP 65536U

#define TAG_INT(v) ((((uint32_t)(v)) << 1) | 1U)
#define UNTAG_INT(w) ((w) >> 1)
#define HDR(arity, st, ord) ((((uint32_t)(arity)) << 10) | (((uint32_t)(st)) << 8) | ((uint32_t)(ord)))

struct anf_state {
    uint32_t young_idx;
    uint32_t major_idx;
    uint32_t nursery_base;
    uint32_t nursery_end;
    uint32_t major_limit;
    uint32_t root_sp;
    uint32_t gc_count;
};

static inline uint32_t next_rng(uint32_t x) {
    return x * 1664525U + 1013904223U;
}

static uint32_t evacuate_word(uint32_t *arena, struct anf_state *st, uint32_t w) {
    if (w & 1U)
        return w;
    uint32_t idx = w >> 1;
    if (idx < st->nursery_base)
        return w;
    uint32_t hdr = arena[idx];
    if (hdr == 0xFFFFFFFFU)
        return arena[idx + 1U] << 1;
    uint32_t arity = hdr >> 10;
    uint32_t dst = st->major_idx;
    if (dst + arity + 1U > st->major_limit) {
        fprintf(stderr, "arena major overflow\n");
        abort();
    }
    st->major_idx = dst + arity + 1U;
    arena[dst] = hdr;
    for (uint32_t i = 1U; i <= arity; i++)
        arena[dst + i] = arena[idx + i];
    arena[idx] = 0xFFFFFFFFU;
    arena[idx + 1U] = dst;
    return dst << 1;
}

__attribute__((noinline))
static void minor_gc(uint32_t *arena, uint32_t *roots, struct anf_state *st) {
    uint32_t scan = st->major_idx;
    for (uint32_t r = 0; r < st->root_sp; r++)
        roots[r] = evacuate_word(arena, st, roots[r]);
    while (scan < st->major_idx) {
        uint32_t hdr = arena[scan];
        uint32_t arity = hdr >> 10;
        if ((hdr & 0x300U) == 0U) {
            for (uint32_t i = 1U; i <= arity; i++)
                arena[scan + i] = evacuate_word(arena, st, arena[scan + i]);
        }
        scan += arity + 1U;
    }
    st->young_idx = st->nursery_base;
    st->gc_count++;
}

static void arena_reset(uint32_t *arena, struct anf_state *st, uint32_t nursery_words) {
    if (st->major_idx > 1U) {
        size_t bytes = ((size_t)st->major_idx * 4ULL + 4095ULL) & ~4095ULL;
        madvise(arena, bytes, MADV_DONTNEED);
    }
    st->nursery_end = 1U << 30; // 4 GiB word mark (plenty of room, well below 2^31)
    st->nursery_base = st->nursery_end - nursery_words;
    st->major_limit = st->nursery_base;
    st->young_idx = st->nursery_base;
    st->major_idx = 1U; // word 0 reserved
    st->root_sp = 0U;
    st->gc_count = 0U;
}

// 1. list_build and list_sum
static uint32_t list_build(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                           uint32_t n, uint32_t seed) {
    uint32_t acc = 1U; // Nil
    uint32_t s = seed;
    uint32_t yg = st->young_idx;
    uint32_t ne = st->nursery_end;
    while (n > 0U) {
        if (yg + 3U > ne) {
            st->young_idx = yg;
            uint32_t sp = st->root_sp;
            roots[sp] = acc;
            st->root_sp = sp + 1U;
            minor_gc(arena, roots, st);
            acc = roots[sp];
            st->root_sp = sp;
            yg = st->young_idx;
        }
        s = next_rng(s);
        uint32_t v = TAG_INT(s & 1023U);
        arena[yg] = HDR(2, 0, 0);
        arena[yg + 1U] = v;
        arena[yg + 2U] = acc;
        acc = yg << 1;
        yg += 3U;
        n--;
    }
    st->young_idx = yg;
    return acc;
}

static uint32_t list_sum(const uint32_t *arena, uint32_t xs, uint32_t acc) {
    while ((xs & 1U) == 0U) {
        uint32_t idx = xs >> 1;
        uint32_t h = arena[idx + 1U];
        xs = arena[idx + 2U];
        acc = acc + (h - 1U);
    }
    return acc;
}

static uint64_t bench_list(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                           uint32_t len, uint32_t rounds) {
    uint32_t keep = list_build(arena, roots, st, len, 42U);
    uint32_t sp = st->root_sp;
    roots[sp] = keep;
    st->root_sp = sp + 1U;
    uint64_t total = 0;
    for (uint32_t r = 0; r < rounds; r++) {
        uint32_t xs = list_build(arena, roots, st, len, r + 1000U);
        uint32_t s1 = list_sum(arena, xs, 1U) >> 1;
        uint32_t s2 = list_sum(arena, roots[sp], 1U) >> 1;
        total += (uint64_t)(s1 + s2);
    }
    st->root_sp = sp;
    return total;
}

// 2. term_build and term_eqb
static uint32_t term_build(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                           uint32_t depth, uint32_t seed, uint32_t flip) {
    if (depth == 0U) {
        if (st->young_idx + 2U > st->nursery_end)
            minor_gc(arena, roots, st);
        uint32_t yg = st->young_idx;
        uint32_t ord = seed & 1U;
        uint32_t payload = TAG_INT((seed >> 1) + flip);
        arena[yg] = HDR(1, 0, ord);
        arena[yg + 1U] = payload;
        st->young_idx = yg + 2U;
        return yg << 1;
    }
    uint32_t s0 = (seed * 3U + 1U) & 0xFFFFU;
    uint32_t s1 = (seed * 3U + 2U) & 0xFFFFU;
    uint32_t s2 = (seed * 3U + 3U) & 0xFFFFU;
    uint32_t sp = st->root_sp;
    uint32_t c0 = term_build(arena, roots, st, depth - 1U, s0, 0U);
    roots[sp] = c0;
    st->root_sp = sp + 1U;
    uint32_t c1 = term_build(arena, roots, st, depth - 1U, s1, 0U);
    roots[sp + 1U] = c1;
    st->root_sp = sp + 2U;
    uint32_t c2 = term_build(arena, roots, st, depth - 1U, s2, flip);
    if (st->young_idx + 12U > st->nursery_end) {
        roots[sp + 2U] = c2;
        st->root_sp = sp + 3U;
        minor_gc(arena, roots, st);
        c2 = roots[sp + 2U];
    }
    c0 = roots[sp];
    c1 = roots[sp + 1U];
    st->root_sp = sp;
    uint32_t yg = st->young_idx;
    // l2 = Cons(c2, TNil)
    arena[yg] = HDR(2, 0, 0);
    arena[yg + 1U] = c2;
    arena[yg + 2U] = 1U;
    uint32_t l2 = yg << 1;
    // l1 = Cons(c1, l2)
    arena[yg + 3U] = HDR(2, 0, 0);
    arena[yg + 4U] = c1;
    arena[yg + 5U] = l2;
    uint32_t l1 = (yg + 3U) << 1;
    // l0 = Cons(c0, l1)
    arena[yg + 6U] = HDR(2, 0, 0);
    arena[yg + 7U] = c0;
    arena[yg + 8U] = l1;
    uint32_t l0 = (yg + 6U) << 1;
    // TComp(seed & 255, l0)
    arena[yg + 9U] = HDR(2, 0, 2);
    arena[yg + 10U] = TAG_INT(seed & 255U);
    arena[yg + 11U] = l0;
    st->young_idx = yg + 12U;
    return (yg + 9U) << 1;
}

static uint32_t term_eqb(const uint32_t *arena, uint32_t a, uint32_t b) {
    uint32_t ia = a >> 1;
    uint32_t ib = b >> 1;
    uint32_t ha = arena[ia] & 255U;
    uint32_t hb = arena[ib] & 255U;
    if (ha != hb)
        return 1U; // false
    if (ha < 2U)
        return (arena[ia + 1U] == arena[ib + 1U]) ? 3U : 1U;
    if (arena[ia + 1U] != arena[ib + 1U])
        return 1U;
    uint32_t xs = arena[ia + 2U];
    uint32_t ys = arena[ib + 2U];
    while ((xs & 1U) == 0U && (ys & 1U) == 0U) {
        uint32_t ix = xs >> 1;
        uint32_t iy = ys >> 1;
        if (term_eqb(arena, arena[ix + 1U], arena[iy + 1U]) == 1U)
            return 1U;
        xs = arena[ix + 2U];
        ys = arena[iy + 2U];
    }
    return (xs == ys) ? 3U : 1U;
}

static uint64_t bench_term(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                           uint32_t depth, uint32_t rounds) {
    uint32_t base = term_build(arena, roots, st, depth, 7U, 0U);
    uint32_t sp = st->root_sp;
    roots[sp] = base;
    st->root_sp = sp + 1U;
    uint64_t total = 0;
    for (uint32_t r = 0; r < rounds; r++) {
        uint32_t flip = r & 1U;
        uint32_t t = term_build(arena, roots, st, depth, 7U, flip);
        uint64_t eq1 = (term_eqb(arena, roots[sp], t) == 3U) ? 1ULL : 0ULL;
        uint64_t eq2 = (term_eqb(arena, t, t) == 3U) ? 1ULL : 0ULL;
        total = total * 131ULL + eq1 * 17ULL + eq2;
    }
    st->root_sp = sp;
    return total;
}

// 3. Persistent AVL map (Node(l, k, v, r, h) = 6 words)
static inline uint32_t avl_height(const uint32_t *arena, uint32_t t) {
    if (t & 1U)
        return TAG_INT(0);
    return arena[(t >> 1) + 5U];
}

static inline uint32_t avl_alloc_node(uint32_t *arena, struct anf_state *st,
                                      uint32_t l, uint32_t k, uint32_t v, uint32_t r) {
    uint32_t hl = avl_height(arena, l) >> 1;
    uint32_t hr = avl_height(arena, r) >> 1;
    uint32_t h = ((hl >= hr) ? hl : hr) + 1U;
    uint32_t yg = st->young_idx;
    arena[yg] = HDR(5, 0, 0);
    arena[yg + 1U] = l;
    arena[yg + 2U] = k;
    arena[yg + 3U] = v;
    arena[yg + 4U] = r;
    arena[yg + 5U] = TAG_INT(h);
    st->young_idx = yg + 6U;
    return yg << 1;
}

static uint32_t avl_bal(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                        uint32_t l, uint32_t k, uint32_t v, uint32_t r) {
    // At most 3 nodes = 18 words allocated across any rotation.
    if (st->young_idx + 18U > st->nursery_end) {
        uint32_t sp = st->root_sp;
        roots[sp] = l;
        roots[sp + 1U] = r;
        st->root_sp = sp + 2U;
        minor_gc(arena, roots, st);
        l = roots[sp];
        r = roots[sp + 1U];
        st->root_sp = sp;
    }
    uint32_t hl = avl_height(arena, l) >> 1;
    uint32_t hr = avl_height(arena, r) >> 1;
    if (hl > hr + 2U) {
        uint32_t il = l >> 1;
        uint32_t ll = arena[il + 1U], lk = arena[il + 2U], lv = arena[il + 3U], lr = arena[il + 4U];
        if ((avl_height(arena, ll) >> 1) >= (avl_height(arena, lr) >> 1)) {
            uint32_t nr = avl_alloc_node(arena, st, lr, k, v, r);
            return avl_alloc_node(arena, st, ll, lk, lv, nr);
        } else {
            uint32_t ilr = lr >> 1;
            uint32_t lrl = arena[ilr + 1U], lrk = arena[ilr + 2U], lrv = arena[ilr + 3U], lrr = arena[ilr + 4U];
            uint32_t nl = avl_alloc_node(arena, st, ll, lk, lv, lrl);
            uint32_t nr = avl_alloc_node(arena, st, lrr, k, v, r);
            return avl_alloc_node(arena, st, nl, lrk, lrv, nr);
        }
    } else if (hr > hl + 2U) {
        uint32_t ir = r >> 1;
        uint32_t rl = arena[ir + 1U], rk = arena[ir + 2U], rv = arena[ir + 3U], rr = arena[ir + 4U];
        if ((avl_height(arena, rr) >> 1) >= (avl_height(arena, rl) >> 1)) {
            uint32_t nl = avl_alloc_node(arena, st, l, k, v, rl);
            return avl_alloc_node(arena, st, nl, rk, rv, rr);
        } else {
            uint32_t irl = rl >> 1;
            uint32_t rll = arena[irl + 1U], rlk = arena[irl + 2U], rlv = arena[irl + 3U], rlr = arena[irl + 4U];
            uint32_t nl = avl_alloc_node(arena, st, l, k, v, rll);
            uint32_t nr = avl_alloc_node(arena, st, rlr, rk, rv, rr);
            return avl_alloc_node(arena, st, nl, rlk, rlv, nr);
        }
    }
    return avl_alloc_node(arena, st, l, k, v, r);
}

static uint32_t avl_insert(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                           uint32_t t, uint32_t k, uint32_t v) {
    if (t & 1U) {
        if (st->young_idx + 6U > st->nursery_end)
            minor_gc(arena, roots, st);
        uint32_t yg = st->young_idx;
        arena[yg] = HDR(5, 0, 0);
        arena[yg + 1U] = 1U;
        arena[yg + 2U] = k;
        arena[yg + 3U] = v;
        arena[yg + 4U] = 1U;
        arena[yg + 5U] = TAG_INT(1);
        st->young_idx = yg + 6U;
        return yg << 1;
    }
    uint32_t idx = t >> 1;
    uint32_t l = arena[idx + 1U];
    uint32_t nk = arena[idx + 2U];
    uint32_t nv = arena[idx + 3U];
    uint32_t r = arena[idx + 4U];
    uint32_t h = arena[idx + 5U];
    if (k == nk) {
        if (st->young_idx + 6U > st->nursery_end) {
            uint32_t sp = st->root_sp;
            roots[sp] = l;
            roots[sp + 1U] = r;
            st->root_sp = sp + 2U;
            minor_gc(arena, roots, st);
            l = roots[sp];
            r = roots[sp + 1U];
            st->root_sp = sp;
        }
        uint32_t yg = st->young_idx;
        arena[yg] = HDR(5, 0, 0);
        arena[yg + 1U] = l;
        arena[yg + 2U] = k;
        arena[yg + 3U] = v;
        arena[yg + 4U] = r;
        arena[yg + 5U] = h;
        st->young_idx = yg + 6U;
        return yg << 1;
    }
    uint32_t sp = st->root_sp;
    if (k < nk) {
        roots[sp] = r;
        st->root_sp = sp + 1U;
        uint32_t nl = avl_insert(arena, roots, st, l, k, v);
        r = roots[sp];
        st->root_sp = sp;
        return avl_bal(arena, roots, st, nl, nk, nv, r);
    } else {
        roots[sp] = l;
        st->root_sp = sp + 1U;
        uint32_t nr = avl_insert(arena, roots, st, r, k, v);
        l = roots[sp];
        st->root_sp = sp;
        return avl_bal(arena, roots, st, l, nk, nv, nr);
    }
}

static uint32_t avl_lookup(const uint32_t *arena, uint32_t t, uint32_t k) {
    while ((t & 1U) == 0U) {
        uint32_t idx = t >> 1;
        uint32_t nk = arena[idx + 2U];
        if (k == nk)
            return arena[idx + 3U];
        t = (k < nk) ? arena[idx + 1U] : arena[idx + 4U];
    }
    return TAG_INT(0);
}

static uint32_t avl_build_n(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                            uint32_t nkeys, uint32_t seed0) {
    uint32_t s = seed0;
    uint32_t t = 1U;
    uint32_t sp = st->root_sp;
    for (uint32_t i = 0; i < nkeys; i++) {
        s = next_rng(s);
        uint32_t k = TAG_INT((s >> 16) & 4095U);
        uint32_t v = TAG_INT(i + 1U);
        roots[sp] = t;
        st->root_sp = sp + 1U;
        t = avl_insert(arena, roots, st, t, k, v);
    }
    st->root_sp = sp;
    return t;
}

static uint64_t bench_avl(uint32_t *arena, uint32_t *roots, struct anf_state *st,
                          uint32_t nkeys, uint32_t rounds) {
    uint32_t base = avl_build_n(arena, roots, st, nkeys, 99U);
    uint32_t sp = st->root_sp;
    roots[sp] = base;
    st->root_sp = sp + 1U;
    uint64_t total = 0;
    for (uint32_t r = 0; r < rounds; r++) {
        uint32_t t = avl_build_n(arena, roots, st, nkeys, r * 977U + 1U);
        uint32_t sum = 0;
        for (uint32_t k = 0; k < 4096U; k++)
            sum += avl_lookup(arena, t, TAG_INT(k)) >> 1;
        uint32_t b = roots[sp];
        for (uint32_t k = 0; k < 1024U; k++)
            sum += avl_lookup(arena, b, TAG_INT(k * 4U)) >> 1;
        total += (uint64_t)sum;
    }
    st->root_sp = sp;
    return total;
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
