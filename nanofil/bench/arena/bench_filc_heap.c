// Per-object Fil-C heap (FUGC) and CertiRocq-style -DVERIFFI void* nursery
// baselines on the exact same three workloads.
//   - Default: every constructor node is a malloc() heap object reclaimed
//     concurrently by FUGC (no free(), pure functional semantics).
//   - With -DVERIFFI_NURSERY: every value is `void *`, allocated in a
//     64-bit `void **` nursery slab and evacuated by Cheney copying, so
//     every word store/copy pays Fil-C's payload + aux + store barrier cost.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

static inline uint32_t next_rng(uint32_t x) {
    return x * 1664525U + 1013904223U;
}

static uint64_t now_ns(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint64_t)ts.tv_sec * 1000000000ULL + (uint64_t)ts.tv_nsec;
}

#ifndef VERIFFI_NURSERY

// ---- Mode A: Per-object Fil-C heap structs collected by FUGC ----

struct cons_node {
    uint32_t head;
    struct cons_node *tail;
};

static struct cons_node *list_build(uint32_t n, uint32_t seed) {
    struct cons_node *acc = NULL;
    uint32_t s = seed;
    while (n > 0U) {
        s = next_rng(s);
        struct cons_node *c = malloc(sizeof(struct cons_node));
        c->head = s & 1023U;
        c->tail = acc;
        acc = c;
        n--;
    }
    return acc;
}

static uint32_t list_sum(const struct cons_node *xs, uint32_t acc) {
    while (xs != NULL) {
        acc += xs->head;
        xs = xs->tail;
    }
    return acc;
}

static uint64_t bench_list(uint32_t len, uint32_t rounds) {
    struct cons_node * volatile keep = list_build(len, 42U);
    uint64_t total = 0;
    for (uint32_t r = 0; r < rounds; r++) {
        struct cons_node *xs = list_build(len, r + 1000U);
        uint32_t s1 = list_sum(xs, 0U);
        uint32_t s2 = list_sum(keep, 0U);
        total += (uint64_t)(s1 + s2);
    }
    return total;
}

struct term_list;
struct term {
    uint32_t tag; // 0 = TInt, 1 = TAtom, 2 = TComp
    uint32_t val;
    struct term_list *args;
};
struct term_list {
    struct term *head;
    struct term_list *tail;
};

static struct term_list *mk_tcons(struct term *h, struct term_list *tl) {
    struct term_list *c = malloc(sizeof(struct term_list));
    c->head = h;
    c->tail = tl;
    return c;
}

static struct term *term_build(uint32_t depth, uint32_t seed, uint32_t flip) {
    struct term *t = malloc(sizeof(struct term));
    if (depth == 0U) {
        t->tag = seed & 1U;
        t->val = (seed >> 1) + flip;
        t->args = NULL;
        return t;
    }
    struct term *c0 = term_build(depth - 1U, (seed * 3U + 1U) & 0xFFFFU, 0U);
    struct term *c1 = term_build(depth - 1U, (seed * 3U + 2U) & 0xFFFFU, 0U);
    struct term *c2 = term_build(depth - 1U, (seed * 3U + 3U) & 0xFFFFU, flip);
    t->tag = 2U;
    t->val = seed & 255U;
    t->args = mk_tcons(c0, mk_tcons(c1, mk_tcons(c2, NULL)));
    return t;
}

static int term_eqb(const struct term *a, const struct term *b) {
    if (a->tag != b->tag || a->val != b->val)
        return 0;
    if (a->tag < 2U)
        return 1;
    const struct term_list *xs = a->args;
    const struct term_list *ys = b->args;
    while (xs != NULL && ys != NULL) {
        if (!term_eqb(xs->head, ys->head))
            return 0;
        xs = xs->tail;
        ys = ys->tail;
    }
    return xs == ys;
}

static uint64_t bench_term(uint32_t depth, uint32_t rounds) {
    struct term * volatile base = term_build(depth, 7U, 0U);
    uint64_t total = 0;
    for (uint32_t r = 0; r < rounds; r++) {
        struct term *t = term_build(depth, 7U, r & 1U);
        uint64_t eq1 = term_eqb(base, t) ? 1ULL : 0ULL;
        uint64_t eq2 = term_eqb(t, t) ? 1ULL : 0ULL;
        total = total * 131ULL + eq1 * 17ULL + eq2;
    }
    return total;
}

struct avl_node {
    struct avl_node *left;
    uint32_t key;
    uint32_t val;
    struct avl_node *right;
    uint32_t height;
};

static inline uint32_t avl_h(const struct avl_node *t) {
    return t ? t->height : 0U;
}

static struct avl_node *avl_mk(struct avl_node *l, uint32_t k, uint32_t v, struct avl_node *r) {
    uint32_t hl = avl_h(l), hr = avl_h(r);
    struct avl_node *n = malloc(sizeof(struct avl_node));
    n->left = l;
    n->key = k;
    n->val = v;
    n->right = r;
    n->height = ((hl >= hr) ? hl : hr) + 1U;
    return n;
}

static struct avl_node *avl_bal(struct avl_node *l, uint32_t k, uint32_t v, struct avl_node *r) {
    uint32_t hl = avl_h(l), hr = avl_h(r);
    if (hl > hr + 2U) {
        if (avl_h(l->left) >= avl_h(l->right))
            return avl_mk(l->left, l->key, l->val, avl_mk(l->right, k, v, r));
        struct avl_node *lr = l->right;
        return avl_mk(avl_mk(l->left, l->key, l->val, lr->left), lr->key, lr->val,
                      avl_mk(lr->right, k, v, r));
    } else if (hr > hl + 2U) {
        if (avl_h(r->right) >= avl_h(r->left))
            return avl_mk(avl_mk(l, k, v, r->left), r->key, r->val, r->right);
        struct avl_node *rl = r->left;
        return avl_mk(avl_mk(l, k, v, rl->left), rl->key, rl->val,
                      avl_mk(rl->right, r->key, r->val, r->right));
    }
    return avl_mk(l, k, v, r);
}

static struct avl_node *avl_insert(struct avl_node *t, uint32_t k, uint32_t v) {
    if (!t) {
        struct avl_node *n = malloc(sizeof(struct avl_node));
        n->left = NULL;
        n->key = k;
        n->val = v;
        n->right = NULL;
        n->height = 1U;
        return n;
    }
    if (k == t->key) {
        struct avl_node *n = malloc(sizeof(struct avl_node));
        n->left = t->left;
        n->key = k;
        n->val = v;
        n->right = t->right;
        n->height = t->height;
        return n;
    }
    if (k < t->key)
        return avl_bal(avl_insert(t->left, k, v), t->key, t->val, t->right);
    return avl_bal(t->left, t->key, t->val, avl_insert(t->right, k, v));
}

static uint32_t avl_lookup(const struct avl_node *t, uint32_t k) {
    while (t != NULL) {
        if (k == t->key)
            return t->val;
        t = (k < t->key) ? t->left : t->right;
    }
    return 0U;
}

static struct avl_node *avl_build_n(uint32_t nkeys, uint32_t seed0) {
    uint32_t s = seed0;
    struct avl_node *t = NULL;
    for (uint32_t i = 0; i < nkeys; i++) {
        s = next_rng(s);
        t = avl_insert(t, (s >> 16) & 4095U, i + 1U);
    }
    return t;
}

static uint64_t bench_avl(uint32_t nkeys, uint32_t rounds) {
    struct avl_node * volatile base = avl_build_n(nkeys, 99U);
    uint64_t total = 0;
    for (uint32_t r = 0; r < rounds; r++) {
        struct avl_node *t = avl_build_n(nkeys, r * 977U + 1U);
        uint32_t sum = 0;
        for (uint32_t k = 0; k < 4096U; k++)
            sum += avl_lookup(t, k);
        for (uint32_t k = 0; k < 1024U; k++)
            sum += avl_lookup(base, k * 4U);
        total += (uint64_t)sum;
    }
    return total;
}

int main(int argc, char **argv) {
    const char *which = (argc > 1) ? argv[1] : "all";
    uint32_t scale = (argc > 2) ? (uint32_t)strtoul(argv[2], NULL, 10) : 1U;
    if (strcmp(which, "all") == 0 || strcmp(which, "list") == 0) {
        uint64_t t0 = now_ns();
        uint64_t res = bench_list(4096U, 2000U * scale);
        printf("list_sum\t%llu\t%.3f\n", (unsigned long long)res, (double)(now_ns() - t0) / 1e6);
    }
    if (strcmp(which, "all") == 0 || strcmp(which, "term") == 0) {
        uint64_t t0 = now_ns();
        uint64_t res = bench_term(8U, 200U * scale);
        printf("term_eqb\t%llu\t%.3f\n", (unsigned long long)res, (double)(now_ns() - t0) / 1e6);
    }
    if (strcmp(which, "all") == 0 || strcmp(which, "avl") == 0) {
        uint64_t t0 = now_ns();
        uint64_t res = bench_avl(2048U, 100U * scale);
        printf("avl\t%llu\t%.3f\n", (unsigned long long)res, (double)(now_ns() - t0) / 1e6);
    }
    return 0;
}

#else

// ---- Mode B: CertiRocq-style -DVERIFFI (`typedef void *value;` nursery + Cheney) ----

typedef void *value;
#define V_IMM(x) ((value)(uintptr_t)((((uintptr_t)(x)) << 1) | 1ULL))
#define V_INT(v) (((uintptr_t)(v)) >> 1)
#define V_IS_IMM(v) ((((uintptr_t)(v)) & 1ULL) != 0ULL)
#define V_HDR(arity, ord) ((value)(uintptr_t)((((uintptr_t)(arity)) << 10) | ((uintptr_t)(ord))))
#define V_BROKEN ((value)(uintptr_t)0xFFFFFFFFFFFFFFFFULL)
#define FIELD(v, i) (((value *)(v))[i])
#define HD_VAL(v) (((value *)(v))[-1])

struct vheap {
    value *major;
    size_t major_idx;
    size_t major_cap;
    value *nursery;
    size_t young_idx;
    size_t nursery_cap;
    value *roots;
    size_t root_sp;
};

static value v_evacuate(struct vheap *h, value v) {
    if (V_IS_IMM(v))
        return v;
    value *p = (value *)v;
    if (!(p >= h->nursery && p < h->nursery + h->nursery_cap))
        return v;
    value hd = p[-1];
    if ((uintptr_t)hd == (uintptr_t)V_BROKEN)
        return p[0];
    size_t arity = ((uintptr_t)hd) >> 10;
    value *dst = h->major + h->major_idx + 1;
    h->major_idx += arity + 1;
    dst[-1] = hd;
    for (size_t i = 0; i < arity; i++)
        dst[i] = p[i];
    p[-1] = V_BROKEN;
    p[0] = (value)dst;
    return (value)dst;
}

__attribute__((noinline))
static void v_minor_gc(struct vheap *h) {
    size_t scan = h->major_idx;
    for (size_t r = 0; r < h->root_sp; r++)
        h->roots[r] = v_evacuate(h, h->roots[r]);
    while (scan < h->major_idx) {
        value *obj = h->major + scan + 1;
        size_t arity = ((uintptr_t)obj[-1]) >> 10;
        for (size_t i = 0; i < arity; i++)
            obj[i] = v_evacuate(h, obj[i]);
        scan += arity + 1;
    }
    h->young_idx = 0;
}

static void v_reset(struct vheap *h) {
    h->young_idx = 0;
    h->major_idx = 0;
    h->root_sp = 0;
}

static value v_list_build(struct vheap *h, uint32_t n, uint32_t seed) {
    value acc = V_IMM(0);
    uint32_t s = seed;
    while (n > 0U) {
        if (h->young_idx + 3 > h->nursery_cap) {
            size_t sp = h->root_sp;
            h->roots[sp] = acc;
            h->root_sp = sp + 1;
            v_minor_gc(h);
            acc = h->roots[sp];
            h->root_sp = sp;
        }
        s = next_rng(s);
        value *cell = h->nursery + h->young_idx + 1;
        h->young_idx += 3;
        cell[-1] = V_HDR(2, 0);
        cell[0] = V_IMM(s & 1023U);
        cell[1] = acc;
        acc = (value)cell;
        n--;
    }
    return acc;
}

static uint32_t v_list_sum(value xs, uint32_t acc) {
    while (!V_IS_IMM(xs)) {
        acc += (uint32_t)V_INT(FIELD(xs, 0));
        xs = FIELD(xs, 1);
    }
    return acc;
}

static uint64_t bench_list(struct vheap *h, uint32_t len, uint32_t rounds) {
    value keep = v_list_build(h, len, 42U);
    size_t sp = h->root_sp;
    h->roots[sp] = keep;
    h->root_sp = sp + 1;
    uint64_t total = 0;
    for (uint32_t r = 0; r < rounds; r++) {
        value xs = v_list_build(h, len, r + 1000U);
        uint32_t s1 = v_list_sum(xs, 0U);
        uint32_t s2 = v_list_sum(h->roots[sp], 0U);
        total += (uint64_t)(s1 + s2);
    }
    h->root_sp = sp;
    return total;
}

static value v_term_build(struct vheap *h, uint32_t depth, uint32_t seed, uint32_t flip) {
    if (depth == 0U) {
        if (h->young_idx + 2 > h->nursery_cap)
            v_minor_gc(h);
        value *p = h->nursery + h->young_idx + 1;
        h->young_idx += 2;
        p[-1] = V_HDR(1, seed & 1U);
        p[0] = V_IMM((seed >> 1) + flip);
        return (value)p;
    }
    size_t sp = h->root_sp;
    value c0 = v_term_build(h, depth - 1U, (seed * 3U + 1U) & 0xFFFFU, 0U);
    h->roots[sp] = c0;
    h->root_sp = sp + 1;
    value c1 = v_term_build(h, depth - 1U, (seed * 3U + 2U) & 0xFFFFU, 0U);
    h->roots[sp + 1] = c1;
    h->root_sp = sp + 2;
    value c2 = v_term_build(h, depth - 1U, (seed * 3U + 3U) & 0xFFFFU, flip);
    if (h->young_idx + 12 > h->nursery_cap) {
        h->roots[sp + 2] = c2;
        h->root_sp = sp + 3;
        v_minor_gc(h);
        c2 = h->roots[sp + 2];
    }
    c0 = h->roots[sp];
    c1 = h->roots[sp + 1];
    h->root_sp = sp;
    value *base = h->nursery + h->young_idx;
    h->young_idx += 12;
    base[0] = V_HDR(2, 0); base[1] = c2; base[2] = V_IMM(0);
    value l2 = (value)(base + 1);
    base[3] = V_HDR(2, 0); base[4] = c1; base[5] = l2;
    value l1 = (value)(base + 4);
    base[6] = V_HDR(2, 0); base[7] = c0; base[8] = l1;
    value l0 = (value)(base + 7);
    base[9] = V_HDR(2, 2); base[10] = V_IMM(seed & 255U); base[11] = l0;
    return (value)(base + 10);
}

static int v_term_eqb(value a, value b) {
    uintptr_t ha = ((uintptr_t)HD_VAL(a)) & 255ULL;
    uintptr_t hb = ((uintptr_t)HD_VAL(b)) & 255ULL;
    if (ha != hb || (uintptr_t)FIELD(a, 0) != (uintptr_t)FIELD(b, 0))
        return 0;
    if (ha < 2ULL)
        return 1;
    value xs = FIELD(a, 1);
    value ys = FIELD(b, 1);
    while (!V_IS_IMM(xs) && !V_IS_IMM(ys)) {
        if (!v_term_eqb(FIELD(xs, 0), FIELD(ys, 0)))
            return 0;
        xs = FIELD(xs, 1);
        ys = FIELD(ys, 1);
    }
    return (uintptr_t)xs == (uintptr_t)ys;
}

static uint64_t bench_term(struct vheap *h, uint32_t depth, uint32_t rounds) {
    value base = v_term_build(h, depth, 7U, 0U);
    size_t sp = h->root_sp;
    h->roots[sp] = base;
    h->root_sp = sp + 1;
    uint64_t total = 0;
    for (uint32_t r = 0; r < rounds; r++) {
        value t = v_term_build(h, depth, 7U, r & 1U);
        uint64_t eq1 = v_term_eqb(h->roots[sp], t) ? 1ULL : 0ULL;
        uint64_t eq2 = v_term_eqb(t, t) ? 1ULL : 0ULL;
        total = total * 131ULL + eq1 * 17ULL + eq2;
    }
    h->root_sp = sp;
    return total;
}

static inline uintptr_t v_avl_h(value t) {
    return V_IS_IMM(t) ? 0ULL : V_INT(FIELD(t, 4));
}

static value v_avl_mk(struct vheap *h, value l, value k, value v, value r) {
    uintptr_t hl = v_avl_h(l), hr = v_avl_h(r);
    value *p = h->nursery + h->young_idx + 1;
    h->young_idx += 6;
    p[-1] = V_HDR(5, 0);
    p[0] = l; p[1] = k; p[2] = v; p[3] = r;
    p[4] = V_IMM(((hl >= hr) ? hl : hr) + 1ULL);
    return (value)p;
}

static value v_avl_bal(struct vheap *h, value l, value k, value v, value r) {
    if (h->young_idx + 18 > h->nursery_cap) {
        size_t sp = h->root_sp;
        h->roots[sp] = l; h->roots[sp + 1] = r;
        h->root_sp = sp + 2;
        v_minor_gc(h);
        l = h->roots[sp]; r = h->roots[sp + 1];
        h->root_sp = sp;
    }
    uintptr_t hl = v_avl_h(l), hr = v_avl_h(r);
    if (hl > hr + 2ULL) {
        value ll = FIELD(l, 0), lk = FIELD(l, 1), lv = FIELD(l, 2), lr = FIELD(l, 3);
        if (v_avl_h(ll) >= v_avl_h(lr))
            return v_avl_mk(h, ll, lk, lv, v_avl_mk(h, lr, k, v, r));
        return v_avl_mk(h, v_avl_mk(h, ll, lk, lv, FIELD(lr, 0)), FIELD(lr, 1), FIELD(lr, 2),
                        v_avl_mk(h, FIELD(lr, 3), k, v, r));
    } else if (hr > hl + 2ULL) {
        value rl = FIELD(r, 0), rk = FIELD(r, 1), rv = FIELD(r, 2), rr = FIELD(r, 3);
        if (v_avl_h(rr) >= v_avl_h(rl))
            return v_avl_mk(h, v_avl_mk(h, l, k, v, rl), rk, rv, rr);
        return v_avl_mk(h, v_avl_mk(h, l, k, v, FIELD(rl, 0)), FIELD(rl, 1), FIELD(rl, 2),
                        v_avl_mk(h, FIELD(rl, 3), rk, rv, rr));
    }
    return v_avl_mk(h, l, k, v, r);
}

static value v_avl_insert(struct vheap *h, value t, value k, value v) {
    if (V_IS_IMM(t)) {
        if (h->young_idx + 6 > h->nursery_cap)
            v_minor_gc(h);
        return v_avl_mk(h, V_IMM(0), k, v, V_IMM(0));
    }
    value l = FIELD(t, 0), nk = FIELD(t, 1), nv = FIELD(t, 2), r = FIELD(t, 3), ht = FIELD(t, 4);
    if ((uintptr_t)k == (uintptr_t)nk) {
        if (h->young_idx + 6 > h->nursery_cap) {
            size_t sp = h->root_sp;
            h->roots[sp] = l; h->roots[sp + 1] = r;
            h->root_sp = sp + 2;
            v_minor_gc(h);
            l = h->roots[sp]; r = h->roots[sp + 1];
            h->root_sp = sp;
        }
        value *p = h->nursery + h->young_idx + 1;
        h->young_idx += 6;
        p[-1] = V_HDR(5, 0);
        p[0] = l; p[1] = k; p[2] = v; p[3] = r; p[4] = ht;
        return (value)p;
    }
    size_t sp = h->root_sp;
    if ((uintptr_t)k < (uintptr_t)nk) {
        h->roots[sp] = r; h->root_sp = sp + 1;
        value nl = v_avl_insert(h, l, k, v);
        r = h->roots[sp]; h->root_sp = sp;
        return v_avl_bal(h, nl, nk, nv, r);
    } else {
        h->roots[sp] = l; h->root_sp = sp + 1;
        value nr = v_avl_insert(h, r, k, v);
        l = h->roots[sp]; h->root_sp = sp;
        return v_avl_bal(h, l, nk, nv, nr);
    }
}

static uint32_t v_avl_lookup(value t, value k) {
    while (!V_IS_IMM(t)) {
        value nk = FIELD(t, 1);
        if ((uintptr_t)k == (uintptr_t)nk)
            return (uint32_t)V_INT(FIELD(t, 2));
        t = ((uintptr_t)k < (uintptr_t)nk) ? FIELD(t, 0) : FIELD(t, 3);
    }
    return 0U;
}

static value v_avl_build_n(struct vheap *h, uint32_t nkeys, uint32_t seed0) {
    uint32_t s = seed0;
    value t = V_IMM(0);
    size_t sp = h->root_sp;
    for (uint32_t i = 0; i < nkeys; i++) {
        s = next_rng(s);
        h->roots[sp] = t; h->root_sp = sp + 1;
        t = v_avl_insert(h, t, V_IMM((s >> 16) & 4095U), V_IMM(i + 1U));
    }
    h->root_sp = sp;
    return t;
}

static uint64_t bench_avl(struct vheap *h, uint32_t nkeys, uint32_t rounds) {
    value base = v_avl_build_n(h, nkeys, 99U);
    size_t sp = h->root_sp;
    h->roots[sp] = base; h->root_sp = sp + 1;
    uint64_t total = 0;
    for (uint32_t r = 0; r < rounds; r++) {
        value t = v_avl_build_n(h, nkeys, r * 977U + 1U);
        uint32_t sum = 0;
        for (uint32_t k = 0; k < 4096U; k++)
            sum += v_avl_lookup(t, V_IMM(k));
        value b = h->roots[sp];
        for (uint32_t k = 0; k < 1024U; k++)
            sum += v_avl_lookup(b, V_IMM(k * 4U));
        total += (uint64_t)sum;
    }
    h->root_sp = sp;
    return total;
}

int main(int argc, char **argv) {
    const char *which = (argc > 1) ? argv[1] : "all";
    uint32_t scale = (argc > 2) ? (uint32_t)strtoul(argv[2], NULL, 10) : 1U;
    struct vheap h = {0};
    h.nursery_cap = 262144;
    h.major_cap = 16 * 1024 * 1024;
    h.nursery = calloc(h.nursery_cap, sizeof(value));
    h.major = calloc(h.major_cap, sizeof(value));
    h.roots = calloc(65536, sizeof(value));
    if (strcmp(which, "all") == 0 || strcmp(which, "list") == 0) {
        v_reset(&h);
        uint64_t t0 = now_ns();
        uint64_t res = bench_list(&h, 4096U, 2000U * scale);
        printf("list_sum\t%llu\t%.3f\n", (unsigned long long)res, (double)(now_ns() - t0) / 1e6);
    }
    if (strcmp(which, "all") == 0 || strcmp(which, "term") == 0) {
        v_reset(&h);
        uint64_t t0 = now_ns();
        uint64_t res = bench_term(&h, 8U, 200U * scale);
        printf("term_eqb\t%llu\t%.3f\n", (unsigned long long)res, (double)(now_ns() - t0) / 1e6);
    }
    if (strcmp(which, "all") == 0 || strcmp(which, "avl") == 0) {
        v_reset(&h);
        uint64_t t0 = now_ns();
        uint64_t res = bench_avl(&h, 2048U, 100U * scale);
        printf("avl\t%llu\t%.3f\n", (unsigned long long)res, (double)(now_ns() - t0) / 1e6);
    }
    free(h.roots);
    free(h.major);
    free(h.nursery);
    return 0;
}
#endif
