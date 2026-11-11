#include "anf_arena.h"

void *zsys_mmap(void *addr, size_t len, int prot, int flags, int fd, long off);
int zsys_munmap(void *addr, size_t len);
int zsys_madvise(void *addr, size_t len, int advice);

#define ANF_PROT_RW       (0x1 | 0x2)
#define ANF_MAP_NORESERVE (0x02 | 0x20 | 0x4000)
#define ANF_MADV_DONTNEED 4

/* Not inlined: clang -O2 drops the alloca of an inlined copy, and the
   bound tests that call it then fall through. */
__attribute__((noinline)) void anf_oom(void) {
    volatile char *p = (volatile char *)__builtin_alloca((1ULL << 48) - 1ULL);
    *p = 0;
}

int anf_arena_init(uint32_t **arena_out, struct anf_state **st_out,
                   uint32_t slab_words, uint32_t nursery_words, uint32_t root_cap) {
    if (!arena_out || !st_out || nursery_words < 16U ||
        slab_words <= nursery_words + 1U || slab_words > ANF_MAX_SLAB_WORDS)
        return -1;
    uint64_t slab_bytes = ((uint64_t)slab_words * 4ULL) + ((uint64_t)ANF_GUARD_WORDS * 4ULL);
    uint64_t state_bytes = sizeof(struct anf_state) + ((uint64_t)root_cap * 4ULL);
    state_bytes = (state_bytes + 4095ULL) & ~4095ULL;
    void *ap = zsys_mmap(NULL, (size_t)slab_bytes, ANF_PROT_RW, ANF_MAP_NORESERVE, -1, 0);
    if (ap == (void *)(intptr_t)-1)
        return -1;
    void *sp = zsys_mmap(NULL, (size_t)state_bytes, ANF_PROT_RW, ANF_MAP_NORESERVE, -1, 0);
    if (sp == (void *)(intptr_t)-1) {
        zsys_munmap(ap, (size_t)slab_bytes);
        return -1;
    }
    struct anf_state *st = (struct anf_state *)sp;
    uint32_t nb = slab_words - nursery_words;
    st->young_idx = nb;
    st->major_idx = 1U;
    st->nursery_base = nb;
    st->nursery_end = slab_words;
    st->major_limit = nb;
    st->root_sp = 0U;
    st->root_cap = root_cap;
    st->major_hwm = 1U;
    st->slab_bytes = slab_bytes;
    st->state_bytes = state_bytes;
    st->gc_count = 0ULL;
    st->promoted_words = 0ULL;
    *arena_out = (uint32_t *)ap;
    *st_out = st;
    return 0;
}

int anf_arena_reset(uint32_t *arena, struct anf_state *st, uint32_t madvise_threshold_words) {
    st->young_idx = st->nursery_base;
    st->major_idx = 1U;
    st->root_sp = 0U;
    if (st->major_hwm > 1U && st->major_hwm > madvise_threshold_words) {
        size_t major_page_limit = ((size_t)st->nursery_base * 4ULL) & ~(size_t)4095U;
        size_t release_bytes = ((size_t)st->major_hwm * 4ULL + 4095ULL) & ~(size_t)4095U;
        if (release_bytes > major_page_limit)
            release_bytes = major_page_limit;
        if (release_bytes > 0U && zsys_madvise(arena, release_bytes, ANF_MADV_DONTNEED) != 0)
            return -1;
        st->major_hwm = 1U;
    }
    return 0;
}

int anf_arena_rewind(uint32_t *arena, struct anf_state *st, uint32_t mark,
                     uint32_t madvise_threshold_words) {
    if (mark < 1U || mark > st->major_idx)
        return -1;
    st->young_idx = st->nursery_base;
    st->major_idx = mark;
    st->root_sp = 0U;
    if (st->major_hwm > mark && st->major_hwm - mark > madvise_threshold_words) {
        size_t lo = ((size_t)mark * 4ULL + 4095ULL) & ~(size_t)4095U;
        size_t hi = ((size_t)st->major_hwm * 4ULL + 4095ULL) & ~(size_t)4095U;
        size_t major_page_limit = ((size_t)st->nursery_base * 4ULL) & ~(size_t)4095U;
        if (hi > major_page_limit)
            hi = major_page_limit;
        if (hi > lo && zsys_madvise((uint8_t *)arena + lo, hi - lo, ANF_MADV_DONTNEED) != 0)
            return -1;
        st->major_hwm = mark;
    }
    return 0;
}

int anf_arena_destroy(uint32_t *arena, struct anf_state *st) {
    int r1 = arena ? zsys_munmap(arena, (size_t)st->slab_bytes) : 0;
    int r2 = st ? zsys_munmap(st, (size_t)st->state_bytes) : 0;
    return (r1 != 0 || r2 != 0) ? -1 : 0;
}

static uint32_t evacuate_word(uint32_t *arena, struct anf_state *st, uint32_t w) {
    if (w & 1U)
        return w;
    uint32_t idx = w >> 1;
    if (idx < st->nursery_base)
        return w;
    uint32_t hdr = arena[idx];
    if (hdr == ANF_FWD_HDR)
        return arena[idx + 1U] << 1;
    uint32_t arity = hdr >> 10;
    uint32_t len = arity + 1U;
    if (len > st->major_limit - st->major_idx)
        anf_oom();
    uint32_t dst = st->major_idx;
    st->major_idx = dst + len;
    arena[dst] = hdr;
    for (uint32_t i = 1U; i <= arity; i++)
        arena[dst + i] = arena[idx + i];
    arena[idx] = ANF_FWD_HDR;
    arena[idx + 1U] = dst;
    return dst << 1;
}

void anf_minor_gc(uint32_t *arena, uint32_t *roots, struct anf_state *st) {
    uint32_t start = st->major_idx;
    uint32_t scan = start;
    for (uint32_t r = 0U; r < st->root_sp; r++)
        roots[r] = evacuate_word(arena, st, roots[r]);
    while (scan < st->major_idx) {
        uint32_t hdr = arena[scan];
        uint32_t arity = hdr >> 10;
        if (ANF_HDR_ST(hdr) == ANF_ST_SCAN) {
            for (uint32_t i = 1U; i <= arity; i++)
                arena[scan + i] = evacuate_word(arena, st, arena[scan + i]);
        }
        scan += arity + 1U;
    }
    if (st->major_idx > st->major_hwm)
        st->major_hwm = st->major_idx;
    st->promoted_words += (uint64_t)(st->major_idx - start);
    st->gc_count += 1ULL;
    st->young_idx = st->nursery_base;
}

static uint32_t reserve_scratch(uint32_t *arena, struct anf_state *st,
                                uint32_t words, int *in_major) {
    if (words < 2U || words > ANF_MAX_ARITY + 2U)
        anf_oom();
    if (words <= st->nursery_end - st->young_idx) {
        *in_major = 0;
        return st->young_idx;
    }
    anf_minor_gc(arena, anf_roots(st), st);
    if (words <= st->nursery_end - st->nursery_base) {
        *in_major = 0;
        return st->young_idx;
    }
    if (words > st->major_limit - st->major_idx)
        anf_oom();
    *in_major = 1;
    return st->major_idx;
}

static void commit_scratch(struct anf_state *st, int in_major, uint32_t used) {
    if (in_major) {
        st->major_idx += used;
        if (st->major_idx > st->major_hwm)
            st->major_hwm = st->major_idx;
    } else {
        st->young_idx += used;
    }
}

uint32_t anf_alloc_words(uint32_t *arena, struct anf_state *st, uint32_t words) {
    if (words < 2U || words - 1U > ANF_MAX_ARITY)
        anf_oom();
    int in_major = 0;
    uint32_t dst = reserve_scratch(arena, st, words, &in_major);
    commit_scratch(st, in_major, words);
    return dst;
}

void anf_root_push(struct anf_state *st, uint32_t w) {
    if (st->root_sp >= st->root_cap)
        anf_oom();
    anf_roots(st)[st->root_sp++] = w;
}

uint32_t anf_root_pop(struct anf_state *st) {
    if (st->root_sp == 0U)
        anf_oom();
    return anf_roots(st)[--st->root_sp];
}

uint32_t *anf_root_frame(struct anf_state *st, uint32_t n) {
    if (n > st->root_cap - st->root_sp)
        anf_oom();
    uint32_t *base = anf_roots(st) + st->root_sp;
    st->root_sp += n;
    return base;
}

uint32_t anf_bytes_from_buf(uint32_t *arena, struct anf_state *st,
                            const uint8_t *buf, uint32_t len) {
    if (len > (ANF_MAX_ARITY - 1U) * 4U)
        anf_oom();
    uint32_t data_words = (len + 3U) >> 2;
    uint32_t arity = 1U + data_words;
    uint32_t idx = anf_alloc_words(arena, st, 1U + arity);
    arena[idx] = ANF_HDR(arity, ANF_ST_BYTES, 0U);
    arena[idx + 1U] = len;
    if (data_words > 0U)
        arena[idx + 1U + data_words] = 0U;
    uint8_t *dst = (uint8_t *)(arena + idx + 2U);
    for (uint32_t i = 0U; i < len; i++)
        dst[i] = buf[i];
    return ANF_BOX(idx);
}

uint32_t anf_bytes_len(const uint32_t *arena, uint32_t s) {
    return arena[ANF_IDX(s) + 1U];
}

uint32_t anf_bytes_get(const uint32_t *arena, uint32_t s, uint32_t i) {
    uint32_t idx = ANF_IDX(s);
    if (i >= arena[idx + 1U])
        anf_oom();
    const uint8_t *p = (const uint8_t *)(arena + idx + 2U);
    return ANF_IMM(p[i]);
}

void anf_bytes_copy_out(const uint32_t *arena, uint32_t s, uint8_t *dst) {
    uint32_t idx = ANF_IDX(s);
    uint32_t len = arena[idx + 1U];
    const uint8_t *src = (const uint8_t *)(arena + idx + 2U);
    for (uint32_t i = 0U; i < len; i++)
        dst[i] = src[i];
}

int anf_bytes_cmp(const uint32_t *arena, uint32_t a, uint32_t b) {
    if (a == b)
        return 0;
    uint32_t ia = ANF_IDX(a), ib = ANF_IDX(b);
    uint32_t la = arena[ia + 1U], lb = arena[ib + 1U];
    uint32_t n = la < lb ? la : lb;
    const uint8_t *pa = (const uint8_t *)(arena + ia + 2U);
    const uint8_t *pb = (const uint8_t *)(arena + ib + 2U);
    for (uint32_t i = 0U; i < n; i++) {
        if (pa[i] != pb[i])
            return pa[i] < pb[i] ? -1 : 1;
    }
    return (la > lb) - (la < lb);
}

uint32_t anf_bytes_concat(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) {
    uint32_t la = anf_bytes_len(arena, a);
    uint32_t lb = anf_bytes_len(arena, b);
    if (lb > (ANF_MAX_ARITY - 1U) * 4U - la)
        anf_oom();
    uint32_t len = la + lb;
    uint32_t data_words = (len + 3U) >> 2;
    uint32_t arity = 1U + data_words;
    anf_root_push(st, a);
    anf_root_push(st, b);
    uint32_t idx = anf_alloc_words(arena, st, 1U + arity);
    b = anf_root_pop(st);
    a = anf_root_pop(st);
    arena[idx] = ANF_HDR(arity, ANF_ST_BYTES, 0U);
    arena[idx + 1U] = len;
    if (data_words > 0U)
        arena[idx + 1U + data_words] = 0U;
    uint8_t *dst = (uint8_t *)(arena + idx + 2U);
    const uint8_t *pa = (const uint8_t *)(arena + ANF_IDX(a) + 2U);
    const uint8_t *pb = (const uint8_t *)(arena + ANF_IDX(b) + 2U);
    for (uint32_t i = 0U; i < la; i++)
        dst[i] = pa[i];
    for (uint32_t i = 0U; i < lb; i++)
        dst[la + i] = pb[i];
    return ANF_BOX(idx);
}

static uint32_t z_finish(uint32_t *arena, struct anf_state *st,
                         uint32_t dst, int in_major, uint32_t neg, uint32_t n) {
    uint32_t *limbs = arena + dst + 1U;
    while (n > 0U && limbs[n - 1U] == 0U)
        n--;
    if (n == 0U)
        return ANF_IMM(0U);
    if (n == 1U) {
        uint32_t v = limbs[0];
        if (!neg && v <= 0x3FFFFFFFU)
            return ANF_IMM(v);
        if (neg && v <= 0x40000000U)
            return ANF_IMM(0U - v);
    }
    if (n > ANF_MAX_ARITY)
        anf_oom();
    arena[dst] = ANF_HDR(n, ANF_ST_BIGINT, neg ? 1U : 0U);
    commit_scratch(st, in_major, 1U + n);
    return ANF_BOX(dst);
}

uint32_t anf_z_of_u64(uint32_t *arena, struct anf_state *st, uint64_t u) {
    if (u <= (uint64_t)ANF_Z_MAX_IMM)
        return ANF_IMM((uint32_t)u);
    uint32_t n = (u >> 32) ? 2U : 1U;
    int in_major = 0;
    uint32_t dst = reserve_scratch(arena, st, 1U + n, &in_major);
    arena[dst + 1U] = (uint32_t)u;
    if (n == 2U)
        arena[dst + 2U] = (uint32_t)(u >> 32);
    return z_finish(arena, st, dst, in_major, 0U, n);
}

uint32_t anf_z_of_i64(uint32_t *arena, struct anf_state *st, int64_t v) {
    if (v >= ANF_Z_MIN_IMM && v <= ANF_Z_MAX_IMM)
        return ANF_IMM((uint32_t)(int32_t)v);
    uint32_t neg = v < 0 ? 1U : 0U;
    uint64_t mag = neg ? (0ULL - (uint64_t)v) : (uint64_t)v;
    uint32_t n = (mag >> 32) ? 2U : 1U;
    int in_major = 0;
    uint32_t dst = reserve_scratch(arena, st, 1U + n, &in_major);
    arena[dst + 1U] = (uint32_t)mag;
    if (n == 2U)
        arena[dst + 2U] = (uint32_t)(mag >> 32);
    return z_finish(arena, st, dst, in_major, neg, n);
}

int anf_z_to_i64(const uint32_t *arena, uint32_t z, int64_t *out) {
    if (ANF_IS_IMM(z)) {
        *out = (int64_t)ANF_IMM_S31(z);
        return 1;
    }
    uint32_t idx = ANF_IDX(z);
    uint32_t hdr = arena[idx];
    uint32_t n = ANF_HDR_ARITY(hdr);
    uint32_t neg = ANF_HDR_ORD(hdr);
    if (n > 2U)
        return 0;
    uint64_t mag = (uint64_t)arena[idx + 1U] |
                   (n == 2U ? ((uint64_t)arena[idx + 2U] << 32) : 0ULL);
    if (!neg) {
        if (mag > 0x7FFFFFFFFFFFFFFFULL)
            return 0;
        *out = (int64_t)mag;
        return 1;
    }
    if (mag > 0x8000000000000000ULL)
        return 0;
    *out = (mag == 0x8000000000000000ULL) ? (-9223372036854775807LL - 1LL) : -(int64_t)mag;
    return 1;
}

static void z_unpack(const uint32_t *arena, uint32_t z, uint32_t *imm_limb,
                     uint32_t *neg, const uint32_t **limbs, uint32_t *n) {
    if (ANF_IS_IMM(z)) {
        int32_t v = ANF_IMM_S31(z);
        if (v == 0) {
            *neg = 0U;
            *limbs = imm_limb;
            *n = 0U;
        } else if (v < 0) {
            *imm_limb = 0U - (uint32_t)v;
            *neg = 1U;
            *limbs = imm_limb;
            *n = 1U;
        } else {
            *imm_limb = (uint32_t)v;
            *neg = 0U;
            *limbs = imm_limb;
            *n = 1U;
        }
    } else {
        uint32_t idx = ANF_IDX(z);
        uint32_t hdr = arena[idx];
        *neg = ANF_HDR_ORD(hdr);
        *limbs = arena + idx + 1U;
        *n = ANF_HDR_ARITY(hdr);
    }
}

static int mag_cmp(const uint32_t *a, uint32_t na, const uint32_t *b, uint32_t nb) {
    if (na != nb)
        return na < nb ? -1 : 1;
    for (uint32_t i = na; i > 0U; i--) {
        if (a[i - 1U] != b[i - 1U])
            return a[i - 1U] < b[i - 1U] ? -1 : 1;
    }
    return 0;
}

int anf_z_cmp(const uint32_t *arena, uint32_t a, uint32_t b) {
    if ((a & b & 1U) != 0U) {
        int32_t va = ANF_IMM_S31(a), vb = ANF_IMM_S31(b);
        return (va > vb) - (va < vb);
    }
    if (ANF_IS_IMM(a))
        return ANF_HDR_ORD(arena[ANF_IDX(b)]) ? 1 : -1;
    if (ANF_IS_IMM(b))
        return ANF_HDR_ORD(arena[ANF_IDX(a)]) ? -1 : 1;
    uint32_t ia = ANF_IDX(a), ib = ANF_IDX(b);
    uint32_t na = ANF_HDR_ARITY(arena[ia]), nb = ANF_HDR_ARITY(arena[ib]);
    uint32_t sa = ANF_HDR_ORD(arena[ia]), sb = ANF_HDR_ORD(arena[ib]);
    if (sa != sb)
        return sa ? -1 : 1;
    int mc = mag_cmp(arena + ia + 1U, na, arena + ib + 1U, nb);
    return sa ? -mc : mc;
}

uint32_t anf_z_neg(uint32_t *arena, struct anf_state *st, uint32_t a) {
    if (ANF_IS_IMM(a)) {
        int64_t v = -(int64_t)ANF_IMM_S31(a);
        return anf_z_of_i64(arena, st, v);
    }
    uint32_t n = ANF_HDR_ARITY(arena[ANF_IDX(a)]);
    anf_root_push(st, a);
    int in_major = 0;
    uint32_t dst = reserve_scratch(arena, st, 1U + n, &in_major);
    a = anf_root_pop(st);
    uint32_t idx = ANF_IDX(a);
    uint32_t neg = ANF_HDR_ORD(arena[idx]) ^ 1U;
    for (uint32_t i = 0U; i < n; i++)
        arena[dst + 1U + i] = arena[idx + 1U + i];
    return z_finish(arena, st, dst, in_major, neg, n);
}

static uint32_t z_add_signed(uint32_t *arena, struct anf_state *st,
                             uint32_t a, uint32_t b, uint32_t flip_b) {
    uint32_t na_est = ANF_IS_IMM(a) ? 1U : ANF_HDR_ARITY(arena[ANF_IDX(a)]);
    uint32_t nb_est = ANF_IS_IMM(b) ? 1U : ANF_HDR_ARITY(arena[ANF_IDX(b)]);
    uint32_t max_n = (na_est > nb_est ? na_est : nb_est) + 1U;
    anf_root_push(st, a);
    anf_root_push(st, b);
    int in_major = 0;
    uint32_t dst = reserve_scratch(arena, st, 1U + max_n, &in_major);
    b = anf_root_pop(st);
    a = anf_root_pop(st);
    uint32_t la_imm = 0U, lb_imm = 0U, sa = 0U, sb = 0U, na = 0U, nb = 0U;
    const uint32_t *pa = NULL, *pb = NULL;
    z_unpack(arena, a, &la_imm, &sa, &pa, &na);
    z_unpack(arena, b, &lb_imm, &sb, &pb, &nb);
    if (nb > 0U)
        sb ^= flip_b;
    uint32_t *out = arena + dst + 1U;
    if (sa == sb) {
        uint64_t carry = 0ULL;
        uint32_t m = na > nb ? na : nb;
        for (uint32_t i = 0U; i < m; i++) {
            uint64_t sum = carry + (i < na ? pa[i] : 0ULL) + (i < nb ? pb[i] : 0ULL);
            out[i] = (uint32_t)sum;
            carry = sum >> 32;
        }
        out[m] = (uint32_t)carry;
        return z_finish(arena, st, dst, in_major, sa, m + 1U);
    }
    int mc = mag_cmp(pa, na, pb, nb);
    if (mc == 0)
        return ANF_IMM(0U);
    const uint32_t *hi = mc > 0 ? pa : pb;
    const uint32_t *lo = mc > 0 ? pb : pa;
    uint32_t nhi = mc > 0 ? na : nb;
    uint32_t nlo = mc > 0 ? nb : na;
    uint32_t neg = mc > 0 ? sa : sb;
    uint64_t borrow = 0ULL;
    for (uint32_t i = 0U; i < nhi; i++) {
        uint64_t av = hi[i];
        uint64_t bv = (i < nlo ? (uint64_t)lo[i] : 0ULL) + borrow;
        out[i] = (uint32_t)(av - bv);
        borrow = av < bv ? 1ULL : 0ULL;
    }
    return z_finish(arena, st, dst, in_major, neg, nhi);
}

uint32_t anf_z_add(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) {
    if ((a & b & 1U) != 0U)
        return anf_z_of_i64(arena, st, (int64_t)ANF_IMM_S31(a) + (int64_t)ANF_IMM_S31(b));
    return z_add_signed(arena, st, a, b, 0U);
}

uint32_t anf_z_sub(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) {
    if ((a & b & 1U) != 0U)
        return anf_z_of_i64(arena, st, (int64_t)ANF_IMM_S31(a) - (int64_t)ANF_IMM_S31(b));
    return z_add_signed(arena, st, a, b, 1U);
}

uint32_t anf_z_mul(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) {
    if (a == ANF_IMM(0U) || b == ANF_IMM(0U))
        return ANF_IMM(0U);
    if ((a & b & 1U) != 0U)
        return anf_z_of_i64(arena, st, (int64_t)ANF_IMM_S31(a) * (int64_t)ANF_IMM_S31(b));
    uint32_t na_est = ANF_IS_IMM(a) ? 1U : ANF_HDR_ARITY(arena[ANF_IDX(a)]);
    uint32_t nb_est = ANF_IS_IMM(b) ? 1U : ANF_HDR_ARITY(arena[ANF_IDX(b)]);
    uint32_t max_n = na_est + nb_est;
    anf_root_push(st, a);
    anf_root_push(st, b);
    int in_major = 0;
    uint32_t dst = reserve_scratch(arena, st, 1U + max_n, &in_major);
    b = anf_root_pop(st);
    a = anf_root_pop(st);
    uint32_t la_imm = 0U, lb_imm = 0U, sa = 0U, sb = 0U, na = 0U, nb = 0U;
    const uint32_t *pa = NULL, *pb = NULL;
    z_unpack(arena, a, &la_imm, &sa, &pa, &na);
    z_unpack(arena, b, &lb_imm, &sb, &pb, &nb);
    uint32_t *out = arena + dst + 1U;
    for (uint32_t i = 0U; i < na + nb; i++)
        out[i] = 0U;
    for (uint32_t i = 0U; i < na; i++) {
        uint64_t carry = 0ULL;
        uint64_t av = pa[i];
        for (uint32_t j = 0U; j < nb; j++) {
            uint64_t prod = av * (uint64_t)pb[j] + (uint64_t)out[i + j] + carry;
            out[i + j] = (uint32_t)prod;
            carry = prod >> 32;
        }
        out[i + nb] = (uint32_t)carry;
    }
    return z_finish(arena, st, dst, in_major, sa ^ sb, na + nb);
}
