/* M1 verification suite for nanofil/anf/anf_arena.c:
 *   1. Fil-C capability bounds, mmap flag, and zero-aux check on 8 GiB + 4 KiB arena
 *   2. Differential 31-bit / multi-limb Z suite across 2^30, 2^31, 2^32, 2^63, 2^64, 2^192
 *   3. Packed byte blocks (ANF_ST_BYTES) including nursery-pointer-lookalike raw words
 *   4. 10,000-step randomized algebraic tree-rewrite stress with a 256-word nursery
 *      under FUGC_SCRIBBLE=1 FUGC_VERIFY=1 + MADV_DONTNEED resets
 *   5. OutOfMemory refusal boundary tests (major exhaustion, oversized alloc, root stack)
 */
#include "anf_arena.h"

#include <signal.h>
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#define CHECK(cond, msg) do { \
    if (!(cond)) { \
        fprintf(stderr, "FAIL [%s:%d]: %s\n", __FILE__, __LINE__, (msg)); \
        exit(1); \
    } \
} while (0)

/* ---- Independent arbitrary-precision reference Z (heap-allocated, outside arena) ---- */

struct ref_z {
    int neg;        /* 0 for >= 0, 1 for < 0 */
    uint32_t n;     /* 0 means zero; else limbs[n-1] != 0 */
    uint32_t limbs[16];
};

static void rz_norm(struct ref_z *z) {
    while (z->n > 0U && z->limbs[z->n - 1U] == 0U)
        z->n--;
    if (z->n == 0U)
        z->neg = 0;
}

static struct ref_z rz_of_u64(uint64_t u) {
    struct ref_z z;
    memset(&z, 0, sizeof z);
    if (u == 0ULL)
        return z;
    z.limbs[0] = (uint32_t)u;
    z.limbs[1] = (uint32_t)(u >> 32);
    z.n = z.limbs[1] ? 2U : 1U;
    return z;
}

static struct ref_z rz_of_i64(int64_t v) {
    uint64_t mag = v < 0 ? (0ULL - (uint64_t)v) : (uint64_t)v;
    struct ref_z z = rz_of_u64(mag);
    if (v < 0)
        z.neg = 1;
    rz_norm(&z);
    return z;
}

static struct ref_z rz_neg(struct ref_z a) {
    if (a.n > 0U)
        a.neg ^= 1;
    return a;
}

static int rz_mag_cmp(const struct ref_z *a, const struct ref_z *b) {
    if (a->n != b->n)
        return a->n < b->n ? -1 : 1;
    for (uint32_t i = a->n; i > 0U; i--) {
        if (a->limbs[i - 1U] != b->limbs[i - 1U])
            return a->limbs[i - 1U] < b->limbs[i - 1U] ? -1 : 1;
    }
    return 0;
}

static int rz_cmp(const struct ref_z *a, const struct ref_z *b) {
    if (a->n == 0U && b->n == 0U)
        return 0;
    if (a->neg != b->neg)
        return a->neg ? -1 : 1;
    int mc = rz_mag_cmp(a, b);
    return a->neg ? -mc : mc;
}

static struct ref_z rz_add(struct ref_z a, struct ref_z b) {
    struct ref_z out;
    memset(&out, 0, sizeof out);
    if (a.n == 0U) return b;
    if (b.n == 0U) return a;
    if (a.neg == b.neg) {
        uint64_t c = 0ULL;
        uint32_t m = a.n > b.n ? a.n : b.n;
        CHECK(m + 1U <= 16U, "ref_z overflow");
        for (uint32_t i = 0U; i < m; i++) {
            uint64_t s = c + (i < a.n ? a.limbs[i] : 0ULL) + (i < b.n ? b.limbs[i] : 0ULL);
            out.limbs[i] = (uint32_t)s;
            c = s >> 32;
        }
        out.limbs[m] = (uint32_t)c;
        out.n = m + 1U;
        out.neg = a.neg;
        rz_norm(&out);
        return out;
    }
    int mc = rz_mag_cmp(&a, &b);
    if (mc == 0)
        return out;
    const struct ref_z *hi = mc > 0 ? &a : &b;
    const struct ref_z *lo = mc > 0 ? &b : &a;
    uint64_t borrow = 0ULL;
    for (uint32_t i = 0U; i < hi->n; i++) {
        uint64_t av = hi->limbs[i];
        uint64_t bv = (i < lo->n ? (uint64_t)lo->limbs[i] : 0ULL) + borrow;
        out.limbs[i] = (uint32_t)(av - bv);
        borrow = av < bv ? 1ULL : 0ULL;
    }
    out.n = hi->n;
    out.neg = hi->neg;
    rz_norm(&out);
    return out;
}

static struct ref_z rz_sub(struct ref_z a, struct ref_z b) {
    return rz_add(a, rz_neg(b));
}

static struct ref_z rz_mul(struct ref_z a, struct ref_z b) {
    struct ref_z out;
    memset(&out, 0, sizeof out);
    if (a.n == 0U || b.n == 0U)
        return out;
    CHECK(a.n + b.n <= 16U, "ref_z mul overflow");
    for (uint32_t i = 0U; i < a.n; i++) {
        uint64_t c = 0ULL;
        for (uint32_t j = 0U; j < b.n; j++) {
            uint64_t p = (uint64_t)a.limbs[i] * (uint64_t)b.limbs[j] + out.limbs[i + j] + c;
            out.limbs[i + j] = (uint32_t)p;
            c = p >> 32;
        }
        out.limbs[i + b.n] = (uint32_t)c;
    }
    out.n = a.n + b.n;
    out.neg = a.neg ^ b.neg;
    rz_norm(&out);
    return out;
}

static int rz_fits_imm(const struct ref_z *r) {
    if (r->n == 0U)
        return 1;
    if (r->n > 1U)
        return 0;
    if (!r->neg)
        return r->limbs[0] <= 0x3FFFFFFFU;
    return r->limbs[0] <= 0x40000000U;
}

static void check_z_matches(const uint32_t *arena, uint32_t w, const struct ref_z *r) {
    int expect_imm = rz_fits_imm(r);
    CHECK(ANF_IS_IMM(w) == expect_imm, "canonical Z immediate/bigint invariant violated");
    if (expect_imm) {
        int32_t got = ANF_IMM_S31(w);
        int64_t exp = r->n == 0U ? 0LL : (r->neg ? -(int64_t)r->limbs[0] : (int64_t)r->limbs[0]);
        CHECK((int64_t)got == exp, "immediate Z value mismatch");
        return;
    }
    uint32_t idx = ANF_IDX(w);
    CHECK(idx >= 1U, "boxed Z index must skip sentinel word 0");
    uint32_t hdr = arena[idx];
    CHECK(ANF_HDR_ST(hdr) == ANF_ST_BIGINT, "boxed Z subtag must be ANF_ST_BIGINT");
    CHECK((int)ANF_HDR_ORD(hdr) == r->neg, "boxed Z sign mismatch");
    CHECK(ANF_HDR_ARITY(hdr) == r->n, "boxed Z limb count mismatch");
    CHECK(arena[idx + r->n] != 0U, "boxed Z top limb must be normalized nonzero");
    for (uint32_t i = 0U; i < r->n; i++)
        CHECK(arena[idx + 1U + i] == r->limbs[i], "boxed Z limb mismatch");
}

/* ---- Test 1: 8 GiB + 4 KiB capability & representation check ---- */

static void test_capability_layout(void) {
    uint32_t *arena = NULL;
    struct anf_state *st = NULL;

    CHECK(anf_arena_init(&arena, &st, ANF_MAX_SLAB_WORDS + 1U, 256U, 64U) == -1,
          "slab_words > 2^31 must be rejected");
    CHECK(anf_arena_init(&arena, &st, 257U, 256U, 64U) == -1,
          "slab_words <= nursery_words + 1 must be rejected");
    CHECK(anf_arena_init(&arena, &st, 1024U, 8U, 64U) == -1,
          "nursery_words < 16 must be rejected");

    CHECK(anf_arena_init(&arena, &st, ANF_MAX_SLAB_WORDS, ANF_DEFAULT_NURSERY,
                         ANF_DEFAULT_ROOT_CAP) == 0,
          "8 GiB + 4 KiB arena init failed");
    CHECK(zhasvalidcap(arena), "arena must carry valid Fil-C capability");
    CHECK(zhasvalidcap(st), "st must carry valid Fil-C capability");

    size_t cap_bytes = (size_t)((char *)zgetupper(arena) - (char *)zgetlower(arena));
    CHECK(cap_bytes == (1ULL << 33) + 4096ULL, "arena capability length != 2^33 + 4096");
    CHECK(st->nursery_end == (1U << 31), "nursery_end != 2^31");
    CHECK(st->nursery_base == (1U << 31) - ANF_DEFAULT_NURSERY, "nursery_base mismatch");
    CHECK(st->major_idx == 1U, "major_idx must start at 1 (word 0 reserved)");

    char *desc_a = zptr_to_new_string(arena);
    char *desc_s = zptr_to_new_string(st);
    CHECK(strstr(desc_a, "mmap") != NULL, "arena object must carry FILC_OBJECT_FLAG_MMAP");
    CHECK(strstr(desc_s, "mmap") != NULL, "state object must carry FILC_OBJECT_FLAG_MMAP");

    /* Keep live 8 GiB arena while destroying is skipped under FUGC_SCRIBBLE=1 so dead-object
     * scribbling does not memset 8 GiB; write nursery + guard tail to check capability span. */
    arena[st->nursery_base] = 0x12345678U;
    arena[st->nursery_end + ANF_GUARD_WORDS - 1U] = 0xCAFEBABEU;
    CHECK(arena[st->nursery_base] == 0x12345678U, "nursery write/read failed");
    CHECK(arena[st->nursery_end + ANF_GUARD_WORDS - 1U] == 0xCAFEBABEU, "guard tail write failed");
    if (!getenv("FUGC_SCRIBBLE"))
        CHECK(anf_arena_destroy(arena, st) == 0, "8 GiB munmap failed");
    printf("ok: capability layout (8 GiB + 4 KiB zsys_mmap, valid cap, mmap flag)\n");
}

/* ---- Test 2: Differential Z suite in a 256-word nursery ---- */

static void test_z_differential(void) {
    uint32_t *arena = NULL;
    struct anf_state *st = NULL;
    /* 64K-word slab, 256-word nursery: forces frequent minor_gc mid-Z-ops */
    CHECK(anf_arena_init(&arena, &st, 65536U, 256U, 4096U) == 0, "z arena init");

    static const int64_t seeds[] = {
        0LL, 1LL, -1LL, 2LL, -2LL, 7LL, -7LL, 255LL, -256LL,
        (1LL << 30) - 1LL, (1LL << 30), -(1LL << 30), -(1LL << 30) - 1LL,
        2147483647LL, 2147483648LL, -2147483648LL, -2147483649LL,
        4294967295LL, 4294967296LL, -4294967295LL, -4294967296LL,
        9223372036854775807LL, -9223372036854775807LL - 1LL
    };
    const size_t n_seeds = sizeof(seeds) / sizeof(seeds[0]);
    const size_t total = n_seeds + 5U;
    struct ref_z refs[32];
    uint32_t *ws = anf_root_frame(st, (uint32_t)total);

    for (size_t i = 0; i < n_seeds; i++) {
        refs[i] = rz_of_i64(seeds[i]);
        ws[i] = anf_z_of_i64(arena, st, seeds[i]);
        check_z_matches(arena, ws[i], &refs[i]);
        int64_t back = 0;
        CHECK(anf_z_to_i64(arena, ws[i], &back) == 1 && back == seeds[i], "to_i64 roundtrip");
    }
    /* Unsigned 2^63 and 2^64 - 1 (outside int64_t) */
    refs[n_seeds] = rz_of_u64(0x8000000000000000ULL);
    ws[n_seeds] = anf_z_of_u64(arena, st, 0x8000000000000000ULL);
    refs[n_seeds + 1] = rz_of_u64(0xFFFFFFFFFFFFFFFFULL);
    ws[n_seeds + 1] = anf_z_of_u64(arena, st, 0xFFFFFFFFFFFFFFFFULL);
    int64_t dummy = 0;
    CHECK(anf_z_to_i64(arena, ws[n_seeds], &dummy) == 0, "+2^63 must not fit int64_t");
    CHECK(anf_z_to_i64(arena, ws[n_seeds + 1], &dummy) == 0, "2^64-1 must not fit int64_t");

    /* Multi-limb values past 2^64, 2^128, and 2^192 */
    refs[n_seeds + 2] = rz_mul(refs[n_seeds + 1], refs[n_seeds + 1]); /* (2^64 - 1)^2 */
    ws[n_seeds + 2] = anf_z_mul(arena, st, ws[n_seeds + 1], ws[n_seeds + 1]);
    refs[n_seeds + 3] = rz_neg(rz_add(refs[n_seeds + 2], rz_of_i64(12345)));
    ws[n_seeds + 3] = anf_z_neg(arena, st, anf_z_add(arena, st, ws[n_seeds + 2], anf_z_of_i64(arena, st, 12345)));
    refs[n_seeds + 4] = rz_mul(refs[n_seeds + 3], refs[n_seeds + 1]); /* ~ -2^192 */
    ws[n_seeds + 4] = anf_z_mul(arena, st, ws[n_seeds + 3], ws[n_seeds + 1]);

    for (size_t i = n_seeds; i < total; i++)
        check_z_matches(arena, ws[i], &refs[i]);

    /* Exhaustive pairwise add, sub, mul, neg, cmp across all values in 256-word nursery */
    for (size_t i = 0; i < total; i++) {
        struct ref_z rn = rz_neg(refs[i]);
        uint32_t wn = anf_z_neg(arena, st, ws[i]);
        check_z_matches(arena, wn, &rn);

        for (size_t j = 0; j < total; j++) {
            int rc = rz_cmp(&refs[i], &refs[j]);
            int wc = anf_z_cmp(arena, ws[i], ws[j]);
            CHECK(wc == rc, "anf_z_cmp mismatch");

            struct ref_z radd = rz_add(refs[i], refs[j]);
            uint32_t wadd = anf_z_add(arena, st, ws[i], ws[j]);
            check_z_matches(arena, wadd, &radd);

            struct ref_z rsub = rz_sub(refs[i], refs[j]);
            uint32_t wsub = anf_z_sub(arena, st, ws[i], ws[j]);
            check_z_matches(arena, wsub, &rsub);

            struct ref_z rmul = rz_mul(refs[i], refs[j]);
            uint32_t wmul = anf_z_mul(arena, st, ws[i], ws[j]);
            check_z_matches(arena, wmul, &rmul);
        }
    }

    /* Fresh nursery operands (unpromoted before call) to force >= 50 GCs during add/sub/mul */
    uint32_t *ab = anf_root_frame(st, 2U);
    ab[0] = ANF_IMM(0U);
    ab[1] = ANF_IMM(0U);
    for (int k = 0; k < 500; k++) {
        anf_roots(st)[st->root_sp - 2U] = anf_z_of_u64(arena, st, 0xFFFFFFFFFFFFFFFFULL - (uint64_t)k);
        anf_roots(st)[st->root_sp - 1U] = anf_z_of_u64(arena, st, 0xFFFFFFFFFFFFFFFFULL - (uint64_t)(k + 3));
        uint32_t diff = anf_z_sub(arena, st,
                                  anf_roots(st)[st->root_sp - 2U],
                                  anf_roots(st)[st->root_sp - 1U]);
        CHECK(diff == ANF_IMM(3), "bigint cancellation must normalize to immediate 3");
        uint32_t prod = anf_z_mul(arena, st,
                                  anf_roots(st)[st->root_sp - 2U],
                                  anf_roots(st)[st->root_sp - 1U]);
        CHECK(!ANF_IS_IMM(prod), "128-bit product must be boxed");
    }
    st->root_sp -= 2U;

    uint64_t gcs = st->gc_count;
    if (gcs < 40ULL) {
        fprintf(stderr, "unexpectedly low gcs=%llu\n", (unsigned long long)gcs);
        exit(1);
    }
    st->root_sp = 0U;
    CHECK(anf_arena_destroy(arena, st) == 0, "z arena destroy");
    printf("ok: differential Z suite (%zu^2 pairs, %llu minor GCs in 256-word nursery)\n",
           total, (unsigned long long)gcs);
}

/* ---- Test 3: Packed byte blocks + nursery-pointer-lookalike words ---- */

static void test_packed_bytes(void) {
    uint32_t *arena = NULL;
    struct anf_state *st = NULL;
    CHECK(anf_arena_init(&arena, &st, 65536U, 256U, 1024U) == 0, "bytes arena init");

    /* Build a byte payload containing raw 32-bit words equal to valid & out-of-range
     * nursery boxed words: if minor_gc scanned ANF_ST_BYTES payloads, evacuate_word
     * would treat these bytes as nursery pointers and corrupt them or panic. */
    uint32_t fake_words[6];
    fake_words[0] = ANF_BOX(st->nursery_base);
    fake_words[1] = ANF_BOX(st->nursery_base + 4U);
    fake_words[2] = ANF_BOX(st->nursery_end - 2U);
    fake_words[3] = 0x006c6c65U; /* embedded NUL + ASCII */
    fake_words[4] = ANF_FWD_HDR & ~1U;
    fake_words[5] = 0xA5A5A5A4U;

    uint32_t s_adv = anf_bytes_from_buf(arena, st, (const uint8_t *)fake_words, sizeof fake_words);
    anf_root_push(st, s_adv);

    static const uint32_t lens[] = { 0, 1, 2, 3, 4, 5, 7, 8, 15, 16, 31, 32, 63, 64, 129 };
    for (size_t li = 0; li < sizeof(lens) / sizeof(lens[0]); li++) {
        uint32_t len = lens[li];
        uint8_t buf[256], out[256];
        for (uint32_t i = 0; i < len; i++)
            buf[i] = (uint8_t)((i * 73U + len * 19U) & 0xFFU);
        uint32_t s = anf_bytes_from_buf(arena, st, buf, len);
        anf_root_push(st, s);
        /* Allocate nursery chaff to force evacuation */
        for (int c = 0; c < 90; c++)
            (void)anf_bytes_from_buf(arena, st, buf, 7U);
        s = anf_root_pop(st);

        CHECK(anf_bytes_len(arena, s) == len, "bytes len mismatch after GC");
        memset(out, 0xEE, sizeof out);
        anf_bytes_copy_out(arena, s, out);
        CHECK(memcmp(buf, out, len) == 0, "bytes copy_out mismatch after GC");
        for (uint32_t i = 0; i < len; i++)
            CHECK(anf_bytes_get(arena, s, i) == ANF_IMM(buf[i]), "bytes_get tagged ascii mismatch");

        /* Concatenation across nursery GC */
        uint32_t cat = anf_bytes_concat(arena, st, s, anf_roots(st)[0]);
        CHECK(anf_bytes_len(arena, cat) == len + (uint32_t)sizeof(fake_words), "concat len");
        uint8_t cat_out[512];
        anf_bytes_copy_out(arena, cat, cat_out);
        CHECK(memcmp(cat_out, buf, len) == 0, "concat prefix mismatch");
        CHECK(memcmp(cat_out + len, fake_words, sizeof fake_words) == 0, "concat suffix mismatch");
    }

    s_adv = anf_root_pop(st);
    uint8_t check_adv[sizeof fake_words];
    anf_bytes_copy_out(arena, s_adv, check_adv);
    CHECK(memcmp(check_adv, fake_words, sizeof fake_words) == 0,
          "adversarial nursery-lookalike bytes corrupted by minor_gc");

    /* Lexicographic comparison checks */
    uint32_t sa = anf_bytes_from_buf(arena, st, (const uint8_t *)"abc\0d", 5U);
    anf_root_push(st, sa);
    uint32_t sb = anf_bytes_from_buf(arena, st, (const uint8_t *)"abc\0e", 5U);
    anf_root_push(st, sb);
    uint32_t sc = anf_bytes_from_buf(arena, st, (const uint8_t *)"abc", 3U);
    sb = anf_root_pop(st);
    sa = anf_root_pop(st);
    CHECK(anf_bytes_cmp(arena, sa, sa) == 0, "bytes self eq");
    CHECK(anf_bytes_cmp(arena, sa, sb) < 0 && anf_bytes_cmp(arena, sb, sa) > 0, "bytes nul cmp");
    CHECK(anf_bytes_cmp(arena, sc, sa) < 0 && anf_bytes_cmp(arena, sa, sc) > 0, "bytes prefix cmp");

    uint64_t gcs = st->gc_count;
    CHECK(anf_arena_destroy(arena, st) == 0, "bytes arena destroy");
    printf("ok: packed byte blocks (%llu minor GCs, adversarial no-scan bytes intact)\n",
           (unsigned long long)gcs);
}

/* ---- Test 4: 10,000-step randomized tree-rewrite stress (256-word nursery) ----
 *
 * Algebraic term representation in arena:
 *   - Empty (0-ary, ord 0): ANF_IMM(0) = 1
 *   - ZLeaf(z)     (1-ary ANF_ST_SCAN, ord 0): [hdr(1,0,0), z]
 *   - BytesLeaf(b) (1-ary ANF_ST_SCAN, ord 1): [hdr(1,0,1), b]
 *   - Pair(a, b)   (2-ary ANF_ST_SCAN, ord 2): [hdr(2,0,2), a, b]
 *   - Node3(z,l,r) (3-ary ANF_ST_SCAN, ord 3): [hdr(3,0,3), z, l, r]
 */

enum model_kind { M_EMPTY = 0, M_Z = 1, M_BYTES = 2, M_PAIR = 3, M_NODE3 = 4 };

struct model_node {
    enum model_kind kind;
    int rc;
    struct ref_z z;
    uint32_t blen;
    uint8_t bytes[48];
    struct model_node *left;
    struct model_node *right;
};

static struct model_node *m_retain(struct model_node *n) {
    if (n) n->rc++;
    return n;
}

static void m_release(struct model_node *n) {
    if (!n || --n->rc > 0)
        return;
    m_release(n->left);
    m_release(n->right);
    free(n);
}

static struct model_node *m_alloc(enum model_kind k) {
    struct model_node *n = (struct model_node *)calloc(1, sizeof(*n));
    CHECK(n != NULL, "calloc model_node");
    n->kind = k;
    n->rc = 1;
    return n;
}

static uint32_t mk_ctor1(uint32_t *arena, struct anf_state *st, uint32_t ord, uint32_t f0) {
    anf_root_push(st, f0);
    uint32_t idx = anf_alloc_words(arena, st, 2U);
    f0 = anf_root_pop(st);
    arena[idx] = ANF_HDR(1U, ANF_ST_SCAN, ord);
    arena[idx + 1U] = f0;
    return ANF_BOX(idx);
}

static uint32_t mk_ctor2(uint32_t *arena, struct anf_state *st, uint32_t ord,
                         uint32_t f0, uint32_t f1) {
    uint32_t *fr = anf_root_frame(st, 2U);
    fr[0] = f0;
    fr[1] = f1;
    uint32_t idx = anf_alloc_words(arena, st, 3U);
    f1 = anf_root_pop(st);
    f0 = anf_root_pop(st);
    arena[idx] = ANF_HDR(2U, ANF_ST_SCAN, ord);
    arena[idx + 1U] = f0;
    arena[idx + 2U] = f1;
    return ANF_BOX(idx);
}

static uint32_t mk_ctor3(uint32_t *arena, struct anf_state *st, uint32_t ord,
                         uint32_t f0, uint32_t f1, uint32_t f2) {
    uint32_t *fr = anf_root_frame(st, 3U);
    fr[0] = f0;
    fr[1] = f1;
    fr[2] = f2;
    uint32_t idx = anf_alloc_words(arena, st, 4U);
    f2 = anf_root_pop(st);
    f1 = anf_root_pop(st);
    f0 = anf_root_pop(st);
    arena[idx] = ANF_HDR(3U, ANF_ST_SCAN, ord);
    arena[idx + 1U] = f0;
    arena[idx + 2U] = f1;
    arena[idx + 3U] = f2;
    return ANF_BOX(idx);
}

static void verify_tree(const uint32_t *arena, uint32_t w, const struct model_node *m) {
    if (!m || m->kind == M_EMPTY) {
        CHECK(w == ANF_IMM(0U), "expected Empty immediate");
        return;
    }
    CHECK(!ANF_IS_IMM(w), "expected boxed constructor");
    uint32_t idx = ANF_IDX(w);
    uint32_t hdr = arena[idx];
    CHECK(ANF_HDR_ST(hdr) == ANF_ST_SCAN, "expected ANF_ST_SCAN constructor");
    uint32_t ord = ANF_HDR_ORD(hdr);
    uint32_t arity = ANF_HDR_ARITY(hdr);
    switch (m->kind) {
    case M_Z:
        CHECK(ord == 0U && arity == 1U, "ZLeaf header mismatch");
        check_z_matches(arena, arena[idx + 1U], &m->z);
        break;
    case M_BYTES: {
        CHECK(ord == 1U && arity == 1U, "BytesLeaf header mismatch");
        uint32_t bw = arena[idx + 1U];
        CHECK(anf_bytes_len(arena, bw) == m->blen, "BytesLeaf length mismatch");
        uint8_t tmp[64];
        anf_bytes_copy_out(arena, bw, tmp);
        CHECK(memcmp(tmp, m->bytes, m->blen) == 0, "BytesLeaf bytes mismatch");
        break;
    }
    case M_PAIR:
        CHECK(ord == 2U && arity == 2U, "Pair header mismatch");
        verify_tree(arena, arena[idx + 1U], m->left);
        verify_tree(arena, arena[idx + 2U], m->right);
        break;
    case M_NODE3:
        CHECK(ord == 3U && arity == 3U, "Node3 header mismatch");
        check_z_matches(arena, arena[idx + 1U], &m->z);
        verify_tree(arena, arena[idx + 2U], m->left);
        verify_tree(arena, arena[idx + 3U], m->right);
        break;
    default:
        CHECK(0, "unreachable model kind");
    }
}

static uint32_t rng_next(uint64_t *state) {
    *state = (*state * 6364136223846793005ULL) + 1442695040888963407ULL;
    return (uint32_t)(*state >> 32);
}

static int model_depth(const struct model_node *m) {
    if (!m || m->kind == M_EMPTY)
        return 0;
    int dl = model_depth(m->left);
    int dr = model_depth(m->right);
    return 1 + (dl > dr ? dl : dr);
}

/* Recursive rewrite step exercising multi-frame shadow roots across Eletapp-style calls */
static uint32_t rewrite_rec(uint32_t *arena, struct anf_state *st,
                            uint32_t w, struct model_node **mp,
                            uint64_t *rng, int depth_budget) {
    uint32_t op = rng_next(rng) % 8U;
    struct model_node *m = *mp;

    if (depth_budget <= 0 || !m || m->kind == M_EMPTY || op <= 2U) {
        uint32_t leaf_kind = rng_next(rng) % 3U;
        if (leaf_kind == 0U) {
            /* New ZLeaf spanning 31-bit and multi-limb values */
            int64_t base = (int64_t)(int32_t)rng_next(rng);
            int shift = (int)(rng_next(rng) % 36U);
            struct ref_z rz = rz_mul(rz_of_i64(base), rz_of_u64(1ULL << shift));
            uint32_t zb = anf_z_of_i64(arena, st, base);
            anf_root_push(st, zb);
            uint32_t zs = anf_z_of_u64(arena, st, 1ULL << shift);
            zb = anf_root_pop(st);
            uint32_t zw = anf_z_mul(arena, st, zb, zs);

            struct model_node *nm = m_alloc(M_Z);
            nm->z = rz;
            m_release(*mp);
            *mp = nm;
            return mk_ctor1(arena, st, 0U, zw);
        }
        if (leaf_kind == 1U) {
            /* New BytesLeaf with arbitrary bytes (including nursery-lookalike words) */
            uint32_t len = rng_next(rng) % 37U;
            struct model_node *nm = m_alloc(M_BYTES);
            nm->blen = len;
            for (uint32_t i = 0; i < len; i++)
                nm->bytes[i] = (uint8_t)(rng_next(rng) & 0xFFU);
            if (len >= 4U) {
                uint32_t fake = ANF_BOX(st->nursery_base + (rng_next(rng) % 200U));
                memcpy(nm->bytes, &fake, 4U);
            }
            uint32_t bw = anf_bytes_from_buf(arena, st, nm->bytes, len);
            m_release(*mp);
            *mp = nm;
            return mk_ctor1(arena, st, 1U, bw);
        }
        m_release(*mp);
        *mp = NULL;
        return ANF_IMM(0U);
    }

    if (op == 3U && (m->kind == M_PAIR || m->kind == M_NODE3)) {
        /* Swap + rewrite both children recursively while holding live values on shadow roots */
        uint32_t idx = ANF_IDX(w);
        uint32_t is_n3 = (m->kind == M_NODE3);
        uint32_t z_old = is_n3 ? arena[idx + 1U] : ANF_IMM(0U);
        uint32_t l_old = arena[idx + (is_n3 ? 2U : 1U)];
        uint32_t r_old = arena[idx + (is_n3 ? 3U : 2U)];

        struct model_node *ml = m_retain(m->right);
        struct model_node *mr = m_retain(m->left);

        uint32_t *fr = anf_root_frame(st, 3U);
        fr[0] = z_old;
        fr[1] = l_old;
        fr[2] = r_old;

        /* Rewrite right->new_left while z_old and l_old sit in fr[0], fr[1] */
        uint32_t nl = rewrite_rec(arena, st, fr[2], &ml, rng, depth_budget - 1);
        fr = anf_roots(st) + st->root_sp - 3U;
        fr[2] = nl;

        /* Allocate transient dead garbage between recursive calls to churn the 256-word nursery */
        for (int g = 0; g < 6; g++) {
            uint32_t dead = anf_z_of_u64(arena, st, 0x100000000ULL + (uint64_t)g);
            (void)mk_ctor2(arena, st, 2U, dead, ANF_IMM(g));
        }

        /* Rewrite left->new_right while z_old and nl sit in fr[0], fr[2] */
        fr = anf_roots(st) + st->root_sp - 3U;
        uint32_t nr = rewrite_rec(arena, st, fr[1], &mr, rng, depth_budget - 1);
        fr = anf_roots(st) + st->root_sp - 3U;
        nl = fr[2];
        z_old = fr[0];
        st->root_sp -= 3U;

        if (is_n3) {
            anf_root_push(st, nl);
            anf_root_push(st, nr);
            uint32_t z_new = anf_z_add(arena, st, z_old, anf_z_of_i64(arena, st, -17));
            nr = anf_root_pop(st);
            nl = anf_root_pop(st);

            struct model_node *nm = m_alloc(M_NODE3);
            nm->z = rz_add(m->z, rz_of_i64(-17));
            nm->left = ml;
            nm->right = mr;
            m_release(*mp);
            *mp = nm;
            return mk_ctor3(arena, st, 3U, z_new, nl, nr);
        } else {
            struct model_node *nm = m_alloc(M_PAIR);
            nm->left = ml;
            nm->right = mr;
            m_release(*mp);
            *mp = nm;
            return mk_ctor2(arena, st, 2U, nl, nr);
        }
    }

    if (op == 4U && depth_budget >= 2) {
        /* Diamond DAG sharing: Pair(sub, sub) where both fields alias the exact same nursery/major node! */
        struct model_node *sub_m = m_retain(m);
        uint32_t sub_w = w;
        if (model_depth(sub_m) > 4) {
            sub_w = rewrite_rec(arena, st, sub_w, &sub_m, rng, 2);
        }
        struct model_node *nm = m_alloc(M_PAIR);
        nm->left = m_retain(sub_m);
        nm->right = sub_m;
        m_release(*mp);
        *mp = nm;
        return mk_ctor2(arena, st, 2U, sub_w, sub_w);
    }

    if (op == 5U && (m->kind == M_PAIR || m->kind == M_NODE3)) {
        /* Project left or right child (discards outer spine + sibling as nursery/major garbage) */
        uint32_t pick_r = rng_next(rng) & 1U;
        uint32_t idx = ANF_IDX(w);
        uint32_t off = (m->kind == M_NODE3 ? 2U : 1U) + pick_r;
        struct model_node *child = m_retain(pick_r ? m->right : m->left);
        m_release(*mp);
        *mp = child;
        return arena[idx + off];
    }

    /* Wrap existing tree in a fresh Node3 with multi-limb Z label */
    anf_root_push(st, w);
    int64_t delta = (int64_t)(int32_t)rng_next(rng) * 3LL;
    uint32_t z1 = anf_z_of_i64(arena, st, delta);
    anf_root_push(st, z1);
    uint32_t z2 = anf_z_of_i64(arena, st, (1LL << 31) + 99LL);
    z1 = anf_root_pop(st);
    uint32_t zprod = anf_z_mul(arena, st, z1, z2);
    anf_root_push(st, zprod);

    struct model_node *side_m = NULL;
    uint32_t side_w = rewrite_rec(arena, st, ANF_IMM(0U), &side_m, rng, 1);
    zprod = anf_root_pop(st);
    w = anf_root_pop(st);

    struct model_node *keep = m_retain(m);
    if (model_depth(keep) > 6 && (keep->kind == M_PAIR || keep->kind == M_NODE3)) {
        uint32_t idx = ANF_IDX(w);
        w = arena[idx + (keep->kind == M_NODE3 ? 2U : 1U)];
        struct model_node *kl = m_retain(keep->left);
        m_release(keep);
        keep = kl;
    }

    struct model_node *nm = m_alloc(M_NODE3);
    nm->z = rz_mul(rz_of_i64(delta), rz_of_i64((1LL << 31) + 99LL));
    nm->left = keep;
    nm->right = side_m;
    m_release(*mp);
    *mp = nm;
    return mk_ctor3(arena, st, 3U, zprod, w, side_w);
}

static void test_randomized_tree_rewrites(void) {
    uint32_t *arena = NULL;
    struct anf_state *st = NULL;
    /* 1 Mi-word (4 MiB) slab, 256-word nursery: evacuation fires every few dozen constructors! */
    CHECK(anf_arena_init(&arena, &st, 1U << 20, 256U, 8192U) == 0, "stress arena init");

    enum { N_ROOTS = 8, STEPS = 10000 };
    struct model_node *models[N_ROOTS];
    memset(models, 0, sizeof models);

    uint32_t *roots = anf_root_frame(st, N_ROOTS);
    for (int i = 0; i < N_ROOTS; i++)
        roots[i] = ANF_IMM(0U);

    uint64_t rng = 0xD1B54A32D192ED03ULL;
    uint64_t total_gcs = 0ULL, total_promoted = 0ULL;
    int resets = 0;

    for (int step = 1; step <= STEPS; step++) {
        int slot = (int)(rng_next(&rng) % N_ROOTS);
        uint32_t cur = anf_roots(st)[slot];
        uint32_t updated = rewrite_rec(arena, st, cur, &models[slot], &rng, 5);
        CHECK(st->root_sp == N_ROOTS, "root_sp unbalanced after rewrite_rec");
        anf_roots(st)[slot] = updated;

        /* Also churn 24 dead nursery constructors per step (~72-96 words) so GC runs every 2-3 steps */
        for (int g = 0; g < 12; g++) {
            uint32_t c = mk_ctor2(arena, st, 2U, ANF_IMM(step + g), ANF_IMM(g));
            (void)c;
        }

        if (step % 250 == 0) {
            for (int i = 0; i < N_ROOTS; i++)
                verify_tree(arena, anf_roots(st)[i], models[i]);
        }

        /* Trigger synchronous FUGC cycle + MADV_DONTNEED reset between independent epochs */
        if (step == 3500 || step == 7000) {
            void *filc_chaff = malloc(4096);
            CHECK(filc_chaff != NULL, "malloc chaff");
            free(filc_chaff);
            zgc_request_and_wait();

            for (int i = 0; i < N_ROOTS; i++)
                verify_tree(arena, anf_roots(st)[i], models[i]);

            total_gcs += st->gc_count;
            total_promoted += st->promoted_words;
            for (int i = 0; i < N_ROOTS; i++) {
                m_release(models[i]);
                models[i] = NULL;
            }
            CHECK(anf_arena_reset(arena, st, 0U) == 0, "anf_arena_reset MADV_DONTNEED failed");
            st->gc_count = 0ULL;
            st->promoted_words = 0ULL;
            roots = anf_root_frame(st, N_ROOTS);
            for (int i = 0; i < N_ROOTS; i++)
                roots[i] = ANF_IMM(0U);
            resets++;
        }
    }

    zgc_request_and_wait();
    for (int i = 0; i < N_ROOTS; i++) {
        verify_tree(arena, anf_roots(st)[i], models[i]);
        m_release(models[i]);
    }
    total_gcs += st->gc_count;
    total_promoted += st->promoted_words;
    st->root_sp = 0U;

    if (total_gcs < 1500ULL) {
        fprintf(stderr, "FAIL: expected >= 1500 minor GCs, got %llu\n", (unsigned long long)total_gcs);
        exit(1);
    }
    CHECK(anf_arena_destroy(arena, st) == 0, "stress arena destroy");
    printf("ok: %d randomized tree-rewrite steps, 0 mismatches (%llu minor GCs, %llu words promoted, %d MADV_DONTNEED resets)\n",
           STEPS, (unsigned long long)total_gcs, (unsigned long long)total_promoted, resets);
}

/* ---- Test 5: OutOfMemory boundary refusal tests ---- */

static int trapped_oom(void (*fn)(void)) {
    fflush(stdout);
    fflush(stderr);
    int fd[2];
    CHECK(pipe(fd) == 0, "pipe");
    pid_t pid = fork();
    CHECK(pid >= 0, "fork");
    if (pid == 0) {
        close(fd[0]);
        dup2(fd[1], 2);
        close(fd[1]);
        fn();
        _exit(0);
    }
    close(fd[1]);
    char buf[4096];
    size_t n = 0;
    ssize_t r;
    while (n < sizeof(buf) - 1 && (r = read(fd[0], buf + n, sizeof(buf) - 1 - n)) > 0)
        n += (size_t)r;
    buf[n] = '\0';
    close(fd[0]);
    int status = 0;
    waitpid(pid, &status, 0);
    return WIFSIGNALED(status) && WTERMSIG(status) == SIGTRAP &&
           strstr(buf, "filc safety error") != NULL &&
           strstr(buf, "out of memory") != NULL;
}

static void oom_major_exhaustion(void) {
    uint32_t *arena = NULL;
    struct anf_state *st = NULL;
    /* slab = 512 words, nursery = 256 words => major_limit = 256 words (words 1..255).
     * Building a live linked list of > 85 2-field cons cells (3 words each) must trap OOM! */
    if (anf_arena_init(&arena, &st, 512U, 256U, 64U) != 0)
        _exit(2);
    uint32_t *r = anf_root_frame(st, 1U);
    r[0] = ANF_IMM(0U);
    for (int i = 0; i < 200; i++) {
        uint32_t idx = anf_alloc_words(arena, st, 3U);
        arena[idx] = ANF_HDR(2U, ANF_ST_SCAN, 0U);
        arena[idx + 1U] = ANF_IMM(i);
        arena[idx + 2U] = anf_roots(st)[0];
        anf_roots(st)[0] = ANF_BOX(idx);
    }
}

static void oom_oversized_alloc(void) {
    uint32_t *arena = NULL;
    struct anf_state *st = NULL;
    if (anf_arena_init(&arena, &st, 1024U, 256U, 64U) != 0)
        _exit(2);
    /* Request 900 words > major_limit (768 words) */
    (void)anf_alloc_words(arena, st, 900U);
}

static void oom_root_overflow(void) {
    uint32_t *arena = NULL;
    struct anf_state *st = NULL;
    if (anf_arena_init(&arena, &st, 1024U, 256U, 16U) != 0)
        _exit(2);
    for (int i = 0; i < 17; i++)
        anf_root_push(st, ANF_IMM(i));
}

static void oom_root_frame_overflow(void) {
    uint32_t *arena = NULL;
    struct anf_state *st = NULL;
    if (anf_arena_init(&arena, &st, 1024U, 256U, 16U) != 0)
        _exit(2);
    anf_root_push(st, ANF_IMM(1));
    (void)anf_root_frame(st, 16U);
}

static void test_oom_boundaries(void) {
    CHECK(trapped_oom(oom_major_exhaustion), "major exhaustion must trap OutOfMemory");
    CHECK(trapped_oom(oom_oversized_alloc), "oversized alloc must trap OutOfMemory");
    CHECK(trapped_oom(oom_root_overflow), "root_push overflow must trap OutOfMemory");
    CHECK(trapped_oom(oom_root_frame_overflow), "root_frame overflow must trap OutOfMemory");
    printf("ok: OutOfMemory refusal boundary tests (major exhaustion, oversized alloc, root stack)\n");
}

int main(void) {
    test_capability_layout();
    test_z_differential();
    test_packed_bytes();
    test_randomized_tree_rewrites();
    test_oom_boundaries();
    printf("all M1 arena checks passed\n");
    return 0;
}
