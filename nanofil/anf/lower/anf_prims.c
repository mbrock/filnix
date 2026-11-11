/* The primitives of modules lowered by AnfLower.v (nanofil/docs/lambda-anf.md,
 * M3): the stdlib's integers, characters and strings in their represented
 * form, as anf_arena.h describes it.
 *
 * - An integer (nat, positive, N, Z) is an immediate (v << 1) | 1 for
 *   -2^30 <= v < 2^30, else an ANF_ST_BIGINT block (sign in the ordinal,
 *   base-2^32 limbs, low first, no leading zero limb).
 * - A character (ascii, Byte.byte) is the immediate of its code.
 * - A string is the immediate 0 (the word 1) when empty, else an
 *   ANF_ST_BYTES block (its length, then its bytes) or a slice of one: a
 *   block of three scanned fields, the bytes block and the immediates of
 *   an offset into it and a length. A tail or substring of SLICE_MIN bytes
 *   or more is a slice, so matching String c s down a string costs O(1)
 *   per byte instead of a copy of the rest.
 *
 * Every anf_p_ function takes the arena, the state and its operands as
 * words. Those the lowering calls on a slow path (an operand is not an
 * immediate, or the result is not one) never collect and never touch the
 * nursery: an integer they make that is not an immediate goes to the major
 * heap, a leaf no collection scans or moves. The string and list makers
 * (anf_p_str_cons and those after it) allocate in the nursery and may
 * collect: the lowering calls them as it calls a function, with its young
 * index stored and its live values on the shadow roots, and they root
 * their own operands across an allocation. Each returns the word of its
 * result; a comparison returns -1, 0 or 1, a test 0 or 1. */
#include <stdlib.h>
#include <string.h>
#include "../anf_arena.h"

/* ## Integers */

/* A magnitude: n limbs, low first, none of them a leading zero. */
struct mag {
    uint32_t n;
    uint32_t *d;
};

/* An integer: its sign and magnitude (zero has n == 0 and neg == 0). */
struct zint {
    int neg;
    struct mag m;
};

static uint32_t *limbs_new(uint32_t n)
{
    uint32_t *d = calloc(n ? n : 1U, sizeof(uint32_t));
    if (!d)
        anf_oom();
    return d;
}

static void norm(struct zint *z)
{
    while (z->m.n > 0U && z->m.d[z->m.n - 1U] == 0U)
        z->m.n--;
    if (z->m.n == 0U)
        z->neg = 0;
}

static struct zint z_new(uint32_t n)
{
    struct zint z = {0, {n, limbs_new(n)}};
    return z;
}

static void z_free(struct zint *z)
{
    free(z->m.d);
}

static struct zint z_of_i64(int64_t v)
{
    struct zint z = z_new(2U);
    uint64_t mag = v < 0 ? 0ULL - (uint64_t)v : (uint64_t)v;
    z.neg = v < 0;
    z.m.d[0] = (uint32_t)mag;
    z.m.d[1] = (uint32_t)(mag >> 32);
    norm(&z);
    return z;
}

/* The integer the word w holds. */
static struct zint z_load(const uint32_t *arena, uint32_t w)
{
    if (ANF_IS_IMM(w))
        return z_of_i64((int64_t)ANF_IMM_S31(w));
    uint32_t idx = ANF_IDX(w);
    uint32_t hdr = arena[idx];
    uint32_t n = ANF_HDR_ARITY(hdr);
    struct zint z = z_new(n);
    z.neg = ANF_HDR_ORD(hdr) != 0U;
    for (uint32_t i = 0U; i < n; i++)
        z.m.d[i] = arena[idx + 1U + i];
    norm(&z);
    return z;
}

/* The word of z, which is freed: an immediate, or a block in the major
 * heap. */
static uint32_t z_store(uint32_t *arena, struct anf_state *st, struct zint *z)
{
    norm(z);
    uint32_t n = z->m.n;
    if (n == 0U) {
        z_free(z);
        return ANF_IMM(0U);
    }
    if (n == 1U) {
        uint32_t v = z->m.d[0];
        if (!z->neg && v <= 0x3FFFFFFFU) {
            z_free(z);
            return ANF_IMM(v);
        }
        if (z->neg && v <= 0x40000000U) {
            z_free(z);
            return ANF_IMM(0U - v);
        }
    }
    if (n > ANF_MAX_ARITY || n + 1U > st->major_limit - st->major_idx)
        anf_oom();
    uint32_t idx = st->major_idx;
    arena[idx] = ANF_HDR(n, ANF_ST_BIGINT, z->neg ? 1U : 0U);
    for (uint32_t i = 0U; i < n; i++)
        arena[idx + 1U + i] = z->m.d[i];
    st->major_idx = idx + n + 1U;
    if (st->major_idx > st->major_hwm)
        st->major_hwm = st->major_idx;
    z_free(z);
    return ANF_BOX(idx);
}

static uint32_t store_i64(uint32_t *arena, struct anf_state *st, int64_t v)
{
    if (v >= ANF_Z_MIN_IMM && v <= ANF_Z_MAX_IMM)
        return ANF_IMM((uint32_t)(int32_t)v);
    struct zint z = z_of_i64(v);
    return z_store(arena, st, &z);
}

static int mag_cmp(const struct mag *a, const struct mag *b)
{
    if (a->n != b->n)
        return a->n < b->n ? -1 : 1;
    for (uint32_t i = a->n; i > 0U; i--)
        if (a->d[i - 1U] != b->d[i - 1U])
            return a->d[i - 1U] < b->d[i - 1U] ? -1 : 1;
    return 0;
}

static int z_cmp(const struct zint *a, const struct zint *b)
{
    if (a->neg != b->neg)
        return a->neg ? -1 : 1;
    int c = mag_cmp(&a->m, &b->m);
    return a->neg ? -c : c;
}

static struct mag mag_add(const struct mag *a, const struct mag *b)
{
    uint32_t n = (a->n > b->n ? a->n : b->n) + 1U;
    struct mag r = {n, limbs_new(n)};
    uint64_t carry = 0ULL;
    for (uint32_t i = 0U; i < n; i++) {
        uint64_t s = carry + (i < a->n ? a->d[i] : 0U) + (i < b->n ? b->d[i] : 0U);
        r.d[i] = (uint32_t)s;
        carry = s >> 32;
    }
    return r;
}

/* a - b, for a >= b. */
static struct mag mag_sub(const struct mag *a, const struct mag *b)
{
    struct mag r = {a->n, limbs_new(a->n)};
    uint64_t borrow = 0ULL;
    for (uint32_t i = 0U; i < a->n; i++) {
        uint64_t av = a->d[i];
        uint64_t bv = (i < b->n ? (uint64_t)b->d[i] : 0ULL) + borrow;
        r.d[i] = (uint32_t)(av - bv);
        borrow = av < bv ? 1ULL : 0ULL;
    }
    return r;
}

static struct mag mag_mul(const struct mag *a, const struct mag *b)
{
    uint32_t n = a->n + b->n;
    struct mag r = {n, limbs_new(n)};
    for (uint32_t i = 0U; i < a->n; i++) {
        uint64_t carry = 0ULL;
        for (uint32_t j = 0U; j < b->n; j++) {
            uint64_t p = (uint64_t)a->d[i] * b->d[j] + r.d[i + j] + carry;
            r.d[i + j] = (uint32_t)p;
            carry = p >> 32;
        }
        r.d[i + b->n] = (uint32_t)carry;
    }
    return r;
}

static void mag_norm(struct mag *m)
{
    while (m->n > 0U && m->d[m->n - 1U] == 0U)
        m->n--;
}

/* The quotient and remainder of the magnitudes a and b (b not zero), by
 * long division one bit at a time. */
static void mag_divmod(const struct mag *a, const struct mag *b, struct mag *q, struct mag *r)
{
    q->n = a->n;
    q->d = limbs_new(a->n);
    r->n = b->n + 1U;
    r->d = limbs_new(b->n + 1U);
    struct mag rr = {0U, r->d};
    for (uint32_t i = a->n * 32U; i > 0U; i--) {
        uint32_t bit = (a->d[(i - 1U) / 32U] >> ((i - 1U) % 32U)) & 1U;
        uint32_t carry = bit;
        for (uint32_t k = 0U; k < b->n + 1U; k++) {
            uint32_t nc = r->d[k] >> 31;
            r->d[k] = (r->d[k] << 1) | carry;
            carry = nc;
        }
        rr.n = b->n + 1U;
        mag_norm(&rr);
        if (mag_cmp(&rr, b) >= 0) {
            uint64_t borrow = 0ULL;
            for (uint32_t k = 0U; k < b->n + 1U; k++) {
                uint64_t av = r->d[k];
                uint64_t bv = (k < b->n ? (uint64_t)b->d[k] : 0ULL) + borrow;
                r->d[k] = (uint32_t)(av - bv);
                borrow = av < bv ? 1ULL : 0ULL;
            }
            q->d[(i - 1U) / 32U] |= 1U << ((i - 1U) % 32U);
        }
    }
    mag_norm(q);
    mag_norm(r);
}

static struct zint z_add(const struct zint *a, const struct zint *b)
{
    struct zint r;
    if (a->neg == b->neg) {
        r.neg = a->neg;
        r.m = mag_add(&a->m, &b->m);
    } else if (mag_cmp(&a->m, &b->m) >= 0) {
        r.neg = a->neg;
        r.m = mag_sub(&a->m, &b->m);
    } else {
        r.neg = b->neg;
        r.m = mag_sub(&b->m, &a->m);
    }
    norm(&r);
    return r;
}

static struct zint z_negated(struct zint z)
{
    if (z.m.n > 0U)
        z.neg = !z.neg;
    return z;
}

/* Truncated division (q rounds toward zero, r has a's sign). */
static void z_divmod_trunc(const struct zint *a, const struct zint *b, struct zint *q, struct zint *r)
{
    mag_divmod(&a->m, &b->m, &q->m, &r->m);
    q->neg = a->neg != b->neg;
    r->neg = a->neg;
    norm(q);
    norm(r);
}

/* Floor division (q rounds down, r has b's sign), as Z.div and Z.modulo;
 * b not zero. */
static void z_divmod_floor(const struct zint *a, const struct zint *b, struct zint *q, struct zint *r)
{
    z_divmod_trunc(a, b, q, r);
    if (r->m.n > 0U && r->neg != b->neg) {
        struct zint one = z_of_i64(1);
        struct zint m1 = z_negated(one);
        struct zint q2 = z_add(q, &m1);
        struct zint r2 = z_add(r, b);
        z_free(q);
        z_free(r);
        z_free(&one);
        *q = q2;
        *r = r2;
    }
}

/* The two's complement of z in n limbs. */
static uint32_t *twos(const struct zint *z, uint32_t n)
{
    uint32_t *d = limbs_new(n);
    for (uint32_t i = 0U; i < n && i < z->m.n; i++)
        d[i] = z->m.d[i];
    if (z->neg) {
        uint64_t carry = 1ULL;
        for (uint32_t i = 0U; i < n; i++) {
            uint64_t v = (uint64_t)(uint32_t)~d[i] + carry;
            d[i] = (uint32_t)v;
            carry = v >> 32;
        }
    }
    return d;
}

/* The integer whose two's complement in n limbs is d, which is freed. */
static struct zint untwos(uint32_t *d, uint32_t n)
{
    struct zint z = {0, {n, d}};
    if (n > 0U && (d[n - 1U] >> 31)) {
        z.neg = 1;
        uint64_t carry = 1ULL;
        for (uint32_t i = 0U; i < n; i++) {
            uint64_t v = (uint64_t)(uint32_t)~d[i] + carry;
            d[i] = (uint32_t)v;
            carry = v >> 32;
        }
    }
    norm(&z);
    return z;
}

/* a shifted left by k bits (k >= 0), keeping the sign. */
static struct zint z_shl(const struct zint *a, uint64_t k)
{
    if (a->m.n == 0U)
        return z_new(0U);
    if (k > (uint64_t)ANF_MAX_ARITY * 32ULL)
        anf_oom();
    uint32_t w = (uint32_t)(k / 32U), b = (uint32_t)(k % 32U);
    struct zint r = z_new(a->m.n + w + 1U);
    r.neg = a->neg;
    for (uint32_t i = 0U; i < a->m.n; i++) {
        uint64_t v = (uint64_t)a->m.d[i] << b;
        r.m.d[i + w] |= (uint32_t)v;
        r.m.d[i + w + 1U] |= (uint32_t)(v >> 32);
    }
    norm(&r);
    return r;
}

/* The magnitude m shifted right by k bits. */
static struct mag mag_shr(const struct mag *m, uint64_t k)
{
    uint64_t w = k / 32U;
    uint32_t b = (uint32_t)(k % 32U);
    if (w >= m->n) {
        struct mag r = {0U, limbs_new(0U)};
        return r;
    }
    uint32_t n = m->n - (uint32_t)w;
    struct mag r = {n, limbs_new(n)};
    for (uint32_t i = 0U; i < n; i++) {
        uint64_t lo = m->d[i + w];
        uint64_t hi = i + w + 1U < m->n ? m->d[i + w + 1U] : 0U;
        r.d[i] = (uint32_t)(((hi << 32) | lo) >> b);
    }
    mag_norm(&r);
    return r;
}

/* a shifted right by k bits, rounding down. */
static struct zint z_shr(const struct zint *a, uint64_t k)
{
    struct zint r;
    if (!a->neg) {
        r.neg = 0;
        r.m = mag_shr(&a->m, k);
        return r;
    }
    /* -((|a| - 1) >> k) - 1 */
    struct zint one = z_of_i64(1);
    struct mag m1 = mag_sub(&a->m, &one.m);
    mag_norm(&m1);
    struct mag s = mag_shr(&m1, k);
    struct zint t = {0, s};
    struct zint u = z_add(&t, &one);
    u = z_negated(u);
    free(m1.d);
    z_free(&t);
    z_free(&one);
    return u;
}

/* Whether the integer w is an immediate. */
#define IMM2(a, b) (ANF_IS_IMM(a) && ANF_IS_IMM(b))
#define S(a) ((int64_t)ANF_IMM_S31(a))

/* The int64 of z, if it has one. */
static int z_i64(const struct zint *z, int64_t *out)
{
    if (z->m.n > 2U)
        return 0;
    uint64_t mag = (z->m.n > 0U ? z->m.d[0] : 0U) | (z->m.n > 1U ? (uint64_t)z->m.d[1] << 32 : 0ULL);
    if (!z->neg) {
        if (mag > (uint64_t)INT64_MAX)
            return 0;
        *out = (int64_t)mag;
    } else {
        if (mag > (uint64_t)INT64_MAX + 1ULL)
            return 0;
        *out = (int64_t)(0ULL - mag);
    }
    return 1;
}

typedef struct zint (*zop2)(const struct zint *, const struct zint *);

static uint32_t big2(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b, zop2 op)
{
    struct zint x = z_load(arena, a), y = z_load(arena, b);
    struct zint r = op(&x, &y);
    z_free(&x);
    z_free(&y);
    return z_store(arena, st, &r);
}

static struct zint op_add(const struct zint *a, const struct zint *b) { return z_add(a, b); }
static struct zint op_sub(const struct zint *a, const struct zint *b)
{
    struct zint nb = *b;
    if (nb.m.n > 0U)
        nb.neg = !nb.neg;
    return z_add(a, &nb);
}
static struct zint op_mul(const struct zint *a, const struct zint *b)
{
    struct zint r = {a->neg != b->neg, mag_mul(&a->m, &b->m)};
    norm(&r);
    return r;
}

int32_t anf_p_cmp(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    (void)st;
    if (IMM2(a, b))
        return (S(a) > S(b)) - (S(a) < S(b));
    struct zint x = z_load(arena, a), y = z_load(arena, b);
    int c = z_cmp(&x, &y);
    z_free(&x);
    z_free(&y);
    return c;
}

uint32_t anf_p_add(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    if (IMM2(a, b))
        return store_i64(arena, st, S(a) + S(b));
    return big2(arena, st, a, b, op_add);
}

uint32_t anf_p_sub(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    if (IMM2(a, b))
        return store_i64(arena, st, S(a) - S(b));
    return big2(arena, st, a, b, op_sub);
}

uint32_t anf_p_mul(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    if (IMM2(a, b))
        return store_i64(arena, st, S(a) * S(b));
    return big2(arena, st, a, b, op_mul);
}

/* The integer a plus the small integer k. */
static uint32_t add_small(uint32_t *arena, struct anf_state *st, uint32_t a, int64_t k)
{
    if (ANF_IS_IMM(a))
        return store_i64(arena, st, S(a) + k);
    struct zint x = z_load(arena, a), y = z_of_i64(k);
    struct zint r = z_add(&x, &y);
    z_free(&x);
    z_free(&y);
    return z_store(arena, st, &r);
}

uint32_t anf_p_succ(uint32_t *arena, struct anf_state *st, uint32_t a) { return add_small(arena, st, a, 1); }
uint32_t anf_p_pred(uint32_t *arena, struct anf_state *st, uint32_t a) { return add_small(arena, st, a, -1); }

/* N.pred and Nat.pred: 0 for 0. */
uint32_t anf_p_pred0(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    return a == ANF_IMM(0U) ? a : add_small(arena, st, a, -1);
}

/* Pos.pred: 1 for 1. */
uint32_t anf_p_pred1(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    return a == ANF_IMM(1U) ? a : add_small(arena, st, a, -1);
}

uint32_t anf_p_neg(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    if (ANF_IS_IMM(a))
        return store_i64(arena, st, -S(a));
    struct zint x = z_load(arena, a);
    x = z_negated(x);
    return z_store(arena, st, &x);
}

uint32_t anf_p_abs(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    if (ANF_IS_IMM(a))
        return store_i64(arena, st, S(a) < 0 ? -S(a) : S(a));
    struct zint x = z_load(arena, a);
    x.neg = 0;
    return z_store(arena, st, &x);
}

/* Z.to_nat and Z.to_N: 0 for a negative integer. */
uint32_t anf_p_max0(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    (void)st;
    if (ANF_IS_IMM(a))
        return S(a) < 0 ? ANF_IMM(0U) : a;
    return ANF_HDR_ORD(arena[ANF_IDX(a)]) ? ANF_IMM(0U) : a;
}

/* ascii_of_nat and ascii_of_N: the character of the low byte. */
uint32_t anf_p_lowbyte(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    (void)st;
    if (ANF_IS_IMM(a))
        return ANF_IMM(ANF_IMM_U31(a) & 255U);
    return ANF_IMM(arena[ANF_IDX(a) + 1U] & 255U);
}

uint32_t anf_p_max(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    return anf_p_cmp(arena, st, a, b) >= 0 ? a : b;
}

uint32_t anf_p_min(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    return anf_p_cmp(arena, st, a, b) <= 0 ? a : b;
}

/* N.sub and Nat.sub: 0 when b is above a. */
uint32_t anf_p_sub0(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    return anf_p_cmp(arena, st, a, b) <= 0 ? ANF_IMM(0U) : anf_p_sub(arena, st, a, b);
}

/* Pos.sub: 1 when b is a or above. */
uint32_t anf_p_sub1(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    return anf_p_cmp(arena, st, a, b) <= 0 ? ANF_IMM(1U) : anf_p_sub(arena, st, a, b);
}

/* xI p and xO p: 2p + 1 and 2p. */
uint32_t anf_p_xI(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    return add_small(arena, st, anf_p_add(arena, st, a, a), 1);
}

uint32_t anf_p_xO(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    return anf_p_add(arena, st, a, a);
}

/* The bit k of the two's complement of a. */
static uint32_t bit_of(const uint32_t *arena, uint32_t a, uint64_t k)
{
    if (ANF_IS_IMM(a))
        return k >= 31U ? (S(a) < 0) : (uint32_t)((S(a) >> k) & 1);
    struct zint x = z_load(arena, a);
    uint32_t n = x.m.n + 1U;
    uint32_t r;
    if (k >= (uint64_t)n * 32U)
        r = x.neg;
    else {
        uint32_t *d = twos(&x, n);
        r = (d[k / 32U] >> (k % 32U)) & 1U;
        free(d);
    }
    z_free(&x);
    return r;
}

/* Half of a positive, rounded down: what xI p and xO p hold. */
uint32_t anf_p_half(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    if (ANF_IS_IMM(a))
        return ANF_IMM((uint32_t)(S(a) >> 1));
    struct zint x = z_load(arena, a);
    struct zint r = z_shr(&x, 1);
    z_free(&x);
    return z_store(arena, st, &r);
}

uint32_t anf_p_odd(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    (void)st;
    return bit_of(arena, a, 0);
}

uint32_t anf_p_even(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    (void)st;
    return bit_of(arena, a, 0) ^ 1U;
}

/* Whether the integer a, not zero, is above zero. */
uint32_t anf_p_zpos(uint32_t *arena, struct anf_state *st, uint32_t a)
{
    (void)st;
    if (ANF_IS_IMM(a))
        return S(a) > 0;
    return ANF_HDR_ORD(arena[ANF_IDX(a)]) == 0U;
}

/* Division: floor (Z.div, Z.modulo, and N's and nat's) or truncated
 * (Z.quot, Z.rem); by zero, the quotient is 0 and the remainder a. */
static uint32_t divide(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b, int floor, int rem)
{
    if (b == ANF_IMM(0U))
        return rem ? a : ANF_IMM(0U);
    if (IMM2(a, b)) {
        int64_t x = S(a), y = S(b), q = x / y, r = x % y;
        if (floor && r != 0 && ((r < 0) != (y < 0))) {
            q -= 1;
            r += y;
        }
        return store_i64(arena, st, rem ? r : q);
    }
    struct zint x = z_load(arena, a), y = z_load(arena, b), q, r;
    if (floor)
        z_divmod_floor(&x, &y, &q, &r);
    else
        z_divmod_trunc(&x, &y, &q, &r);
    z_free(&x);
    z_free(&y);
    if (rem) {
        z_free(&q);
        return z_store(arena, st, &r);
    }
    z_free(&r);
    return z_store(arena, st, &q);
}

uint32_t anf_p_div(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) { return divide(arena, st, a, b, 1, 0); }
uint32_t anf_p_mod(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) { return divide(arena, st, a, b, 1, 1); }
uint32_t anf_p_quot(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) { return divide(arena, st, a, b, 0, 0); }
uint32_t anf_p_rem(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) { return divide(arena, st, a, b, 0, 1); }

/* a to the power b; 0 for a negative b. */
uint32_t anf_p_pow(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    if (!ANF_IS_IMM(b)) {
        if (ANF_HDR_ORD(arena[ANF_IDX(b)]))
            return ANF_IMM(0U);
        if (a == ANF_IMM(0U) || a == ANF_IMM(1U))
            return a;
        anf_oom();
    }
    int64_t e = S(b);
    if (e < 0)
        return ANF_IMM(0U);
    struct zint r = z_of_i64(1), x = z_load(arena, a);
    while (e > 0) {
        if (e & 1) {
            struct zint t = op_mul(&r, &x);
            z_free(&r);
            r = t;
        }
        e >>= 1;
        if (e > 0) {
            struct zint t = op_mul(&x, &x);
            z_free(&x);
            x = t;
        }
    }
    z_free(&x);
    return z_store(arena, st, &r);
}

/* The bitwise and (0), or (1) or xor (2) of the two's complements. */
static uint32_t bitwise(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b, int op)
{
    if (IMM2(a, b)) {
        int32_t x = ANF_IMM_S31(a), y = ANF_IMM_S31(b);
        return ANF_IMM((uint32_t)(op == 0 ? (x & y) : op == 1 ? (x | y) : (x ^ y)));
    }
    struct zint x = z_load(arena, a), y = z_load(arena, b);
    uint32_t n = (x.m.n > y.m.n ? x.m.n : y.m.n) + 1U;
    uint32_t *dx = twos(&x, n), *dy = twos(&y, n);
    for (uint32_t i = 0U; i < n; i++)
        dx[i] = op == 0 ? (dx[i] & dy[i]) : op == 1 ? (dx[i] | dy[i]) : (dx[i] ^ dy[i]);
    free(dy);
    z_free(&x);
    z_free(&y);
    struct zint r = untwos(dx, n);
    return z_store(arena, st, &r);
}

uint32_t anf_p_land(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) { return bitwise(arena, st, a, b, 0); }
uint32_t anf_p_lor(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) { return bitwise(arena, st, a, b, 1); }
uint32_t anf_p_lxor(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) { return bitwise(arena, st, a, b, 2); }

/* a shifted left by b bits, or right when b is negative (Z.shiftl);
 * right shifts round down. */
static uint32_t shift(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b, int left)
{
    struct zint k = z_load(arena, b);
    int64_t kk;
    int ok = z_i64(&k, &kk);
    z_free(&k);
    if (!ok)
        kk = (ANF_HDR_ORD(arena[ANF_IDX(b)]) ? INT64_MIN / 2 : INT64_MAX / 2);
    if (!left)
        kk = -kk;
    struct zint x = z_load(arena, a), r;
    if (kk >= 0)
        r = z_shl(&x, (uint64_t)kk);
    else
        r = z_shr(&x, (uint64_t)-kk);
    z_free(&x);
    return z_store(arena, st, &r);
}

uint32_t anf_p_shiftl(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) { return shift(arena, st, a, b, 1); }
uint32_t anf_p_shiftr(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b) { return shift(arena, st, a, b, 0); }

/* Z.testbit: false for a negative index. */
uint32_t anf_p_testbit(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    (void)st;
    if (!ANF_IS_IMM(b))
        return ANF_HDR_ORD(arena[ANF_IDX(b)]) ? 0U : bit_of(arena, a, UINT64_MAX / 2);
    if (S(b) < 0)
        return 0U;
    return bit_of(arena, a, (uint64_t)S(b));
}

/* ## Strings */

#define SLICE_MIN 64U

static int s_is_slice(const uint32_t *arena, uint32_t s)
{
    return ANF_HDR_ST(arena[ANF_IDX(s)]) == ANF_ST_SCAN;
}

static uint32_t s_len(const uint32_t *arena, uint32_t s)
{
    if (ANF_IS_IMM(s))
        return 0U;
    return s_is_slice(arena, s) ? ANF_IMM_U31(arena[ANF_IDX(s) + 3U]) : arena[ANF_IDX(s) + 1U];
}

/* A non-empty string's bytes. */
static const uint8_t *s_bytes(const uint32_t *arena, uint32_t s)
{
    uint32_t idx = ANF_IDX(s);
    if (!s_is_slice(arena, s))
        return (const uint8_t *)(arena + idx + 2U);
    return (const uint8_t *)(arena + ANF_IDX(arena[idx + 1U]) + 2U) + ANF_IMM_U31(arena[idx + 2U]);
}

/* For a driver that prints a string: its length and, when it is not
 * empty, its bytes. */
const uint8_t *anf_str_bytes(const uint32_t *arena, uint32_t s, uint32_t *len)
{
    *len = s_len(arena, s);
    return *len ? s_bytes(arena, s) : NULL;
}

uint32_t anf_p_str_eqb(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    (void)st;
    uint32_t la = s_len(arena, a), lb = s_len(arena, b);
    if (la != lb)
        return 0U;
    return la == 0U || memcmp(s_bytes(arena, a), s_bytes(arena, b), la) == 0;
}

int32_t anf_p_str_compare(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    (void)st;
    uint32_t la = s_len(arena, a), lb = s_len(arena, b);
    uint32_t n = la < lb ? la : lb;
    int c = n ? memcmp(s_bytes(arena, a), s_bytes(arena, b), n) : 0;
    if (c != 0)
        return c < 0 ? -1 : 1;
    return (la > lb) - (la < lb);
}

uint32_t anf_p_str_length(uint32_t *arena, struct anf_state *st, uint32_t s)
{
    (void)st;
    return ANF_IMM(s_len(arena, s));
}

uint32_t anf_p_str_head(uint32_t *arena, struct anf_state *st, uint32_t s)
{
    (void)st;
    return ANF_IMM(s_bytes(arena, s)[0]);
}

/* Maps.string_hash s h: each byte folded in as (h * 31 + byte) mod 2^20,
 * which needs only h's low 20 bits. */
uint32_t anf_p_str_hash(uint32_t *arena, struct anf_state *st, uint32_t s, uint32_t h)
{
    (void)st;
    uint32_t v;
    if (ANF_IS_IMM(h))
        v = (uint32_t)ANF_IMM_S31(h);
    else {
        struct zint z = z_load(arena, h);
        uint32_t *d = twos(&z, z.m.n + 1U);
        v = d[0];
        free(d);
        z_free(&z);
    }
    v &= 0xFFFFFU;
    uint32_t n = s_len(arena, s);
    for (uint32_t i = 0U; i < n; i++)
        v = (v * 31U + s_bytes(arena, s)[i]) & 0xFFFFFU;
    return ANF_IMM(v);
}

/* List.length, whose first argument is the erased type. */
uint32_t anf_p_list_length(uint32_t *arena, struct anf_state *st, uint32_t l)
{
    (void)st;
    uint32_t n = 0U;
    while (!ANF_IS_IMM(l)) {
        n++;
        l = arena[ANF_IDX(l) + 2U];
    }
    return ANF_IMM(n);
}

/* ## Strings and lists that allocate, and may collect */

/* A new string of len bytes, len > 0, its bytes still to be written. */
static uint32_t s_alloc(uint32_t *arena, struct anf_state *st, uint32_t len)
{
    if (len > (ANF_MAX_ARITY - 1U) * 4U)
        anf_oom();
    uint32_t data = (len + 3U) >> 2;
    uint32_t idx = anf_alloc_words(arena, st, 2U + data);
    arena[idx] = ANF_HDR(1U + data, ANF_ST_BYTES, 0U);
    arena[idx + 1U] = len;
    arena[idx + 1U + data] = 0U;
    return idx;
}

static uint8_t *w_bytes(uint32_t *arena, uint32_t idx)
{
    return (uint8_t *)(arena + idx + 2U);
}

/* String c s. */
uint32_t anf_p_str_cons(uint32_t *arena, struct anf_state *st, uint32_t c, uint32_t s)
{
    uint32_t len = s_len(arena, s) + 1U;
    anf_root_push(st, s);
    uint32_t idx = s_alloc(arena, st, len);
    s = anf_root_pop(st);
    w_bytes(arena, idx)[0] = (uint8_t)ANF_IMM_U31(c);
    if (len > 1U)
        memcpy(w_bytes(arena, idx) + 1, s_bytes(arena, s), len - 1U);
    return ANF_BOX(idx);
}

/* The string from the byte at off on, len of them: a copy when short,
 * else a slice of the bytes block under s. */
static uint32_t s_slice(uint32_t *arena, struct anf_state *st, uint32_t s, uint32_t off, uint32_t len)
{
    if (len == 0U)
        return ANF_IMM(0U);
    anf_root_push(st, s);
    uint32_t idx = len < SLICE_MIN ? s_alloc(arena, st, len) : anf_alloc_words(arena, st, 4U);
    s = anf_root_pop(st);
    if (len < SLICE_MIN) {
        memcpy(w_bytes(arena, idx), s_bytes(arena, s) + off, len);
        return ANF_BOX(idx);
    }
    uint32_t base = s, at = off;
    if (s_is_slice(arena, s)) {
        base = arena[ANF_IDX(s) + 1U];
        at += ANF_IMM_U31(arena[ANF_IDX(s) + 2U]);
    }
    arena[idx] = ANF_HDR(3U, ANF_ST_SCAN, 0U);
    arena[idx + 1U] = base;
    arena[idx + 2U] = ANF_IMM(at);
    arena[idx + 3U] = ANF_IMM(len);
    return ANF_BOX(idx);
}

/* The rest of a string after its first byte. */
uint32_t anf_p_str_tail(uint32_t *arena, struct anf_state *st, uint32_t s)
{
    return s_slice(arena, st, s, 1U, s_len(arena, s) - 1U);
}

/* String.substring n m s: m bytes from n on, as many as there are. */
uint32_t anf_p_substring(uint32_t *arena, struct anf_state *st, uint32_t n, uint32_t m, uint32_t s)
{
    uint32_t len = s_len(arena, s);
    uint64_t from = ANF_IS_IMM(n) ? ANF_IMM_U31(n) : UINT64_MAX;
    uint64_t want = ANF_IS_IMM(m) ? ANF_IMM_U31(m) : UINT64_MAX;
    if (from >= len)
        return ANF_IMM(0U);
    if (want > len - from)
        want = len - from;
    return s_slice(arena, st, s, (uint32_t)from, (uint32_t)want);
}

uint32_t anf_p_str_append(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b)
{
    if (ANF_IS_IMM(a))
        return b;
    if (ANF_IS_IMM(b))
        return a;
    uint32_t la = s_len(arena, a), lb = s_len(arena, b);
    if (lb > (ANF_MAX_ARITY - 1U) * 4U - la)
        anf_oom();
    anf_root_push(st, a);
    anf_root_push(st, b);
    uint32_t idx = s_alloc(arena, st, la + lb);
    b = anf_root_pop(st);
    a = anf_root_pop(st);
    memcpy(w_bytes(arena, idx), s_bytes(arena, a), la);
    memcpy(w_bytes(arena, idx) + la, s_bytes(arena, b), lb);
    return ANF_BOX(idx);
}

/* String.concat sep l: the strings of l with sep between them. */
uint32_t anf_p_str_concat(uint32_t *arena, struct anf_state *st, uint32_t sep, uint32_t l,
                          uint32_t nil, uint32_t cons)
{
    (void)nil;
    (void)cons;
    uint64_t total = 0U, count = 0U;
    for (uint32_t k = l; !ANF_IS_IMM(k); k = arena[ANF_IDX(k) + 2U]) {
        total += s_len(arena, arena[ANF_IDX(k) + 1U]);
        count++;
    }
    if (count > 1U)
        total += (count - 1U) * s_len(arena, sep);
    if (total == 0U)
        return ANF_IMM(0U);
    if (total > (uint64_t)(ANF_MAX_ARITY - 1U) * 4U)
        anf_oom();
    anf_root_push(st, sep);
    anf_root_push(st, l);
    uint32_t idx = s_alloc(arena, st, (uint32_t)total);
    l = anf_root_pop(st);
    sep = anf_root_pop(st);
    uint8_t *out = w_bytes(arena, idx);
    uint32_t at = 0U;
    for (uint32_t k = l; !ANF_IS_IMM(k); k = arena[ANF_IDX(k) + 2U]) {
        if (k != l) {
            uint32_t n = s_len(arena, sep);
            if (n)
                memcpy(out + at, s_bytes(arena, sep), n);
            at += n;
        }
        uint32_t e = arena[ANF_IDX(k) + 1U];
        uint32_t n = s_len(arena, e);
        if (n)
            memcpy(out + at, s_bytes(arena, e), n);
        at += n;
    }
    return ANF_BOX(idx);
}

/* The string of a list of characters, in its order (string_of_list_ascii)
 * or reversed (IrText.string_of_rev). */
static uint32_t of_list(uint32_t *arena, struct anf_state *st, uint32_t l, int reversed)
{
    uint64_t n = 0U;
    for (uint32_t k = l; !ANF_IS_IMM(k); k = arena[ANF_IDX(k) + 2U])
        n++;
    if (n == 0U)
        return ANF_IMM(0U);
    if (n > (uint64_t)(ANF_MAX_ARITY - 1U) * 4U)
        anf_oom();
    anf_root_push(st, l);
    uint32_t idx = s_alloc(arena, st, (uint32_t)n);
    l = anf_root_pop(st);
    uint8_t *out = w_bytes(arena, idx);
    uint32_t i = 0U;
    for (uint32_t k = l; !ANF_IS_IMM(k); k = arena[ANF_IDX(k) + 2U], i++)
        out[reversed ? (uint32_t)n - 1U - i : i] = (uint8_t)ANF_IMM_U31(arena[ANF_IDX(k) + 1U]);
    return ANF_BOX(idx);
}

uint32_t anf_p_str_of_list(uint32_t *arena, struct anf_state *st, uint32_t l, uint32_t nil, uint32_t cons)
{
    (void)nil;
    (void)cons;
    return of_list(arena, st, l, 0);
}

uint32_t anf_p_str_of_rev(uint32_t *arena, struct anf_state *st, uint32_t l, uint32_t nil, uint32_t cons)
{
    (void)nil;
    (void)cons;
    return of_list(arena, st, l, 1);
}

/* list_ascii_of_string: the list of a string's characters, cons cells of
 * the header cons ending in nil, allocated together. */
uint32_t anf_p_list_of_str(uint32_t *arena, struct anf_state *st, uint32_t s, uint32_t nil, uint32_t cons)
{
    uint32_t n = s_len(arena, s);
    if (n == 0U)
        return nil;
    if ((uint64_t)n * 3U > ANF_MAX_ARITY)
        anf_oom();
    anf_root_push(st, s);
    uint32_t idx = anf_alloc_words(arena, st, 3U * n);
    s = anf_root_pop(st);
    for (uint32_t i = 0U; i < n; i++) {
        uint32_t c = idx + 3U * i;
        arena[c] = cons;
        arena[c + 1U] = ANF_IMM(s_bytes(arena, s)[i]);
        arena[c + 2U] = i + 1U < n ? ANF_BOX(c + 3U) : nil;
    }
    return ANF_BOX(idx);
}
