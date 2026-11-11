/* 32-bit single-arena runtime and Cheney minor collector for λANF on Nanofil IR
 * (nanofil/docs/lambda-anf.md, M1).
 *
 * Every functional value is one 32-bit word (class w):
 *   - bit 0 == 1: immediate ((val << 1) | 1), for 0-ary constructors, ascii
 *     bytes, function IDs, and signed 31-bit integers in [-2^30, 2^30 - 1].
 *   - bit 0 == 0: boxed block at arena word index idx = w >> 1 (1 <= idx < 2^31;
 *     word 0 is reserved).
 *
 * Boxed block layout at arena[idx .. idx + arity] (arity >= 1):
 *   - arena[idx]: header (arity << 10) | (st << 8) | ord
 *       st == 0 (ANF_ST_SCAN):   constructor/closure; fields 1..arity are w words
 *       st == 1 (ANF_ST_BYTES):  packed bytes; field 1 is byte_len, 2..arity raw bytes
 *       st == 2 (ANF_ST_BIGINT): normalized Z bigint; ord 0=pos/1=neg, 1..arity u32 limbs
 *       0xFFFFFFFFU:             Cheney forwarding header; forwarded dst in arena[idx + 1]
 */
#ifndef NANOFIL_ANF_ARENA_H
#define NANOFIL_ANF_ARENA_H

#include <stddef.h>
#include <stdint.h>

#define ANF_IMM(v)          (((uint32_t)(v) << 1) | 1U)
#define ANF_IS_IMM(w)       (((w) & 1U) != 0U)
#define ANF_IMM_S31(w)      ((int32_t)(w) >> 1)
#define ANF_IMM_U31(w)      ((uint32_t)(w) >> 1)

#define ANF_BOX(idx)        ((uint32_t)(idx) << 1)
#define ANF_IDX(w)          ((uint32_t)(w) >> 1)

#define ANF_ST_SCAN         0U
#define ANF_ST_BYTES        1U
#define ANF_ST_BIGINT       2U
#define ANF_FWD_HDR         0xFFFFFFFFU
#define ANF_MAX_ARITY       0x3FFFFFU

#define ANF_HDR(arity, st, ord) \
    (((uint32_t)(arity) << 10) | (((uint32_t)(st) & 3U) << 8) | ((uint32_t)(ord) & 0xFFU))
#define ANF_HDR_ARITY(hdr)  ((uint32_t)(hdr) >> 10)
#define ANF_HDR_ST(hdr)     (((uint32_t)(hdr) >> 8) & 3U)
#define ANF_HDR_ORD(hdr)    ((uint32_t)(hdr) & 0xFFU)

#define ANF_Z_MIN_IMM       (-(1LL << 30))
#define ANF_Z_MAX_IMM       ((1LL << 30) - 1LL)

#define ANF_MAX_SLAB_WORDS      (1U << 31)
#define ANF_GUARD_WORDS         1024U
#define ANF_DEFAULT_NURSERY     (1U << 20)
#define ANF_DEFAULT_ROOT_CAP    (1U << 18)

struct anf_state {
    uint32_t young_idx;
    uint32_t major_idx;
    uint32_t nursery_base;
    uint32_t nursery_end;
    uint32_t major_limit;
    uint32_t root_sp;
    uint32_t root_cap;
    uint32_t major_hwm;
    uint64_t slab_bytes;
    uint64_t state_bytes;
    uint64_t gc_count;
    uint64_t promoted_words;
};

static inline uint32_t *anf_roots(struct anf_state *st) {
    return (uint32_t *)(st + 1);
}

void anf_oom(void);
int anf_arena_init(uint32_t **arena_out, struct anf_state **st_out,
                   uint32_t slab_words, uint32_t nursery_words, uint32_t root_cap);
int anf_arena_reset(uint32_t *arena, struct anf_state *st, uint32_t madvise_threshold_words);
/* Back to the state when the major heap was mark words long, with an
   empty nursery and no roots: what a program put below mark, such as
   its constants, stays. The pages above mark go back to the kernel
   (MADV_DONTNEED) when the heap had grown more than
   madvise_threshold_words past it. -1 for a mark past the major heap. */
int anf_arena_rewind(uint32_t *arena, struct anf_state *st, uint32_t mark,
                     uint32_t madvise_threshold_words);
int anf_arena_destroy(uint32_t *arena, struct anf_state *st);

void anf_minor_gc(uint32_t *arena, uint32_t *roots, struct anf_state *st);
uint32_t anf_alloc_words(uint32_t *arena, struct anf_state *st, uint32_t words);

void anf_root_push(struct anf_state *st, uint32_t w);
uint32_t anf_root_pop(struct anf_state *st);
uint32_t *anf_root_frame(struct anf_state *st, uint32_t n);

uint32_t anf_bytes_from_buf(uint32_t *arena, struct anf_state *st,
                            const uint8_t *buf, uint32_t len);
uint32_t anf_bytes_len(const uint32_t *arena, uint32_t s);
uint32_t anf_bytes_get(const uint32_t *arena, uint32_t s, uint32_t i);
void anf_bytes_copy_out(const uint32_t *arena, uint32_t s, uint8_t *dst);
int anf_bytes_cmp(const uint32_t *arena, uint32_t a, uint32_t b);
uint32_t anf_bytes_concat(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b);

uint32_t anf_z_of_i64(uint32_t *arena, struct anf_state *st, int64_t v);
uint32_t anf_z_of_u64(uint32_t *arena, struct anf_state *st, uint64_t u);
int anf_z_to_i64(const uint32_t *arena, uint32_t z, int64_t *out);
int anf_z_cmp(const uint32_t *arena, uint32_t a, uint32_t b);
uint32_t anf_z_neg(uint32_t *arena, struct anf_state *st, uint32_t a);
uint32_t anf_z_add(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b);
uint32_t anf_z_sub(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b);
uint32_t anf_z_mul(uint32_t *arena, struct anf_state *st, uint32_t a, uint32_t b);

#endif
