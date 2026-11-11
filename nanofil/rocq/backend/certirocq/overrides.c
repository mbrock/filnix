#include <stdint.h>
#include <stdlib.h>
#include "gc_stack.h"
#include "glue.h"

#define is_ptr(x) Is_block(x)

extern value ascii_vals[256];

/* Static Peano nat chain: nat_blocks[k] = S(nat_blocks[k-1]), 1 <= k < MAX_STATIC_NAT.
 * Because nat_blocks is in static storage (outside GC from-space), the GC never scans
 * or copies it, while Gallina pattern-matching sees ordinary S / O constructors, and
 * nat_to_u64 / make_nat are O(1) pointer arithmetic with zero heap allocation! */
#define MAX_STATIC_NAT 4194304
static value nat_blocks[MAX_STATIC_NAT][2];
static uint32_t nat_ready_up_to = 0;

static value make_nat(uint64_t n) {
  if (n == 0) return (value)1LL;
  if (n >= MAX_STATIC_NAT) n = MAX_STATIC_NAT - 1;
  if (n > nat_ready_up_to) {
    for (uint32_t k = nat_ready_up_to + 1; k <= (uint32_t)n; k++) {
      nat_blocks[k][0] = (value)1024LL;
      nat_blocks[k][1] = (k == 1) ? (value)1LL : (value)(&nat_blocks[k - 1][1]);
    }
    nat_ready_up_to = (uint32_t)n;
  }
  return (value)(&nat_blocks[n][1]);
}

static uint64_t nat_to_u64(value v) {
  if (!is_ptr(v)) return 0;
  uintptr_t lo = (uintptr_t)(&nat_blocks[1][0]);
  uintptr_t hi = (uintptr_t)(&nat_blocks[MAX_STATIC_NAT - 1][1]);
  uintptr_t pv0 = (uintptr_t)v;
  if (pv0 >= lo && pv0 <= hi) {
    return (uint64_t)(((value *)v - &nat_blocks[0][1]) / 2);
  }
  value top = v;
  uint64_t acc = 0;
  while (is_ptr(v)) {
    uintptr_t pv = (uintptr_t)v;
    if (pv >= lo && pv <= hi) {
      uint64_t idx = (uint64_t)(((value *)v - &nat_blocks[0][1]) / 2);
      uint64_t total = acc + idx;
      if (total > 0 && total < MAX_STATIC_NAT) {
        Field(top, 0) = make_nat(total - 1);
      }
      return total;
    }
    acc++;
    v = Field(v, 0);
  }
  if (acc > 0 && acc < MAX_STATIC_NAT) {
    Field(top, 0) = make_nat(acc - 1);
  }
  return acc;
}

/* Ascii helper */
static inline unsigned char ascii_code(value ch) {
  uintptr_t p = (uintptr_t)ch;
  uintptr_t a0 = (uintptr_t)ascii_vals[0];
  uintptr_t a255 = (uintptr_t)ascii_vals[255];
  if (p >= a0 && p <= a255) {
    return (unsigned char)((p - a0) / (9 * sizeof(value)));
  }
  unsigned char c = 0;
  for (int b = 0; b < 8; b++) {
    if (Field(ch, b) == (value)3LL) c |= (unsigned char)(1u << b);
  }
  return c;
}

/* Ascii.eqb (c1, c2) -> bool (true = 3LL, false = 1LL) */
value f_case_known_505884(struct thread_info *tinfo, value c1, value c2) {
  (void)tinfo;
  if (c1 == c2) return (value)3LL;
  return (ascii_code(c1) == ascii_code(c2)) ? (value)3LL : (value)1LL;
}

/* String.eqb (s1, s2) -> bool (true = 3LL, false = 1LL) */
value f_case_known_505857(struct thread_info *tinfo, value s1, value s2) {
  (void)tinfo;
  while (is_ptr(s1) && is_ptr(s2)) {
    if (s1 == s2) return (value)3LL;
    if (ascii_code(Field(s1, 0)) != ascii_code(Field(s2, 0)))
      return (value)1LL;
    s1 = Field(s1, 1);
    s2 = Field(s2, 1);
  }
  return (is_ptr(s1) == is_ptr(s2)) ? (value)3LL : (value)1LL;
}

/* Pos.compare_cont: f_case_known_504260(tinfo, x, y, r) -> comparison (Eq=1LL, Lt=3LL, Gt=5LL) */
value f_case_known_504260(struct thread_info *tinfo, value x, value y, value r) {
  (void)tinfo;
  while (is_ptr(x) && is_ptr(y)) {
    if (x == y) return r;
    int tx = (int)(((intnat)Field(x, -1)) & 255);
    int ty = (int)(((intnat)Field(y, -1)) & 255);
    if (tx != ty) {
      r = (tx == 0) ? (value)5LL : (value)3LL;
    }
    x = Field(x, 0);
    y = Field(y, 0);
  }
  if (is_ptr(x)) return (value)5LL;
  if (is_ptr(y)) return (value)3LL;
  return r;
}

value y_uncurried_known_504189(struct thread_info *tinfo, value y, value x, value r) {
  return f_case_known_504260(tinfo, x, y, r);
}

/* String.compare: f_case_known_531006(tinfo, s1, env, s2) -> comparison (Eq=1LL, Lt=3LL, Gt=5LL) */
value f_case_known_531006(struct thread_info *tinfo, value s1, value env, value s2) {
  (void)tinfo;
  (void)env;
  while (is_ptr(s1) && is_ptr(s2)) {
    if (s1 == s2) return (value)1LL;
    value c1 = Field(s1, 0), c2 = Field(s2, 0);
    if (c1 != c2) {
      unsigned char b1 = ascii_code(c1), b2 = ascii_code(c2);
      if (b1 < b2) return (value)3LL;
      if (b1 > b2) return (value)5LL;
    }
    s1 = Field(s1, 1);
    s2 = Field(s2, 1);
  }
  if (is_ptr(s1)) return (value)5LL;
  if (is_ptr(s2)) return (value)3LL;
  return (value)1LL;
}

/* Decode/encode CertiRocq positive and Z */
static uint64_t pos_to_u64(value p) {
  uint64_t v = 0;
  unsigned int shift = 0;
  while (is_ptr(p)) {
    int tag = (int)(((intnat)Field(p, -1)) & 255);
    if (tag == 0) v |= (1ULL << shift);
    shift++;
    p = Field(p, 0);
  }
  v |= (1ULL << shift);
  return v;
}

static int64_t z_to_i64(value z) {
  if (!is_ptr(z)) return 0;
  int tag = (int)(((intnat)Field(z, -1)) & 255);
  uint64_t mag = pos_to_u64(Field(z, 0));
  return (tag == 0) ? (int64_t)mag : -(int64_t)mag;
}

/* Static table of all positive values 1..1048575 and Zpos 1..1048575 */
static value pos_small_blocks[1048576][2];
static value z_pos_small_blocks[1048576][2];
static int pos_table_ready = 0;

static void ensure_pos_table(void) {
  if (pos_table_ready) return;
  for (uint32_t n = 1; n < 1048576; n++) {
    if (n >= 2) {
      uint32_t half = n >> 1;
      value parent = (half == 1) ? (value)1LL : (value)(&pos_small_blocks[half][1]);
      pos_small_blocks[n][0] = (n & 1) ? (value)1024LL : (value)1025LL;
      pos_small_blocks[n][1] = parent;
    }
    value p = (n == 1) ? (value)1LL : (value)(&pos_small_blocks[n][1]);
    z_pos_small_blocks[n][0] = (value)1024LL;
    z_pos_small_blocks[n][1] = p;
  }
  pos_table_ready = 1;
}

static value u64_to_pos(struct thread_info *tinfo, uint64_t n) {
  if (n <= 1) return (value)1LL;
  ensure_pos_table();
  if (n < 1048576) return (value)(&pos_small_blocks[n][1]);
  /* Build from MSB down until < 1048576 */
  uint64_t bits[64];
  int k = 0;
  while (n >= 1048576) {
    bits[k++] = n & 1;
    n >>= 1;
  }
  if (tinfo->limit - tinfo->alloc < 2 * k + 4) {
    tinfo->nalloc = 2 * k + 4;
    garbage_collect(tinfo);
  }
  value cur = (n == 1) ? (value)1LL : (value)(&pos_small_blocks[n][1]);
  for (int i = k - 1; i >= 0; i--) {
    value *p = tinfo->alloc;
    tinfo->alloc += 2;
    p[0] = bits[i] ? (value)1024LL : (value)1025LL;
    p[1] = cur;
    cur = (value)(p + 1);
  }
  return cur;
}

static value i64_to_z(struct thread_info *tinfo, int64_t z) {
  if (z == 0) return (value)1LL;
  ensure_pos_table();
  if (z > 0 && z < 1048576) return (value)(&z_pos_small_blocks[z][1]);
  uint64_t mag = (z > 0) ? (uint64_t)z : (uint64_t)(-z);
  value p = u64_to_pos(tinfo, mag);
  if (tinfo->limit - tinfo->alloc < 4) {
    value roots[1] = { p };
    struct stack_frame frame = { .next = roots + 1, .root = roots, .prev = tinfo->fp };
    tinfo->fp = &frame;
    tinfo->nalloc = 4;
    garbage_collect(tinfo);
    tinfo->fp = frame.prev;
    p = roots[0];
  }
  value *blk = tinfo->alloc;
  tinfo->alloc += 2;
  blk[0] = (z > 0) ? (value)1024LL : (value)1025LL;
  blk[1] = p;
  return (value)(blk + 1);
}

/* Maps.hash_step */
value NanofildMapsdhash_step_uncurried_17156(struct thread_info *tinfo, value env, value x, value h) {
  (void)env;
  int64_t hv = z_to_i64(h);
  int64_t xv = z_to_i64(x);
  int64_t rem = (hv * 31 + xv) % 1048576;
  if (rem < 0) rem += 1048576;
  return i64_to_z(tinfo, rem);
}

/* Maps.string_hash */
value f_case_known_509515(struct thread_info *tinfo, value s, value hash_step_clo, value h) {
  (void)hash_step_clo;
  if (!is_ptr(s)) return h;
  int64_t hv = z_to_i64(h);
  while (is_ptr(s)) {
    unsigned char c = ascii_code(Field(s, 0));
    hv = (hv * 31 + (int64_t)c) % 1048576;
    if (hv < 0) hv += 1048576;
    s = Field(s, 1);
  }
  return i64_to_z(tinfo, hv);
}

/* nat_of_ascii & ascii_of_nat */
value StdlibdStringsdAsciidnat_of_ascii_known_502635(struct thread_info *tinfo, value a) {
  (void)tinfo;
  return make_nat(ascii_code(a));
}

value StdlibdStringsdAsciidascii_of_nat_known_504633(struct thread_info *tinfo, value n, value z, value o, value y) {
  (void)tinfo; (void)z; (void)o; (void)y;
  return ascii_vals[nat_to_u64(n) & 255];
}

/* Pos.to_nat, Z.to_nat, Z.of_nat */
value CorelibdBinNumsdPosDefdPosdto_nat_known_502300(struct thread_info *tinfo, value x) {
  (void)tinfo;
  return make_nat(pos_to_u64(x));
}

value CorelibdBinNumsdIntDefdZdto_nat_known_504654(struct thread_info *tinfo, value z) {
  (void)tinfo;
  int64_t v = z_to_i64(z);
  return (v <= 0) ? (value)1LL : make_nat((uint64_t)v);
}

value CorelibdBinNumsdIntDefdZdof_nat_known_503816(struct thread_info *tinfo, value n) {
  return i64_to_z(tinfo, (int64_t)nat_to_u64(n));
}

/* Nat.add, Nat.sub, Nat.eqb, Nat.leb, Nat.compare, Regs.nat_leb, Regs.nat_ltb */
value f_case_known_502275(struct thread_info *tinfo, value n, value m) {
  (void)tinfo;
  return make_nat(nat_to_u64(n) + nat_to_u64(m));
}

value f_case_known_503847(struct thread_info *tinfo, value n, value m, value n2) {
  (void)tinfo; (void)n2;
  uint64_t nv = nat_to_u64(n), mv = nat_to_u64(m);
  return (nv <= mv) ? (value)1LL : make_nat(nv - mv);
}

value f_case_known_502700(struct thread_info *tinfo, value n, value m) {
  (void)tinfo;
  if (n == m) return (value)3LL;
  return (nat_to_u64(n) == nat_to_u64(m)) ? (value)3LL : (value)1LL;
}

value f_case_known_502804(struct thread_info *tinfo, value n, value m) {
  (void)tinfo;
  if (n == m) return (value)3LL;
  return (nat_to_u64(n) <= nat_to_u64(m)) ? (value)3LL : (value)1LL;
}

value f_case_known_530876(struct thread_info *tinfo, value n, value m) {
  (void)tinfo;
  if (n == m) return (value)1LL;
  uint64_t nv = nat_to_u64(n), mv = nat_to_u64(m);
  return (nv == mv) ? (value)1LL : (nv < mv) ? (value)3LL : (value)5LL;
}

value BackenddRegsdnat_leb_uncurried_known_629219(struct thread_info *tinfo, value b, value a) {
  (void)tinfo;
  return (nat_to_u64(a) <= nat_to_u64(b)) ? (value)3LL : (value)1LL;
}

value BackenddRegsdnat_ltb_uncurried_known_629304(struct thread_info *tinfo, value b, value a) {
  (void)tinfo;
  return (nat_to_u64(a) < nat_to_u64(b)) ? (value)3LL : (value)1LL;
}

/* IrText.count: f_case_known_507007(tinfo, cs, n) */
value f_case_known_507007(struct thread_info *tinfo, value cs, value n) {
  (void)tinfo;
  uint64_t acc = nat_to_u64(n);
  while (is_ptr(cs)) {
    acc++;
    cs = Field(cs, 1);
  }
  return make_nat(acc);
}

/* List.rev_append: f_case_known_503195(tinfo, l, lp) */
value f_case_known_503195(struct thread_info *tinfo, value l, value lp) {
  if (!is_ptr(l)) return lp;
  value roots[2] = { l, lp };
  struct stack_frame frame = { .next = roots + 2, .root = roots, .prev = tinfo->fp };
  tinfo->fp = &frame;
  while (is_ptr(roots[0])) {
    if (tinfo->limit - tinfo->alloc < 4) {
      tinfo->nalloc = 4;
      garbage_collect(tinfo);
    }
    value hd = Field(roots[0], 0);
    roots[0] = Field(roots[0], 1);
    value *cell = tinfo->alloc;
    tinfo->alloc += 3;
    cell[0] = (value)2048LL;
    cell[1] = hd;
    cell[2] = roots[1];
    roots[1] = (value)(cell + 1);
  }
  tinfo->fp = frame.prev;
  return roots[1];
}

/* IrText.string_of_rev: BackenddIrTextdstring_of_rev_known_503223(tinfo, cs) */
value BackenddIrTextdstring_of_rev_known_503223(struct thread_info *tinfo, value cs) {
  if (!is_ptr(cs)) return (value)1LL;
  value roots[2] = { cs, (value)1LL };
  struct stack_frame frame = { .next = roots + 2, .root = roots, .prev = tinfo->fp };
  tinfo->fp = &frame;
  while (is_ptr(roots[0])) {
    if (tinfo->limit - tinfo->alloc < 4) {
      tinfo->nalloc = 4;
      garbage_collect(tinfo);
    }
    value c = Field(roots[0], 0);
    roots[0] = Field(roots[0], 1);
    value *cell = tinfo->alloc;
    tinfo->alloc += 3;
    cell[0] = (value)2048LL;
    cell[1] = c;
    cell[2] = roots[1];
    roots[1] = (value)(cell + 1);
  }
  tinfo->fp = frame.prev;
  return roots[1];
}

/* term_eqb: f_case_known_511259(tinfo, t, u) */
value f_case_known_511259(struct thread_info *tinfo, value t, value u) {
  if (t == u) return (value)3LL;
  int tt = (int)(((intnat)Field(t, -1)) & 255);
  int ut = (int)(((intnat)Field(u, -1)) & 255);
  if (tt != ut) return (value)1LL;
  switch (tt) {
    case 0: /* TInt */
      return (z_to_i64(Field(t, 0)) == z_to_i64(Field(u, 0))) ? (value)3LL : (value)1LL;
    case 1: /* TAtom */
      return f_case_known_505857(tinfo, Field(t, 0), Field(u, 0));
    case 2: { /* TApp f args */
      if (f_case_known_505857(tinfo, Field(t, 0), Field(u, 0)) == (value)1LL)
        return (value)1LL;
      value l1 = Field(t, 1), l2 = Field(u, 1);
      while (is_ptr(l1) && is_ptr(l2)) {
        if (f_case_known_511259(tinfo, Field(l1, 0), Field(l2, 0)) == (value)1LL)
          return (value)1LL;
        l1 = Field(l1, 1);
        l2 = Field(l2, 1);
      }
      return (is_ptr(l1) == is_ptr(l2)) ? (value)3LL : (value)1LL;
    }
    case 3: { /* TList ts */
      value l1 = Field(t, 0), l2 = Field(u, 0);
      while (is_ptr(l1) && is_ptr(l2)) {
        if (f_case_known_511259(tinfo, Field(l1, 0), Field(l2, 0)) == (value)1LL)
          return (value)1LL;
        l1 = Field(l1, 1);
        l2 = Field(l2, 1);
      }
      return (is_ptr(l1) == is_ptr(l2)) ? (value)3LL : (value)1LL;
    }
    default:
      return (value)1LL;
  }
}

/* Also override f_case_known_530885 (called by curried Nat.compare in sort Nat.compare) */
value f_case_known_530885(struct thread_info *tinfo, value m, value np) {
  /* In f_case_known_530885(tinfo, m, np), n = S np, and m is being matched */
  if (!is_ptr(m)) return (value)5LL; /* n = S np > O = m -> Gt (5LL) */
  return f_case_known_530876(tinfo, np, Field(m, 0));
}

/* Term.lookup: f_case_known_511786(tinfo, ps, k) */
value f_case_known_511786(struct thread_info *tinfo, value ps, value k) {
  while (is_ptr(ps)) {
    value pair = Field(ps, 0);
    if (f_case_known_511259(tinfo, k, Field(pair, 0)) == (value)3LL) {
      value val = Field(pair, 1);
      if (tinfo->limit - tinfo->alloc < 4) {
        value roots[1] = { val };
        struct stack_frame frame = { .next = roots + 1, .root = roots, .prev = tinfo->fp };
        tinfo->fp = &frame;
        tinfo->nalloc = 4;
        garbage_collect(tinfo);
        tinfo->fp = frame.prev;
        val = roots[0];
      }
      return alloc_make_Corelib_Init_Datatypes_option_Some(tinfo, val);
    }
    ps = Field(ps, 1);
  }
  return (value)1LL;
}

/* Term.put: NanofildTermdput_uncurried_uncurried_uncurried_known_511372(tinfo, ps, v, k)
 * In Term.v: Fixpoint put k v ps := match ps with [] => [(k, v)] | (k', v') :: ps' => if name_eqb k k' then (k, v) :: ps' else (k', v') :: put k v ps' end
 * Wait: let's check Term.v's exact definition of put! */

value NanofildTermdput_uncurried_uncurried_uncurried_known_511372(struct thread_info *tinfo, value ps, value v, value k) {
  /* Fast path: check if k is in ps */
  int found = 0;
  for (value cur = ps; is_ptr(cur); cur = Field(cur, 1)) {
    value pair = Field(cur, 0);
    if (f_case_known_511259(tinfo, k, Field(pair, 0)) == (value)3LL) {
      found = 1;
      break;
    }
  }
  value roots[4] = { ps, v, k, (value)1LL };
  struct stack_frame frame = { .next = roots + 4, .root = roots, .prev = tinfo->fp };
  tinfo->fp = &frame;
  if (found) {
    /* Rebuild filtered list in reverse, then reverse onto [] */
    value rev = (value)1LL;
    roots[3] = rev;
    while (is_ptr(roots[0])) {
      value pair = Field(roots[0], 0);
      roots[0] = Field(roots[0], 1);
      if (f_case_known_511259(tinfo, roots[2], Field(pair, 0)) == (value)1LL) {
        if (tinfo->limit - tinfo->alloc < 4) {
          /* Save pair via roots[0] isn't needed if we check before loading pair, so let's re-read */
        }
      }
    }
    /* Simpler: two-pass count or recursive/stack filter */
  }
  tinfo->fp = frame.prev;
  if (!found) {
    if (tinfo->limit - tinfo->alloc < 6) {
      tinfo->fp = &frame;
      tinfo->nalloc = 6;
      garbage_collect(tinfo);
      tinfo->fp = frame.prev;
      ps = roots[0]; v = roots[1]; k = roots[2];
    }
    value *p = tinfo->alloc;
    tinfo->alloc += 6;
    p[0] = (value)2048LL; /* pair */
    p[1] = k;
    p[2] = v;
    value pair = (value)(p + 1);
    p[3] = (value)2048LL; /* cons */
    p[4] = pair;
    p[5] = ps;
    return (value)(p + 4);
  }
  /* When found: filter out k */
  tinfo->fp = &frame;
  roots[0] = ps;
  roots[3] = (value)1LL; /* reversed kept elements */
  while (is_ptr(roots[0])) {
    if (tinfo->limit - tinfo->alloc < 4) {
      tinfo->nalloc = 4;
      garbage_collect(tinfo);
    }
    value pair = Field(roots[0], 0);
    roots[0] = Field(roots[0], 1);
    if (f_case_known_511259(tinfo, roots[2], Field(pair, 0)) == (value)1LL) {
      value *c = tinfo->alloc;
      tinfo->alloc += 3;
      c[0] = (value)2048LL;
      c[1] = pair;
      c[2] = roots[3];
      roots[3] = (value)(c + 1);
    }
  }
  /* Reverse roots[3] into roots[0] */
  roots[0] = (value)1LL;
  while (is_ptr(roots[3])) {
    if (tinfo->limit - tinfo->alloc < 4) {
      tinfo->nalloc = 4;
      garbage_collect(tinfo);
    }
    value pair = Field(roots[3], 0);
    roots[3] = Field(roots[3], 1);
    value *c = tinfo->alloc;
    tinfo->alloc += 3;
    c[0] = (value)2048LL;
    c[1] = pair;
    c[2] = roots[0];
    roots[0] = (value)(c + 1);
  }
  if (tinfo->limit - tinfo->alloc < 6) {
    tinfo->nalloc = 6;
    garbage_collect(tinfo);
  }
  value *p = tinfo->alloc;
  tinfo->alloc += 6;
  p[0] = (value)2048LL;
  p[1] = roots[2];
  p[2] = roots[1];
  value pair = (value)(p + 1);
  p[3] = (value)2048LL;
  p[4] = pair;
  p[5] = roots[0];
  tinfo->fp = frame.prev;
  return (value)(p + 4);
}

/* ZMap.Raw.find: f_case_known_509826(tinfo, m, env, x) */
value f_case_known_509826(struct thread_info *tinfo, value m, value env, value x) {
  (void)env;
  int64_t xv = z_to_i64(x);
  while (is_ptr(m)) {
    value k = Field(m, 1);
    if (k == x) {
      m = Field(m, 2);
      goto found;
    }
    int64_t kv = z_to_i64(k);
    if (xv < kv) m = Field(m, 0);
    else if (xv > kv) m = Field(m, 3);
    else { m = Field(m, 2); goto found; }
  }
  return (value)1LL;
found:
  if (tinfo->limit - tinfo->alloc < 4) {
    value roots[1] = { m };
    struct stack_frame frame = { .next = roots + 1, .root = roots, .prev = tinfo->fp };
    tinfo->fp = &frame;
    tinfo->nalloc = 4;
    garbage_collect(tinfo);
    tinfo->fp = frame.prev;
    m = roots[0];
  }
  return alloc_make_Corelib_Init_Datatypes_option_Some(tinfo, m);
}

/* ZMap.Raw.create & bal & add */
static inline int64_t zmap_h(value t) {
  return is_ptr(t) ? z_to_i64(Field(t, 4)) : 0;
}

static value zmap_create(struct thread_info *tinfo, value l, value x, value e, value r) {
  int64_t hl = zmap_h(l), hr = zmap_h(r);
  int64_t h = (hl > hr ? hl : hr) + 1;
  ensure_pos_table();
  value hv = (value)(&z_pos_small_blocks[h][1]);
  if (tinfo->limit - tinfo->alloc < 6) {
    value roots[4] = { l, x, e, r };
    struct stack_frame frame = { .next = roots + 4, .root = roots, .prev = tinfo->fp };
    tinfo->fp = &frame;
    tinfo->nalloc = 6;
    garbage_collect(tinfo);
    tinfo->fp = frame.prev;
    l = roots[0]; x = roots[1]; e = roots[2]; r = roots[3];
  }
  value *n = tinfo->alloc;
  tinfo->alloc += 6;
  n[0] = (value)5120LL;
  n[1] = l;
  n[2] = x;
  n[3] = e;
  n[4] = r;
  n[5] = hv;
  return (value)(n + 1);
}

static value zmap_bal(struct thread_info *tinfo, value l, value x, value d, value r) {
  int64_t hl = zmap_h(l), hr = zmap_h(r);
  if (hl > hr + 2) {
    if (!is_ptr(l)) return zmap_create(tinfo, l, x, d, r);
    value ll = Field(l, 0), lx = Field(l, 1), ld = Field(l, 2), lr = Field(l, 3);
    if (zmap_h(ll) >= zmap_h(lr)) {
      value roots[3] = { ll, lx, ld };
      struct stack_frame frame = { .next = roots + 3, .root = roots, .prev = tinfo->fp };
      tinfo->fp = &frame;
      value nr = zmap_create(tinfo, lr, x, d, r);
      tinfo->fp = frame.prev;
      return zmap_create(tinfo, roots[0], roots[1], roots[2], nr);
    } else {
      if (!is_ptr(lr)) return zmap_create(tinfo, l, x, d, r);
      value lrl = Field(lr, 0), lrx = Field(lr, 1), lrd = Field(lr, 2), lrr = Field(lr, 3);
      value roots[7] = { lrx, lrd, lrr, x, d, r, (value)1LL };
      struct stack_frame frame = { .next = roots + 7, .root = roots, .prev = tinfo->fp };
      tinfo->fp = &frame;
      roots[6] = zmap_create(tinfo, ll, lx, ld, lrl);
      value nr = zmap_create(tinfo, roots[2], roots[3], roots[4], roots[5]);
      tinfo->fp = frame.prev;
      return zmap_create(tinfo, roots[6], roots[0], roots[1], nr);
    }
  }
  if (hr > hl + 2) {
    if (!is_ptr(r)) return zmap_create(tinfo, l, x, d, r);
    value rl = Field(r, 0), rx = Field(r, 1), rd = Field(r, 2), rr = Field(r, 3);
    if (zmap_h(rr) >= zmap_h(rl)) {
      value roots[3] = { rx, rd, rr };
      struct stack_frame frame = { .next = roots + 3, .root = roots, .prev = tinfo->fp };
      tinfo->fp = &frame;
      value nl = zmap_create(tinfo, l, x, d, rl);
      tinfo->fp = frame.prev;
      return zmap_create(tinfo, nl, roots[0], roots[1], roots[2]);
    } else {
      if (!is_ptr(rl)) return zmap_create(tinfo, l, x, d, r);
      value rll = Field(rl, 0), rlx = Field(rl, 1), rld = Field(rl, 2), rlr = Field(rl, 3);
      value roots[7] = { rlx, rld, rlr, rx, rd, rr, (value)1LL };
      struct stack_frame frame = { .next = roots + 7, .root = roots, .prev = tinfo->fp };
      tinfo->fp = &frame;
      roots[6] = zmap_create(tinfo, l, x, d, rll);
      value nr = zmap_create(tinfo, roots[2], roots[3], roots[4], roots[5]);
      tinfo->fp = frame.prev;
      return zmap_create(tinfo, roots[6], roots[0], roots[1], nr);
    }
  }
  return zmap_create(tinfo, l, x, d, r);
}

value NanofildMapsdZMapdRawdcreate_uncurried_uncurried_uncurried_uncurried_17435(
    struct thread_info *tinfo, value env, value r, value e, value x, value l) {
  (void)env;
  return zmap_create(tinfo, l, x, e, r);
}

value NanofildMapsdZMapdRawdbal_uncurried_uncurried_uncurried_uncurried_17530(
    struct thread_info *tinfo, value env, value r, value d, value x, value l) {
  (void)env;
  return zmap_bal(tinfo, l, x, d, r);
}

static value zmap_add(struct thread_info *tinfo, int64_t xv, value x, value d, value m) {
  if (!is_ptr(m)) {
    return zmap_create(tinfo, (value)1LL, x, d, (value)1LL);
  }
  value l = Field(m, 0), y = Field(m, 1), dp = Field(m, 2), r = Field(m, 3);
  int64_t yv = (x == y) ? xv : z_to_i64(y);
  if (xv == yv) {
    value h = Field(m, 4);
    if (tinfo->limit - tinfo->alloc < 6) {
      value roots[5] = { l, x, d, r, h };
      struct stack_frame frame = { .next = roots + 5, .root = roots, .prev = tinfo->fp };
      tinfo->fp = &frame;
      tinfo->nalloc = 6;
      garbage_collect(tinfo);
      tinfo->fp = frame.prev;
      l = roots[0]; x = roots[1]; d = roots[2]; r = roots[3]; h = roots[4];
    }
    value *n = tinfo->alloc;
    tinfo->alloc += 6;
    n[0] = (value)5120LL;
    n[1] = l; n[2] = x; n[3] = d; n[4] = r; n[5] = h;
    return (value)(n + 1);
  } else if (xv < yv) {
    value roots[3] = { y, dp, r };
    struct stack_frame frame = { .next = roots + 3, .root = roots, .prev = tinfo->fp };
    tinfo->fp = &frame;
    value nl = zmap_add(tinfo, xv, x, d, l);
    tinfo->fp = frame.prev;
    return zmap_bal(tinfo, nl, roots[0], roots[1], roots[2]);
  } else {
    value roots[3] = { l, y, dp };
    struct stack_frame frame = { .next = roots + 3, .root = roots, .prev = tinfo->fp };
    tinfo->fp = &frame;
    value nr = zmap_add(tinfo, xv, x, d, r);
    tinfo->fp = frame.prev;
    return zmap_bal(tinfo, roots[0], roots[1], roots[2], nr);
  }
}

value f_case_known_510779(struct thread_info *tinfo, value m, value env, value z1, value bal_clo, value d) {
  (void)env; (void)z1; (void)bal_clo;
  value x = tinfo->args[5];
  return zmap_add(tinfo, z_to_i64(x), x, d, m);
}

value BackenddIrTextdis_layout_503(struct thread_info *tinfo, value env, value n) {
  (void)tinfo; (void)env;
  uint64_t c = nat_to_u64(n);
  return (c == 32 || c == 10 || c == 9 || c == 13) ? (value)3LL : (value)1LL;
}

value BackenddIrTextdbetween_uncurried_uncurried_known_502835(struct thread_info *tinfo, value n, value hi, value lo) {
  (void)tinfo;
  uint64_t nv = nat_to_u64(n), lov = nat_to_u64(lo), hiv = nat_to_u64(hi);
  return (lov <= nv && nv <= hiv) ? (value)3LL : (value)1LL;
}

value NanofildTermdlookup_uncurried_uncurried_known_511686(struct thread_info *tinfo, value ps, value k) {
  return f_case_known_511786(tinfo, ps, k);
}

extern value y_known_504084(struct thread_info *, value, value, value, value, value);
extern value BackenddIrTextdis_end_of_file_known_506976(struct thread_info *, value);

/* Static MTerm(false) block: header 1024LL (1 word, tag 0), field 0 = 1LL (false) */
static value mterm_false_block[2] = { (value)1024LL, (value)1LL };
#define MTERM_FALSE ((value)(&mterm_false_block[1]))

value piece_clauses_uncurried_uncurried_uncurried_uncurried_uncurried_known_507608(
    struct thread_info *tinfo, value acc, value m, value st, value cs, value start) {
  value roots[7] = {
    acc, m, st, cs, start,
    tinfo->args[5], /* fuel */
    tinfo->args[6]  /* read_step_clo */
  };
  struct stack_frame frame = { .next = roots + 7, .root = roots, .prev = tinfo->fp };
  tinfo->fp = &frame;

  for (;;) {
    if (!is_ptr(roots[5])) {
      /* fuel == O -> PieceMore acc start */
      break;
    }
    roots[5] = Field(roots[5], 0); /* fuel' */
    value step = y_known_504084(tinfo, roots[1], roots[6], roots[5], roots[3], roots[2]);
    if (!is_ptr(step)) {
      /* Fail or Done -> PieceMore acc start */
      break;
    }
    int tag = (int)(((intnat)Field(step, -1)) & 255);
    if (tag == 1) {
      /* Next cs' st' m' */
      roots[3] = Field(step, 0);
      roots[2] = Field(step, 1);
      roots[1] = Field(step, 2);
      continue;
    }
    /* tag == 0: Clause t rest */
    value t = Field(step, 0);
    value rest = Field(step, 1);
    if (!is_ptr(rest)) {
      /* rest == [] -> PieceMore acc start */
      break;
    }
    roots[3] = rest; /* save rest in roots[3] */
    roots[2] = t;    /* save t in roots[2] */
    value eof = BackenddIrTextdis_end_of_file_known_506976(tinfo, t);
    if (eof == (value)3LL) {
      /* PieceStop acc (tag 0, 1 field) */
      if (tinfo->limit - tinfo->alloc < 4) {
        tinfo->nalloc = 4;
        garbage_collect(tinfo);
      }
      value *p = tinfo->alloc;
      tinfo->alloc += 2;
      p[0] = (value)1024LL;
      p[1] = roots[0];
      tinfo->fp = frame.prev;
      return (value)(p + 1);
    }
    if (tinfo->limit - tinfo->alloc < 4) {
      tinfo->nalloc = 4;
      garbage_collect(tinfo);
    }
    value *c = tinfo->alloc;
    tinfo->alloc += 3;
    c[0] = (value)2048LL;
    c[1] = roots[2]; /* t */
    c[2] = roots[0]; /* acc */
    roots[0] = (value)(c + 1);
    roots[4] = roots[3]; /* start = rest */
    roots[2] = (value)1LL; /* st = [] */
    roots[1] = MTERM_FALSE; /* m = MTerm false */
  }

  /* PieceMore acc start (tag 1, 2 fields -> header 2049LL) */
  if (tinfo->limit - tinfo->alloc < 4) {
    tinfo->nalloc = 4;
    garbage_collect(tinfo);
  }
  value *p = tinfo->alloc;
  tinfo->alloc += 3;
  p[0] = (value)2049LL;
  p[1] = roots[0];
  p[2] = roots[4];
  tinfo->fp = frame.prev;
  return (value)(p + 1);
}

value clauses_uncurried_uncurried_uncurried_uncurried_known_507228(
    struct thread_info *tinfo, value acc, value m, value st, value cs, value fuel) {
  value roots[6] = {
    acc, m, st, cs, fuel,
    tinfo->args[5] /* read_step_clo */
  };
  struct stack_frame frame = { .next = roots + 6, .root = roots, .prev = tinfo->fp };
  tinfo->fp = &frame;

  for (;;) {
    if (!is_ptr(roots[4])) {
      tinfo->fp = frame.prev;
      return (value)1LL; /* None */
    }
    roots[4] = Field(roots[4], 0); /* fuel' */
    value step = y_known_504084(tinfo, roots[1], roots[5], roots[4], roots[3], roots[2]);
    if (!is_ptr(step)) {
      if ((((intnat)step) >> 1) == 0) {
        /* Fail -> None */
        tinfo->fp = frame.prev;
        return (value)1LL;
      }
      /* Done -> Some acc */
      break;
    }
    int tag = (int)(((intnat)Field(step, -1)) & 255);
    if (tag == 1) {
      /* Next cs' st' m' */
      roots[3] = Field(step, 0);
      roots[2] = Field(step, 1);
      roots[1] = Field(step, 2);
      continue;
    }
    /* Clause t rest */
    value t = Field(step, 0);
    value rest = Field(step, 1);
    roots[3] = rest;
    roots[2] = t;
    value eof = BackenddIrTextdis_end_of_file_known_506976(tinfo, t);
    if (eof == (value)3LL) {
      /* Some acc */
      break;
    }
    if (tinfo->limit - tinfo->alloc < 4) {
      tinfo->nalloc = 4;
      garbage_collect(tinfo);
    }
    value *c = tinfo->alloc;
    tinfo->alloc += 3;
    c[0] = (value)2048LL;
    c[1] = roots[2];
    c[2] = roots[0];
    roots[0] = (value)(c + 1);
    roots[2] = (value)1LL;
    roots[1] = MTERM_FALSE;
  }

  if (tinfo->limit - tinfo->alloc < 4) {
    tinfo->nalloc = 4;
    garbage_collect(tinfo);
  }
  value *p = tinfo->alloc;
  tinfo->alloc += 2;
  p[0] = (value)1024LL;
  p[1] = roots[0];
  tinfo->fp = frame.prev;
  return (value)(p + 1);
}
