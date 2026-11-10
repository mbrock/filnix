// The stdlib's integers and strings for the Crane extraction of the
// nanofil backend: the type and the functions CraneMap.v names.
#pragma once
#include <concepts>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <gmpxx.h>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

namespace nf {
// A positive, an N or a Z. A number that fits 64 signed bits is held in
// the word; any other is a GMP integer on the heap, and is never one
// that would fit. The compiler's numbers are nearly all small, and a
// copy of a small one allocates nothing.
//
// Under [Set Crane GC] the GMP integer is in a collected block that is
// never written again, so a Z is two words that copy as two words, and
// the collector frees the integer.
class Z {
  int64_t s_ = 0;
#ifdef CRANE_GC
  const mpz_class *b_ = nullptr;
#else
  mpz_class *b_ = nullptr;
#endif

  static Z of_mpz(mpz_class &&m) {
    if (m.fits_slong_p()) return Z(static_cast<int64_t>(m.get_si()));
    Z r;
    r.b_ = new mpz_class(std::move(m));
    return r;
  }
  mpz_class wide() const { return b_ ? *b_ : mpz_class(static_cast<long>(s_)); }
  bool is_small() const { return b_ == nullptr; }

public:
  Z() = default;
  template <std::integral T> Z(T v) {
    if constexpr (std::is_signed_v<T>) {
      s_ = static_cast<int64_t>(v);
    } else {
      uint64_t u = static_cast<uint64_t>(v);
      if (u <= static_cast<uint64_t>(INT64_MAX)) s_ = static_cast<int64_t>(u);
      else b_ = new mpz_class(static_cast<unsigned long>(u));
    }
  }
  static Z decimal(const char *digits) { return of_mpz(mpz_class(digits)); }
#ifndef CRANE_GC
  Z(const Z &o) : s_(o.s_), b_(o.b_ ? new mpz_class(*o.b_) : nullptr) {}
  Z(Z &&o) noexcept : s_(o.s_), b_(o.b_) { o.b_ = nullptr; }
  Z &operator=(const Z &o) {
    if (this != &o) {
      mpz_class *n = o.b_ ? new mpz_class(*o.b_) : nullptr;
      delete b_;
      b_ = n;
      s_ = o.s_;
    }
    return *this;
  }
  Z &operator=(Z &&o) noexcept {
    if (this != &o) {
      delete b_;
      b_ = o.b_;
      s_ = o.s_;
      o.b_ = nullptr;
    }
    return *this;
  }
  ~Z() { delete b_; }
#endif

  friend Z operator+(const Z &a, const Z &b) {
    int64_t r;
    if (a.is_small() && b.is_small() && !__builtin_add_overflow(a.s_, b.s_, &r)) return Z(r);
    return of_mpz(mpz_class(a.wide() + b.wide()));
  }
  friend Z operator-(const Z &a, const Z &b) {
    int64_t r;
    if (a.is_small() && b.is_small() && !__builtin_sub_overflow(a.s_, b.s_, &r)) return Z(r);
    return of_mpz(mpz_class(a.wide() - b.wide()));
  }
  friend Z operator*(const Z &a, const Z &b) {
    int64_t r;
    if (a.is_small() && b.is_small() && !__builtin_mul_overflow(a.s_, b.s_, &r)) return Z(r);
    return of_mpz(mpz_class(a.wide() * b.wide()));
  }
  friend Z operator-(const Z &a) {
    if (a.is_small() && a.s_ != INT64_MIN) return Z(-a.s_);
    return of_mpz(mpz_class(-a.wide()));
  }
  friend Z abs(const Z &a) { return sign(a) < 0 ? -a : a; }
  // Bits as of the two's complement of unbounded width, as Z.land has them.
  friend Z operator&(const Z &a, const Z &b) {
    if (a.is_small() && b.is_small()) return Z(a.s_ & b.s_);
    return of_mpz(mpz_class(a.wide() & b.wide()));
  }
  friend Z operator|(const Z &a, const Z &b) {
    if (a.is_small() && b.is_small()) return Z(a.s_ | b.s_);
    return of_mpz(mpz_class(a.wide() | b.wide()));
  }
  // A shift to the right rounds down.
  friend Z operator>>(const Z &a, unsigned long n) {
    if (a.is_small()) return Z(n >= 64 ? (a.s_ < 0 ? int64_t{-1} : int64_t{0}) : a.s_ >> n);
    mpz_class r;
    mpz_fdiv_q_2exp(r.get_mpz_t(), a.b_->get_mpz_t(), n);
    return of_mpz(std::move(r));
  }
  friend Z shl(const Z &a, unsigned long n) {
    int64_t r;
    if (a.is_small() && n < 63 && !__builtin_mul_overflow(a.s_, int64_t{1} << n, &r)) return Z(r);
    mpz_class w = a.wide(), q;
    mpz_mul_2exp(q.get_mpz_t(), w.get_mpz_t(), n);
    return of_mpz(std::move(q));
  }
  friend int sign(const Z &a) { return a.is_small() ? (a.s_ > 0) - (a.s_ < 0) : sgn(*a.b_); }
  // A wide number is outside int64_t, so its sign orders it against a
  // small one.
  friend int cmp(const Z &a, const Z &b) {
    if (a.is_small() && b.is_small()) return (a.s_ > b.s_) - (a.s_ < b.s_);
    if (a.is_small()) return -sgn(*b.b_);
    if (b.is_small()) return sgn(*a.b_);
    return ::cmp(*a.b_, *b.b_);
  }
  friend bool operator==(const Z &a, const Z &b) {
    if (a.is_small() && b.is_small()) return a.s_ == b.s_;
    return cmp(a, b) == 0;
  }
  friend bool operator!=(const Z &a, const Z &b) { return !(a == b); }
  friend bool operator<(const Z &a, const Z &b) { return cmp(a, b) < 0; }
  friend bool operator<=(const Z &a, const Z &b) { return cmp(a, b) <= 0; }
  friend bool operator>(const Z &a, const Z &b) { return cmp(a, b) > 0; }
  friend bool operator>=(const Z &a, const Z &b) { return cmp(a, b) >= 0; }

  friend bool z_odd(const Z &a) { return a.is_small() ? (a.s_ & 1) != 0 : mpz_odd_p(a.b_->get_mpz_t()) != 0; }
  // Z.div and Z.modulo round down, and a division by 0 gives 0 and the
  // dividend.
  friend Z z_div(const Z &a, const Z &b) {
    if (a.is_small() && b.is_small() && b.s_ != -1) {
      if (b.s_ == 0) return Z(0);
      int64_t q = a.s_ / b.s_, r = a.s_ % b.s_;
      if (r != 0 && ((r < 0) != (b.s_ < 0))) --q;
      return Z(q);
    }
    if (sign(b) == 0) return Z(0);
    mpz_class x = a.wide(), y = b.wide(), q;
    mpz_fdiv_q(q.get_mpz_t(), x.get_mpz_t(), y.get_mpz_t());
    return of_mpz(std::move(q));
  }
  friend Z z_mod(const Z &a, const Z &b) {
    if (a.is_small() && b.is_small() && b.s_ != -1) {
      if (b.s_ == 0) return a;
      int64_t r = a.s_ % b.s_;
      if (r != 0 && ((r < 0) != (b.s_ < 0))) r += b.s_;
      return Z(r);
    }
    if (sign(b) == 0) return a;
    mpz_class x = a.wide(), y = b.wide(), r;
    mpz_fdiv_r(r.get_mpz_t(), x.get_mpz_t(), y.get_mpz_t());
    return of_mpz(std::move(r));
  }
  // Z.quot rounds toward 0.
  friend Z z_quot(const Z &a, const Z &b) {
    if (a.is_small() && b.is_small() && b.s_ != -1) return Z(b.s_ == 0 ? int64_t{0} : a.s_ / b.s_);
    if (sign(b) == 0) return Z(0);
    mpz_class x = a.wide(), y = b.wide(), q;
    mpz_tdiv_q(q.get_mpz_t(), x.get_mpz_t(), y.get_mpz_t());
    return of_mpz(std::move(q));
  }
  friend unsigned long small(const Z &a) {
    if (!a.is_small() || a.s_ < 0) {
      if (!a.is_small() && a.b_->fits_ulong_p()) return a.b_->get_ui();
      std::fputs("nanofil-backend: a count past 64 bits\n", stderr);
      std::abort();
    }
    return static_cast<unsigned long>(a.s_);
  }
  // Z.pow: 0 for a negative exponent.
  friend Z z_pow(const Z &a, const Z &b) {
    if (sign(b) < 0) return Z(0);
    mpz_class x = a.wide(), r;
    mpz_pow_ui(r.get_mpz_t(), x.get_mpz_t(), small(b));
    return of_mpz(std::move(r));
  }
  // Z.log2: 0 for a number that is not positive.
  friend Z z_log2(const Z &a) {
    if (sign(a) <= 0) return Z(0);
    if (a.is_small()) return Z(63 - __builtin_clzll(static_cast<unsigned long long>(a.s_)));
    return Z(static_cast<unsigned long>(mpz_sizeinbase(a.b_->get_mpz_t(), 2) - 1));
  }
  // The number modulo m, rounding down.
  friend unsigned long z_residue(const Z &a, unsigned long m) {
    if (a.is_small()) {
      int64_t r = a.s_ % static_cast<int64_t>(m);
      return static_cast<unsigned long>(r < 0 ? r + static_cast<int64_t>(m) : r);
    }
    return mpz_fdiv_ui(a.b_->get_mpz_t(), m);
  }
};

// The class's friends, named for a call that spells out nf::.
Z abs(const Z &a);
Z shl(const Z &a, unsigned long n);
int sign(const Z &a);
int cmp(const Z &a, const Z &b);
bool z_odd(const Z &a);
Z z_div(const Z &a, const Z &b);
Z z_mod(const Z &a, const Z &b);
Z z_quot(const Z &a, const Z &b);
unsigned long small(const Z &a);
Z z_pow(const Z &a, const Z &b);
Z z_log2(const Z &a);
unsigned long z_residue(const Z &a, unsigned long m);

// Z.shiftl: a shift by a negative count is to the right, rounding down.
inline Z z_shiftl(const Z &a, const Z &n) {
  if (sign(n) >= 0) return shl(a, small(n));
  return a >> small(-n);
}
// A comparison's sign as the extracted `comparison`, which is declared
// after this header.
template <class C> inline C order(int c) { return c < 0 ? C::LT : c == 0 ? C::EQ : C::GT; }
// Maps.string_hash: each character's code folded into h by
// (h * 31 + code) mod 2^20.
inline Z string_hash(const std::string &s, const Z &h) {
  if (s.empty()) return h;
  unsigned long x = z_residue(h, 1ul << 20);
  for (unsigned char c : s) x = (x * 31 + c) & 0xFFFFF;
  return Z(x);
}
// string_of_list_ascii, for the extracted list of characters.
template <class L> inline std::string string_of_list(const L &cs) {
  std::string s;
  for (const L *p = &cs;;) {
    auto *cell = get_if<typename L::Cons>(&p->v());
    if (!cell) return s;
    s.push_back(cell->a);
    p = cell->l.get();
  }
}
inline Z z_min(const Z &a, const Z &b) { return a <= b ? a : b; }
inline Z z_max(const Z &a, const Z &b) { return a >= b ? a : b; }
inline Z z_of_nat(uint64_t n) { return Z(n); }
inline uint64_t z_to_nat(const Z &a) {
  if (sign(a) <= 0) return 0;
  return small(a);
}
constexpr long small_literal(const char *s) {
  long v = 0;
  for (; *s; ++s) v = v * 10 + (*s - '0');
  return v;
}
} // namespace nf

// A decimal literal: a machine integer when it has at most 18 digits,
// else parsed once.
template <char... Cs> inline nf::Z operator""_nfz() {
  static constexpr char s[] = {Cs..., 0};
  if constexpr (sizeof...(Cs) <= 18) {
    constexpr long v = nf::small_literal(s);
    return nf::Z(v);
  } else {
    static const nf::Z big = nf::Z::decimal(s);
    return big;
  }
}
