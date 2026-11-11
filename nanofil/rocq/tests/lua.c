/* Lua's own functions for the Rocq model's outcome gate (rocq/scripts/lua.sh,
   docs/rocq.md). Lua 5.4.7's lctype.c, lobject.c and lstring.c are
   included as one translation unit, as Lua's onelua.c does, and each
   entry below calls a function of theirs that needs no lua_State and
   no libc on the path it takes: integer and float arithmetic
   (luaO_rawarith), integer numerals (luaO_str2num), the string hash
   (luaS_hash), UTF-8 escapes (luaO_utf8esc) and luaO_ceillog2. Lua's
   other functions call libc or need a running state, which the
   interpreter does not model; Lua's test suite runs them natively
   (nix/lua.nix). */

// run: $arith_int 0 7 -3
// run: $arith_int 1 7 -3
// run: $arith_int 2 -9223372036854775807 3
// run: $arith_int 7 12 10
// run: $arith_int 8 12 10
// run: $arith_int 9 12 10
// run: $arith_int 12 5 0
// run: $arith_int 13 5 0
// run: $arith_int 5 1 3
// run: $arith_float 0 1 3
// run: $arith_float 2 -7 3
// run: $arith_float 5 1 3
// run: $arith_float 5 1 0
// run: $arith_float 12 2 0
// run: $arith_mixed 0 1 3
// run: $arith_mixed 5 10 4
// run: $str2int 0
// run: $str2int 1
// run: $str2int 2
// run: $str2int 3
// run: $hash 0 0
// run: $hash 1 2654435769
// run: $utf8 65
// run: $utf8 233
// run: $utf8 8364
// run: $utf8 128512
// run: $ceillog2 1000

#define LUA_CORE
#include "lctype.c"
#include "lobject.c"
#include "lstring.c"

/* The bits of a Lua number: a float result is returned as its IEEE
   pattern, so the comparison sees every bit. */
static long long result_bits(const TValue *r) {
    union { lua_Number n; long long i; } u;
    if (ttisinteger(r)) return ivalue(r);
    u.n = fltvalue(r);
    return u.i;
}

/* op is Lua's LUA_OP* number; -1 when luaO_rawarith refuses. */
long long arith_int(int op, long long a, long long b) {
    TValue x, y, r;
    setivalue(&x, a);
    setivalue(&y, b);
    if (!luaO_rawarith(NULL, op, &x, &y, &r)) return -1;
    return result_bits(&r);
}

long long arith_float(int op, long long a, long long b) {
    TValue x, y, r;
    setfltvalue(&x, (lua_Number)a);
    setfltvalue(&y, (lua_Number)b);
    if (!luaO_rawarith(NULL, op, &x, &y, &r)) return -1;
    return result_bits(&r);
}

/* An integer and a float operand: Lua converts the integer. */
long long arith_mixed(int op, long long a, long long b) {
    TValue x, y, r;
    setivalue(&x, a);
    setfltvalue(&y, (lua_Number)b);
    if (!luaO_rawarith(NULL, op, &x, &y, &r)) return -1;
    return result_bits(&r);
}

static const char *const numerals[] = {
    "12345", "  -0x10  ", "0x7fffffffffffffff", "-9223372036854775808",
};

/* The numeral's value, or -1 when it is not an integer numeral. */
long long str2int(int which) {
    TValue o;
    if (luaO_str2num(numerals[which], &o) == 0 || !ttisinteger(&o)) return -1;
    return ivalue(&o);
}

static const char *const strings[] = { "", "the quick brown fox" };

unsigned hash(int which, unsigned seed) {
    const char *s = strings[which];
    size_t l = 0;
    while (s[l] != '\0') l++;
    return luaS_hash(s, l, seed);
}

/* The escape's length, then its bytes, first byte lowest. */
long long utf8(unsigned long x) {
    char buff[UTF8BUFFSZ];
    int n = luaO_utf8esc(buff, x);
    long long r = 0;
    for (int i = UTF8BUFFSZ - 1; i >= UTF8BUFFSZ - n; i--)
        r = r * 256 + (unsigned char)buff[i];
    return r * 8 + n;
}

int ceillog2(unsigned x) { return luaO_ceillog2(x); }
