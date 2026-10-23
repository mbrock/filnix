#!/usr/bin/env bash
# Compare actual c_lex terms, not whitespace or pretty-printed C. In
# particular radix/suffix, GNU keyword folding and string bytes must agree.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
src="$here/../src"
tpl=${TPL:-tpl}
filcc=${FILCC:?set FILCC to a filcc clang}
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
n=0
compare() {
  local f=$1
  "$filcc" -E -o "$work/ref.i" "$f"
  (cd "$src" && "$tpl" -q main.pl -- tokens "$work/ref.i" </dev/null) >"$work/ref.tokens"
  (cd "$src" && "$tpl" -q main.pl -- tokens "$f" </dev/null) >"$work/our.tokens"
  if ! diff -u "$work/ref.tokens" "$work/our.tokens" >"$work/diff"; then
    echo "PREPROCESSOR MISMATCH $f" >&2
    head -100 "$work/diff" >&2
    exit 1
  fi
  n=$((n + 1))
}
if (($#)); then
  for f in "$@"; do compare "$(realpath "$f")"; done
else
  for h in stdio stdlib string stdint ctype limits errno unistd signal math pthread time \
           sys/stat dirent wchar inttypes fcntl sys/mman getopt setjmp; do
    printf '#include <%s.h>\n' "$h" >"$work/header.c"
    compare "$work/header.c"
    echo "pptest: <$h.h> matches"
  done
  while IFS= read -r -d '' f; do compare "$f"; done < <(find "$here/c" -name '*.c' -print0 | sort -z)
  cat >"$work/once.h" <<'EOF'
#pragma once
int included_once;
EOF
  cat >"$work/macros.c" <<'EOF'
#define OBJ 27
#define ADD(a,b) ((a)+(b))
#define STR(x) #x
#define CAT(a,b) a##b
#define EXPAND_CAT(a,b) CAT(a,b)
#define VAR(a,...) a(__VA_ARGS__)
#define ALL(...) __VA_ARGS__
#define NAMED(args...) args
#define SELF SELF
#define ONE TWO
#define TWO ONE
#define CALL ADD
#define EMPTY()
#include "once.h"
#include "once.h"
#define HEADER "once.h"
#include HEADER
#include "./once.h"
#pragma ignored
OBJ ADD(OBJ, ADD(1,2)) VAR(ADD,3,4) CALL(2,3)
ALL() ALL(1,2,(3,4)) NAMED(5,6) STR()
STR(OBJ   + /* comment */ "quoted\\text")
STR(ADD(1,2)) CAT(OB,J) EXPAND_CAT(OB,J)
CAT(,OBJ) CAT(OBJ,) CAT(,) EMPTY() SELF ONE
ADD(
  3,
  4)
#undef OBJ
#ifdef OBJ
#error undef failed
#elif defined(SELF) && !defined missing && (2+3*4==14) && ((8>>2)==2)
int conditional;
#else
#error condition failed
#endif
#if 0
#if 1/0
#error inactive
#endif
#elif (1 || 1/0) && (0 ? 1/0 : 1)
int short_circuit;
#endif
#if __has_include("once.h") && __has_include(<stdio.h>) && !__has_include(<missing_nanofil.h>)
int has_include;
#endif
#if (-1 < 1U) || (~0U >> 63) != 1 || (18446744073709551615ULL + 1) != 0
#error uintmax conversion failed
#endif
#if (9007199254740993LL / 3) != 3002399751580331LL || (-7/3) != -2 || (-7%3) != -1
#error integer division failed
#endif
#if (1 ? -1 : 0U) < 0
#error conditional conversions failed
#endif
#if L'\0' - 1 < 0 && ('a' == 97) && (1 | 2 ^ 3 & 4) == 3
int character_condition;
#endif
#define MULTI(a) a + \
  2
MULTI(1)
__LINE__ __FILE__
#define OBJECT_PASTE 1##2
OBJECT_PASTE
CAT(L,'x') CAT(L,"wide")
STR(ADD())
#define RECUR(x) RECUR(x)
RECUR(RECUR(3))
#define x 3
#define f(a) f(x * (a))
#undef x
#define x 2
#define g f
#define z z[0]
#define h g(~
#define m(a) a(w)
#define w 0,1
#define t(a) a
f(y+1) + f(f(z)) % t(t(g)(0) + t)(1);
g(x + (3,4) - w) | h 5) & m(f) ^ m(m);
EOF
  compare "$work/macros.c"
  cat >"$work/locations.c" <<'EOF'
#define DECL int
// a physical source line
DECL source_line; \
int continued_line;
#include "once.h"
EOF
  compare "$work/locations.c"
  (cd "$src" && PP_LOCATION_FILE="$work/locations.c" PP_HEADER_FILE="$work/once.h" \
    "$tpl" -q -g "use_module(c_pp),use_module(library(lists)),
      getenv('FILCC',C),pp_profile(C,P),getenv('PP_LOCATION_FILE',F),getenv('PP_HEADER_FILE',H),
      (pp_file(F,P,Ts),memberchk(tok(kw(int),F:3),Ts),memberchk(tok(kw(int),F:4),Ts),
       memberchk(tok(kw(int),H:2),Ts) -> halt(0); halt(1))." </dev/null)
  echo 'pptest: original file, macro invocation and spliced-line locations checked'
  cat >"$work/line-pragma.c" <<'EOF'
#define line 1000
#line line "virtual/source.c"
__LINE__ __FILE__
#if __LINE__ != 1001 || !__has_include("once.h")
#error logical line or physical include directory lost
#endif
#include "once.h"
#line \
2000
__LINE__ __FILE__
#define COMMENT /* a comment may span
physical lines without ending a directive */ 7
COMMENT __LINE__
#define push_macro ignored
#define pop_macro ignored
#pragma push_macro("SAVED")
#define SAVED 111
#pragma push_macro("SAVED")
#undef SAVED
#define SAVED 222
SAVED
#pragma pop_macro("SAVED")
SAVED
#pragma pop_macro("SAVED")
#ifdef SAVED
#error an undefined macro was not restored
#endif
#define FN(x) ((x)+3)
#pragma push_macro("FN")
#undef FN
#define FN 5
FN
#pragma pop_macro("FN")
FN(4)
EOF
  compare "$work/line-pragma.c"
  printf '#error intentional\n' >"$work/error.c"
  if (cd "$src" && "$tpl" -q main.pl -- tokens "$work/error.c" </dev/null) >"$work/out" 2>"$work/err"; then
    echo 'pptest: #error was accepted' >&2; exit 1
  fi
  grep -q 'error_directive' "$work/err"
fi
echo "pptest: $n token streams match filcc -E"
