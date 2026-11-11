#!/usr/bin/env bash
# Linker contracts, through its command-line interface, with a native
# filcc probe for weak alias getters (which differ from ELF aliases).
set -euo pipefail
: "${FILCC:?set FILCC to a filcc clang}"
nf=$(cd "$(dirname "$0")/../../.." && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
link() { swipl "$nf/rocq/scripts/link.pl" "$@"; }
check() { swipl -q -g "read_file_to_terms('$work/out', [module(Is)], []), ($1), halt" -t 'halt(1)'; }

cat >"$work/main" <<'EOF'
module([func(main,export,w,[],[block(s,[],[call(result(tmp(x),w),global(a),[])],ret(tmp(x)))])]).
EOF
cat >"$work/a" <<'EOF'
module([alias(a,export,impl),func(impl,local,w,[],[block(s,[],[call(result(tmp(x),w),global(b),[])],ret(tmp(x)))])]).
EOF
cat >"$work/b" <<'EOF'
module([func(b,export,w,[],[block(s,[],[],ret(const(37)))])]).
EOF
cat >"$work/unused" <<'EOF'
module([func(main,export,w,[],[block(s,[],[],ret(const(99)))]),data(init,init(ctor,none),8,[item(p,sym(main,0))])]).
EOF
cat >"$work/decl" <<'EOF'
module([data(a,extern(weak),8,[])]).
EOF
# Reverse dependency order forces repeated extraction. The unused member
# would conflict with main and refuse its ctor if eagerly included; a weak
# declaration must not satisfy demand for a definition.
link main "main=$work/main" --archive "decl=$work/decl" --archive "b=$work/b" \
  --archive "a=$work/a" --archive "unused=$work/unused" >"$work/out"
check "length(Is,4), member(alias(a,export,'a#impl'),Is), member(func(b,export,_,_,_),Is)"

cat >"$work/weak" <<'EOF'
module([func(f,weak,w,[],[block(s,[],[],ret(const(11)))]),alias(g,export,f),data(d,weak,8,[item(l,const(13))]),data(r,ro(weak),8,[item(l,const(17))])]).
EOF
cat >"$work/strong" <<'EOF'
module([func(main,export,w,[],[block(s,[],[call(result(tmp(x),w),global(f),[]),call(result(tmp(y),w),global(g),[]),let(tmp(d),p,copy,[global(d)]),let(tmp(r),p,copy,[global(r)]),let(tmp(h),w,mul,[tmp(x),const(100)]),let(tmp(z),w,add,[tmp(h),tmp(y)])],ret(tmp(z)))]),func(f,export,w,[],[block(s,[],[],ret(const(23)))]),data(d,export,8,[item(l,const(29))]),data(r,ro(export),8,[item(l,const(31))])]).
EOF
link main "weak=$work/weak" "strong=$work/strong" >"$work/out"
check "member(func(f,export,w,[],[block(s,[],[],ret(const(23)))]),Is), member(alias(g,export,f),Is), member(data(d,export,8,[item(l,const(29))]),Is), member(data(r,ro(export),8,[item(l,const(31))]),Is), length(Is,5)"
"$nf/bin/nanofil" --goal "use_module('$nf/src/interp'), read_file_to_terms('$work/out', [M], []), run(M, main, [], 100, ret(2323))" </dev/null
# filcc's g getter jumps to the preemptible f getter: both call B's f,
# rather than g keeping A's body as it would with an ordinary ELF alias.
cat >"$work/weak.c" <<'EOF'
__attribute__((weak)) int f(void) { return 11; }
extern int g(void) __attribute__((alias("f")));
EOF
cat >"$work/strong.c" <<'EOF'
#include <stdio.h>
int f(void) { return 23; }
int g(void);
int main(void) { printf("%d %d\n", f(), g()); return 0; }
EOF
"$FILCC" -O1 "$work/weak.c" "$work/strong.c" -o "$work/native"
test "$("$work/native")" = '23 23'

cat >"$work/ctors" <<'EOF'
module([func(main,export,w,[],[block(s,[],[],ret(const(0)))]),func(startup,local,void,[],[block(s,[],[call(void,global(b),[])],ret)]),func(cleanup,local,void,[],[block(s,[],[],ret)]),data(ci,init(ctor,none),8,[item(p,sym(startup,0))]),data(di,init(dtor,7),8,[item(p,sym(cleanup,0))])]).
EOF
if link main "c=$work/ctors" >"$work/out" 2>"$work/err"; then
  echo 'link-demand: ctor unexpectedly accepted without --ctors' >&2; exit 1
fi
grep -q 'which the linked module does not run' "$work/err"
link --ctors main "c=$work/ctors" --archive "b=$work/b" >"$work/out"
check "length(Is,6), member(data(ci,init(ctor,none),8,[item(p,sym('c#startup',0))]),Is), member(data(di,init(dtor,7),8,[item(p,sym('c#cleanup',0))]),Is), member(func('c#startup',local,_,_,_),Is), member(func('c#cleanup',local,_,_,_),Is), member(func(b,export,_,_,_),Is)"
echo 'link-demand: archive fixed point, weak aliases/data, ctor refusal and roots ok'
