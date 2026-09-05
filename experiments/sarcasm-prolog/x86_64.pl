:- module(sp_x86_64, [emit_c/1]).
:- use_module(library(lists)).

% Compiler-backed first target: Fil-C owns ABI, capabilities, roots and checks.
emit_c(Functions) :-
    format('#include <stdint.h>~n#include <stddef.h>~n#include <limits.h>~n', []),
    format('#if !defined(__FILC__) || !defined(__x86_64__)~n#error "requires x86-64 Fil-C"~n#endif~n', []),
    format('static const unsigned char *sp_address(const unsigned char *p, uint64_t i, uint64_t s, uint64_t d) {~n', []),
    format('  uint64_t o;~n  if (__builtin_mul_overflow(i,s,&o) || __builtin_add_overflow(o,d,&o) || o > PTRDIFF_MAX) __builtin_trap();~n  return p + (ptrdiff_t)o;~n}~n', []),
    maplist(emit_function,Functions).
emit_function(function(Name,Args,Plan)) :-
    format('uint64_t ~w(const unsigned char *arg0', [Name]),
    (Args=[ptr,u64] -> format(', uint64_t arg1',[]); true),
    format(') {~n',[]), emit_plan(Plan,0), format('}~n',[]).
emit_plan([], _).
emit_plan([read(P,I,S,O,W,Loads)|Xs],N) :- !,
    Bits is W*8,
    format('  /* covering read: offset ~d, width ~d */~n  uint~d_t chunk~d;~n  __builtin_memcpy(&chunk~d, ',[O,W,Bits,N,N]),
    address(P,I,S,O), format(', ~d);~n',[W]),
    maplist(extract(N,O),Loads), N1 is N+1, emit_plan(Xs,N1).
emit_plan([store(P,I,S,O,W,V,L)|Xs],N) :- !,
    Bits is W*8, origin(L),
    format('  { uint~d_t stored = (uint~d_t)(',[Bits,Bits]), value(V),
    format(');~n    __builtin_memcpy((void *)',[]), address(P,I,S,O),
    format(', &stored, ~d); }~n',[W]), emit_plan(Xs,N).
emit_plan([assign(V,W,A,L)|Xs],N) :- !,
    origin(L), declaration(V), format('(uint~d_t)(',[W]), value(A), format(');~n',[]), emit_plan(Xs,N).
emit_plan([pointer_copy(V,P,L)|Xs],N) :- !,
    origin(L), pointer_declaration(V), value(P), format(';~n',[]), emit_plan(Xs,N).
emit_plan([pointer_offset(V,P,I,S,O,L)|Xs],N) :- !,
    origin(L), pointer_declaration(V), address(P,I,S,O), format(';~n',[]), emit_plan(Xs,N).
emit_plan([binary(V,K,W,A,B,L)|Xs],N) :- !,
    origin(L), declaration(V), format('(uint~d_t)(',[W]), value(A), operator(K),
    (memberchk(K,[shl,shr]) -> format('(',[]), value(B), Mask is W-1, format(' & ~d)',[Mask]); value(B)),
    format(');~n',[]), emit_plan(Xs,N).
emit_plan([return(V)|Xs],N) :- format('  return ',[]), value(V), format(';~n',[]), emit_plan(Xs,N).
extract(N,O,load(V,_,_,_,D,W,L)) :-
    Shift is (D-O)*8, Bits is W*8,
    origin(L), declaration(V), format('(uint~d_t)(chunk~d >> ~d);~n',[Bits,N,Shift]).
origin(L) :- format('  /* source line ~d */~n',[L]).
declaration(v(N)) :- format('  uint64_t v~d = ',[N]).
pointer_declaration(v(N)) :- format('  const unsigned char *v~d = ',[N]).
address(P,I,S,O) :-
    format('sp_address(',[]), value(P), format(', ',[]), value(I),
    format(', UINT64_C(~d), UINT64_C(~d))',[S,O]).
value(view(V,W)) :- format('((uint~d_t)',[W]), value(V), format(')',[]).
value(v(N)) :- format('v~d',[N]).
value(arg0) :- format('arg0',[]).
value(arg1) :- format('arg1',[]).
value(literal(N)) :- format('UINT64_C(~d)',[N]).
operator(add) :- format(' + ',[]).
operator(xor) :- format(' ^ ',[]).
operator(or) :- format(' | ',[]).
operator(and) :- format(' & ',[]).
operator(shl) :- format(' << ',[]).
operator(shr) :- format(' >> ',[]).
