/*  Address expressions for M5, not a no-alias or bounds proof.

    alias_facts(+Func, -Facts)
      Assoc Temp -> addr(Class, Base, Offset), for l/p values in strict
      SSA functions. Otherwise empty. Base is alloc(Temp), param(Temp),
      symbol(Name), or value(Temp) for an opaque SSA value (including
      loads, calls, casts and phis). A missing fact means unknown, e.g.
      a cycle in unreachable code with no base to start from.

      Address = Base + Offset modulo 2^64; Offset is the signed 64-bit
      representative. In class p the capability is also the base's.
      Follow only same-class copies and constant add/sub. A w copy is
      not an address alias, even when its operand was an l.

      Different bases may alias! Parameters, symbols and opaque values
      need not name different objects. An alloc base names the current
      execution of that SSA definition, not all its loop iterations.
      These facts alone justify neither removing a bounds check nor
      moving an access or allocation across control flow.
*/
:- module(alias, [alias_facts/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(cfg).
:- use_module(promote, [strict_ssa/3]).

alias_facts(F, Facts) :-
    F = func(_, _, _, _, Blocks),
    fn_cfg(Blocks, Cfg),
    dominators(Cfg, Idom),
    (   strict_ssa(F, Cfg, Idom)
    ->  findall(D-def(K, Source), address_def(F, D, K, Source), Defs),
        list_to_assoc(Defs, ByTemp),
        findall(D-addr(K, Base, 0),
                ( member(D-def(K, Source), Defs),
                  address_base(Source, D, K, ByTemp, Base) ),
                Seeds),
        list_to_assoc(Seeds, Initial),
        findall(S-edge(D, Delta),
                ( member(D-def(K, Source), Defs),
                  address_offset(Source, K, ByTemp, S, Delta) ),
                Edges0),
        keysort(Edges0, Edges1),
        group_pairs_by_key(Edges1, Edges),
        list_to_assoc(Edges, Users),
        propagate_offsets(Seeds, Users, Initial, Facts)
    ;   empty_assoc(Facts)
    ).

% address_def(+F, -D, -K, -Source): temp D of address class K is a
% parameter (param), an instruction (ins(Op, Args)) or opaque.
address_def(func(_, _, _, Params, _), D, K, param) :-
    member(par(K, t(D)), Params),
    address_class(K).
address_def(func(_, _, _, _, Blocks), D, K, Source) :-
    member(blk(_, Phis, Insts, _), Blocks),
    (   member(phi(t(D), K, _), Phis), Source = opaque
    ;   member(ins(t(D), K, Op, Args), Insts), Source = ins(Op, Args)
    ;   member(call(to(t(D), K), _, _), Insts), Source = opaque
    ;   member(call(tuple(Tos), _, _), Insts),
        member(to(t(D), K), Tos),
        Source = opaque
    ),
    address_class(K).

address_class(l).
address_class(p).

% address_base(+Source, +D, +K, +Defs, -Base): D starts a base of its
% own; it fails for a definition that offsets another address.
address_base(param, D, _, _, param(D)) :- !.
address_base(ins(alloc(_), _), D, _, _, alloc(D)) :- !.
address_base(ins(copy, [glo(S)]), _, _, _, symbol(S)) :- !.
address_base(Source, D, K, Defs, value(D)) :-
    \+ address_offset(Source, K, Defs, _, _).

% address_offset(+Source, +K, +Defs, -S, -Delta): Source computes the
% same-class temp S plus Delta.
address_offset(ins(copy, [t(S)]), K, Defs, S, 0) :-
    get_assoc(S, Defs, def(K, _)).
address_offset(ins(add, [t(S), c(N)]), K, Defs, S, N) :-
    get_assoc(S, Defs, def(K, _)).
address_offset(ins(add, [c(N), t(S)]), l, Defs, S, N) :-
    get_assoc(S, Defs, def(l, _)).
address_offset(ins(sub, [t(S), c(N)]), K, Defs, S, Delta) :-
    get_assoc(S, Defs, def(K, _)),
    Delta is -N.

% Every derived definition has one source. Root phis rather than chasing
% their cycles: they select a value from an earlier dynamic execution.
% Visit a definition only when its source is known, regardless of layout.
propagate_offsets([], _, Facts, Facts).
propagate_offsets([S-Addr|Pending0], Users, Facts0, Facts) :-
    (   get_assoc(S, Users, Edges) -> true ; Edges = [] ),
    foldl(derive_address(Addr), Edges, Facts0-Pending0, Facts1-Pending),
    propagate_offsets(Pending, Users, Facts1, Facts).

% The offset wraps modulo 2^64 to its signed 64-bit representative.
derive_address(addr(K, Base, Off), edge(D, Delta),
               Facts0-Pending, Facts-[D-Addr|Pending]) :-
    U is (Off + Delta) mod 18446744073709551616,
    (   U >= 9223372036854775808
    ->  O is U - 18446744073709551616
    ;   O = U
    ),
    Addr = addr(K, Base, O),
    put_assoc(D, Facts0, Addr, Facts).
