/*  Address expressions for M5 (alias_facts/2), not a no-alias or
    bounds proof.

    Address = Base + Offset modulo 2^64; Offset is the signed 64-bit
    representative. In class p the capability is also the base's.
    Follow only same-class copies and constant add/sub. A w copy is not
    an address alias, even when its operand was an l.

    Different bases may alias! Parameters, symbols and opaque values
    need not name different objects. An alloc base names the current
    execution of that SSA definition, not all its loop iterations. These
    facts alone justify neither removing a bounds check nor moving an
    access or allocation across control flow.
*/
:- module(alias, [alias_facts/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(cfg).
:- use_module(promote, [strict_ssa/3]).
:- use_module(ir, [op_kind/2]).

%! alias_facts(+Func, -Facts) is det.
%
%  Facts is the assoc Temp -> addr(Class, Base, Offset), for the l/p
%  values of Func if it is in strict SSA form, and otherwise empty. Base
%  is alloc(Temp), param(Temp), symbol(Name), or value(Temp) for an
%  opaque SSA value (including loads, calls, casts and phis). A missing
%  fact means unknown, e.g. a cycle in unreachable code with no base to
%  start from.

alias_facts(F, Facts) :-
    F = func(_, _, _, _, Blocks),
    func_cfg(Blocks, Cfg),
    cfg_idoms(Cfg, Idom),
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
        pending_facts(Seeds, Users, Initial, Facts)
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
address_base(param, D, _, _, param(D)).
address_base(opaque, D, _, _, value(D)).
address_base(ins(Op, Args), D, K, Defs, Base) :-
    ins_base(Op, Args, D, K, Defs, Base).

% ins_base(+Op, +Args, +D, +K, +Defs, -Base): as address_base/5, for an
% instruction.
ins_base(Op, Args, D, K, Defs, Base) :-
    op_kind(Op, Kind),
    kind_base(Kind, Op, Args, D, K, Defs, Base).

% kind_base(+Kind, +Op, +Args, +D, +K, +Defs, -Base): as ins_base/6, for
% Op of Kind. An alloc and the copy of a symbol start their own bases,
% an add, sub or copy that offsets an address (address_offset/5) starts
% none, and every other instruction starts a value base.
kind_base(additive, Op, Args, D, K, Defs, value(D)) :-
    \+ address_offset(ins(Op, Args), K, Defs, _, _).
kind_base(alu, _, _, D, _, _, value(D)).
kind_base(shift, _, _, D, _, _, value(D)).
kind_base(neg, _, _, D, _, _, value(D)).
kind_base(copy, _, [V], D, K, Defs, Base) :- copy_base(V, D, K, Defs, Base).
kind_base(ptoi, _, _, D, _, _, value(D)).
kind_base(itop, _, _, D, _, _, value(D)).
kind_base(va_args, _, _, D, _, _, value(D)).
kind_base(va_arg, _, _, D, _, _, value(D)).
kind_base(cmp, _, _, D, _, _, value(D)).
kind_base(ext, _, _, D, _, _, value(D)).
kind_base(load, _, _, D, _, _, value(D)).
kind_base(alloc, _, _, D, _, _, alloc(D)).

% copy_base(+V, +D, +K, +Defs, -Base): as kind_base/7, for D a copy of V.
copy_base(glo(S), _, _, _, symbol(S)).
copy_base(t(S), D, K, Defs, value(D)) :-
    \+ address_offset(ins(copy, [t(S)]), K, Defs, _, _).
copy_base(c(_), D, _, _, value(D)).

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

% pending_facts(+Pending, +Users, +Facts0, -Facts): Facts is
% Facts0 with the addresses derived, directly or not, from Pending, the
% list of S-Addr whose users are still to be derived. Every derived
% definition has one source, so a definition is reached only once its
% source is known, regardless of layout. Phis are roots rather than
% followed around their cycles: they select a value from an earlier
% dynamic execution.
pending_facts([], _, Facts, Facts).
pending_facts([S-Addr|Pending0], Users, Facts0, Facts) :-
    (   get_assoc(S, Users, Edges) -> true ; Edges = [] ),
    foldl(addr_edge_state(Addr), Edges, Facts0-Pending0,
          Facts1-Pending),
    pending_facts(Pending, Users, Facts1, Facts).

% addr_edge_state(+Addr, +Edge, +Facts0-Pending0, -Facts-Pending):
% the user D of Edge has the address Addr plus Delta, in Facts and in
% front of Pending0. The offset wraps modulo 2^64 to its signed 64-bit
% representative.
addr_edge_state(addr(K, Base, Off), edge(D, Delta),
                       Facts0-Pending, Facts-[D-Addr|Pending]) :-
    U is (Off + Delta) mod 18446744073709551616,
    (   U >= 9223372036854775808
    ->  O is U - 18446744073709551616
    ;   O = U
    ),
    Addr = addr(K, Base, O),
    put_assoc(D, Facts0, Addr, Facts).
