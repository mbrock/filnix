/*  Escape classification of allocs: alloc_classes/2 tells, for each
    alloc of a function, whether its address is only used for loads and
    stores at known offsets. Prior art: QBE's ALoc/AEsc.

    The module also exports the relations alloc_classes/2 is built
    from: address_temps/2, load_width/2 and def_counts/2.

    The analysis rests on one fact: a local alloc can only be reached
    through its own address, so no other pointer or integer can name it.

    Offsets are exact integers. An IR add wraps modulo 2^64, but here a
    huge constant gives a huge offset, which promote's bounds check
    refuses.
*/
:- module(escape, [alloc_classes/2, alloc_classes/4, address_temps/2,
                   load_width/2, def_counts/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(ir, [op_kind/2]).

%! load_width(?LoadType, ?Width) is nondet.
%
%  A supported integer or pointer load reads a slot of width Width
%  (b h w l p). Other load types must make the allocation escape.

load_width(l, l).
load_width(sw, w).
load_width(uw, w).
load_width(sh, h).
load_width(uh, h).
load_width(sb, b).
load_width(ub, b).
load_width(p, p).

%! alloc_classes(+Func, -Classes) is det.
%
%  Classes is [A-Class] for every alloc temp A of Func, in order, with
%  Class one of:
%
%    - local(Size, Accesses): every use of A's address is the address of
%      a load or store at a fixed offset, possibly through add/sub of
%      constants or copy. Accesses is an ordset of acc(Off, Width),
%      Width in b h w l p. Size is the alloc's operand.
%    - escapes(Why): the address is used any other way (stored, passed,
%      returned, compared, converted, merged in a phi, offset by a
%      variable, loaded with an unsupported type), or it or a temp
%      derived from it is defined more than once, so offsets are unknown.

alloc_classes(F, Classes) :-
    address_temps(F, Addrs),
    def_counts(F, DefCounts),
    alloc_classes(F, Addrs, DefCounts, Classes).

%! alloc_classes(+Func, +Addrs, +DefCounts, -Classes) is det.
%
%  As alloc_classes/2, given Func's address_temps/2 and def_counts/2.
alloc_classes(F, Addrs, DefCounts, Classes) :-
    F = func(_, _, _, _, Blocks),
    findall(I, ( member(block(_, _, Is, _), Blocks), member(I, Is) ), Insts),
    findall(A-Size, member(let(tmp(A), _, alloc(_), [Size]), Insts), Allocs),
    findall(Root-E,
            ( member(I, Insts), inst_event(I, Addrs, Root-E) ),
            InstEvents),
    findall(Root-esc(phi),
            ( member(block(_, Phis, _, _), Blocks),
              member(phi(_, _, Args), Phis),
              member(_-tmp(X), Args),
              get_assoc(X, Addrs, Root-_) ),
            PhiEscapes),
    findall(Root-esc(jump),
            ( member(block(_, _, _, Jump), Blocks),
              jump_value(Jump, tmp(X)),
              get_assoc(X, Addrs, Root-_) ),
            JumpEscapes),
    % A temp derived from A that is also defined some other way.
    findall(Root-esc(redefined),
            ( gen_assoc(X, Addrs, Root-_),
              get_assoc(X, DefCounts, N),
              N > 1 ),
            Redefined),
    append([InstEvents, PhiEscapes, JumpEscapes, Redefined], Events0),
    % Group once by allocation, preserving event order (and hence the
    % first escape reason), rather than scanning every event per alloc.
    keysort(Events0, Sorted),
    group_pairs_by_key(Sorted, Pairs),
    list_to_assoc(Pairs, Events),
    maplist(events_alloc_class(Events), Allocs, Classes).

% events_alloc_class(+Events, +A-Size, -A-Class): Class is the class of
% the alloc A, of operand Size, given the assoc Events of each alloc's
% events in order: escapes for the first escape, or else local.
events_alloc_class(Events, A-Size, A-Class) :-
    (   get_assoc(A, Events, Es) -> true ; Es = [] ),
    (   memberchk(esc(Why), Es)
    ->  Class = escapes(Why)
    ;   findall(Acc, member(acc(Acc), Es), Accs0),
        sort(Accs0, Accs),
        Class = local(Size, Accs)
    ).

% inst_event(+Ins, +Addrs, -Root-Event) is nondet: Event is what Ins
% does with the address of alloc Root: an access at a known offset, or
% an escape of every alloc whose address it reads. A constant offset (a
% derived address, seen by address_temps) is neither.
inst_event(let(D, K, Op, Args), Addrs, Event) :-
    op_kind(Op, Kind),
    kind_event(Kind, let(D, K, Op, Args), Addrs, Event).
inst_event(store(W, V, A), Addrs, Event) :-
    (   V = tmp(X),
        get_assoc(X, Addrs, Root-_),
        Event = Root-esc(stored)
    ;   A = tmp(X),
        get_assoc(X, Addrs, Root-Off),
        Event = Root-acc(acc(Off, W))
    ).
% Atomic accesses are not slot accesses: their objects escape, so they
% stay heap objects, which Fil-C's atomic helpers require (atomic boxes
% live in a heap object's aux).
inst_event(let(_, _, atomic_load(_), [tmp(X)]), Addrs, Root-esc(atomic)) :-
    get_assoc(X, Addrs, Root-_).
inst_event(atomic_store(_, V, A), Addrs, Root-esc(atomic)) :-
    member(tmp(X), [V, A]),
    get_assoc(X, Addrs, Root-_).
% A cas, of an integer as of a pointer, lets every address it reads
% escape: its object stays on the heap, which lock cmpxchg on a shared
% object and Fil-C's pointer helper both need, and promotion never
% deletes the object of a cas it would leave behind.
inst_event(let(_, _, cas(_), Args), Addrs, Root-esc(atomic)) :-
    member(tmp(X), Args),
    get_assoc(X, Addrs, Root-_).
% A full-width vector check (docs/vector-access.md) keeps its object on
% the heap: promoting it would need the static bounds to discharge it.
inst_event(access(_, tmp(X), _, _), Addrs, Root-esc(access)) :-
    get_assoc(X, Addrs, Root-_).
% A fixed-register asm reads its inputs' values: in plain mode a w input
% can be a derived address, whose object then stays (docs/asm-fixed.md).
inst_event(asm_fixed(_, Ins, _), Addrs, Root-esc(asm)) :-
    member(_-tmp(X), Ins),
    get_assoc(X, Addrs, Root-_).
inst_event(call(_, F, Args), Addrs, Root-esc(call)) :-
    findall(V, member(arg(_, V), Args), Vs),
    member(tmp(X), [F|Vs]),
    get_assoc(X, Addrs, Root-_).

% kind_event(+Kind, +Ins, +Addrs, -Root-Event) is nondet: as
% inst_event/3, for the instruction Ins of an Op of Kind. A load
% accesses its address only when its slot width is supported; otherwise
% it escapes, so promotion cannot mistake an unknown access for no use.
% Every other op lets the addresses it reads escape.
kind_event(load, let(_, _, load(T), [tmp(X)]), Addrs,
           Root-Event) :-
    get_assoc(X, Addrs, Root-Off),
    (   load_width(T, W)
    ->  Event = acc(acc(Off, W))
    ;   Event = esc(load(T))
    ).
kind_event(additive, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(alu, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(shift, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(neg, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(copy, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(ptoi, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(itop, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(va_args, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(va_arg, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(setjmp, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(va_arg, let(_, _, _, [tmp(X)]), Addrs,
           Root-acc(acc(Off, p))) :- get_assoc(X, Addrs, Root-Off).
kind_event(cmp, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(ext, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).
kind_event(alloc, Ins, Addrs, Event) :- ins_escape(Ins, Addrs, Event).

% ins_escape(+Ins, +Addrs, -Root-esc(Op)) is nondet: Ins, an instruction
% of Op that is not a derived address, reads the address of alloc Root.
ins_escape(let(D, K, Op, Args), Addrs, Root-esc(Op)) :-
    \+ ( offset_of(let(D, K, Op, Args), Y, _),         % derived address
         get_assoc(Y, Addrs, _) ),
    member(tmp(X), Args),
    get_assoc(X, Addrs, Root-_).

jump_value(branch(V, _, _), V).
jump_value(ret(V), V).
jump_value(rets(Vs), V) :- member(V, Vs).

% offset_of(+Ins, -Src, -Delta): Ins computes Src + Delta.
offset_of(let(_, _, add, [tmp(X), const(N)]), X, N).
offset_of(let(_, _, add, [const(N), tmp(X)]), X, N).
offset_of(let(_, _, sub, [tmp(X), const(N)]), X, D) :- D is -N.
offset_of(let(_, _, copy, [tmp(X)]), X, 0).

%! address_temps(+Func, -Addrs) is det.
%
%  Addrs is the assoc Temp -> A-Off for each alloc temp A (Off 0) and
%  each temp derived from one by constant offsets, whatever the class.

address_temps(func(_, _, _, _, Blocks), Addrs) :-
    findall(I, ( member(block(_, _, Is, _), Blocks), member(I, Is) ), Insts),
    findall(A-(A-0), member(let(tmp(A), _, alloc(_), _), Insts), AllocPairs),
    list_to_assoc(AllocPairs, Addrs0),
    % edge(Pos, D, N): instruction Pos defines D as the source plus N.
    findall(X-edge(Pos, D, N),
            ( nth0(Pos, Insts, Ins),
              Ins = let(tmp(D), _, _, _),
              offset_of(Ins, X, N) ),
            Edges0),
    keysort(Edges0, Edges1),
    group_pairs_by_key(Edges1, Edges),
    list_to_assoc(Edges, BySource),
    assoc_to_list(Addrs0, Seeds),
    layers_addrs(Seeds, BySource, Addrs0, Addrs).

% layers_addrs(+Layer, +BySource, +Addrs0, -Addrs): Addrs is
% Addrs0 with the temps derived, directly or not, from the X-(Root-Off)
% pairs of Layer and not yet in Addrs0. A dependency is followed only
% when its source is first resolved, a whole layer at a time: as in the
% old fixed point, a redefined temp takes its earliest-resolved
% definition, then instruction order breaks ties. Cycles without an
% allocation seed remain unresolved.
layers_addrs([], _, Addrs, Addrs).
layers_addrs([S|Ss], BySource, Addrs0, Addrs) :-
    findall(Pos-(D-(Root-Off)),
            ( member(X-(Root-Off0), [S|Ss]),
              get_assoc(X, BySource, Edges),
              member(edge(Pos, D, N), Edges),
              \+ get_assoc(D, Addrs0, _),
              Off is Off0 + N ),
            Found),
    keysort(Found, Ordered),
    pairs_values(Ordered, Pairs),
    % One entry per temp; redefinitions are caught later.
    sort(1, @<, Pairs, New),
    foldl(pair_assoc, New, Addrs0, Addrs1),
    layers_addrs(New, BySource, Addrs1, Addrs).

pair_assoc(K-V, Assoc0, Assoc) :-
    put_assoc(K, Assoc0, V, Assoc).

%! def_counts(+Func, -Counts) is det.
%
%  Counts is the assoc Temp -> number of definitions of Temp in Func
%  (parameters, phis, instructions and call results).
def_counts(func(_, _, _, Params, Blocks), Counts) :-
    findall(N, member(param(_, tmp(N)), Params), ParamDefs),
    findall(N,
            ( member(block(_, Phis, Insts, _), Blocks),
              (   member(phi(tmp(N), _, _), Phis)
              ;   member(let(tmp(N), _, _, _), Insts)
              ;   member(call(result(tmp(N), _), _, _), Insts)
              ;   member(call(tuple(Rs), _, _), Insts),
                  member(result(tmp(N), _), Rs)
              ;   member(asm_fixed(_, _, Outs), Insts),
                  member(_-tmp(N), Outs)
              ) ),
            BlockDefs),
    append(ParamDefs, BlockDefs, Defs),
    msort(Defs, Sorted),
    clumped_pairs(Sorted, Pairs),
    list_to_assoc(Pairs, Counts).

% clumped_pairs(+Sorted, -Pairs): Pairs is X-N for each run of N equal
% elements X of Sorted.
clumped_pairs([], []).
clumped_pairs([X|Xs], [X-N|Ps]) :-
    run_of(X, Xs, 1, N, Rest),
    clumped_pairs(Rest, Ps).

% run_of(+X, +Xs, +N0, -N, -Rest): Xs is a run of N - N0 copies of X
% followed by Rest, which does not start with X.
run_of(X, [Y|Ys], N0, N, Rest) :-
    X == Y,
    !,
    N1 is N0 + 1,
    run_of(X, Ys, N1, N, Rest).
run_of(_, Rest, N, N, Rest).
