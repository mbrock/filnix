/*  Escape classification of allocs (QBE's ALoc/AEsc).

    alloc_classes(+Func, -Classes)
      Classes: [A-Class] for every alloc temp A of Func, in order, with
        local(Size, Accesses)  every use of A's address is the address of
                               a load or store at a fixed offset, possibly
                               through add/sub of constants or copy.
                               Accesses: ordset of acc(Off, Width), Width
                               in b h w l p. Size is the alloc's operand.
        escapes(Why)           the address is used any other way (stored,
                               passed, returned, compared, converted,
                               merged in a phi, offset by a variable), or
                               it or a temp derived from it is defined
                               more than once, so offsets are unknown.

    address_temps(+Func, -Addrs)
      assoc Temp -> A-Off for each alloc temp (Off 0) and each temp
      derived from one by constant offsets, whatever the class.

    load_width(?LoadType, ?Width)

    A local alloc can only be reached through its own address, so no
    other pointer or integer can name it. Offsets are exact integers (an
    add wraps modulo 2^64, so a huge constant gives a huge offset, which
    promote's bounds check refuses).
*/
:- module(escape, [alloc_classes/2, address_temps/2, load_width/2,
                   def_counts/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).

load_width(l, l).
load_width(sw, w).
load_width(uw, w).
load_width(sh, h).
load_width(uh, h).
load_width(sb, b).
load_width(ub, b).
load_width(p, p).

alloc_classes(F, Classes) :-
    F = func(_, _, _, _, Blocks),
    findall(I, ( member(blk(_, _, Is, _), Blocks), member(I, Is) ), Insts),
    address_temps(F, Addrs),
    def_counts(F, DefCounts),
    findall(A-Size, member(ins(t(A), _, alloc(_), [Size]), Insts), Allocs),
    findall(Root-E,
            ( member(I, Insts), inst_event(I, Addrs, Root-E) ),
            InstEvents),
    findall(Root-esc(phi),
            ( member(blk(_, Phis, _, _), Blocks),
              member(phi(_, _, Args), Phis),
              member(_-t(X), Args),
              get_assoc(X, Addrs, Root-_) ),
            PhiEscapes),
    findall(Root-esc(jump),
            ( member(blk(_, _, _, Jump), Blocks),
              jump_value(Jump, t(X)),
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
    maplist(classify_alloc(Events), Allocs, Classes).

classify_alloc(Events, A-Size, A-Class) :-
    (   get_assoc(A, Events, Es) -> true ; Es = [] ),
    (   memberchk(esc(Why), Es)
    ->  Class = escapes(Why)
    ;   findall(Acc, member(acc(Acc), Es), Accs0),
        sort(Accs0, Accs),
        Class = local(Size, Accs)
    ).

% What an instruction does with addresses: an access at a known offset,
% a constant offset (a derived address, seen by address_temps), or an
% escape of every alloc whose address it reads.
inst_event(ins(_, _, load(T), [t(X)]), Addrs, Root-acc(acc(Off, W))) :-
    get_assoc(X, Addrs, Root-Off), !,
    load_width(T, W).
inst_event(store(W, V, A), Addrs, Event) :- !,
    (   V = t(X), get_assoc(X, Addrs, Root-_), Event = Root-esc(stored)
    ;   A = t(X), get_assoc(X, Addrs, Root-Off), Event = Root-acc(acc(Off, W))
    ).
inst_event(I, Addrs, Root-esc(Why)) :-
    \+ ( offset_of(I, Y, _), get_assoc(Y, Addrs, _) ),  % derived address
    inst_values(I, Why, Vs),
    member(t(X), Vs),
    get_assoc(X, Addrs, Root-_).

% inst_values(+Ins, -Why, -Values): the values Ins reads, and the escape
% reason if one of them is an address.
inst_values(ins(_, _, Op, Args), Op, Args).
inst_values(call(_, F, Args), call, [F|Vs]) :-
    findall(V, member(arg(_, V), Args), Vs).

jump_value(jnz(V, _, _), V).
jump_value(ret(V), V).
jump_value(rets(Vs), V) :- member(V, Vs).

% offset_of(+Ins, -Src, -Delta): Ins computes Src + Delta.
offset_of(ins(_, _, add, [t(X), c(N)]), X, N).
offset_of(ins(_, _, add, [c(N), t(X)]), X, N).
offset_of(ins(_, _, sub, [t(X), c(N)]), X, D) :- D is -N.
offset_of(ins(_, _, copy, [t(X)]), X, 0).

address_temps(func(_, _, _, _, Blocks), Addrs) :-
    findall(I, ( member(blk(_, _, Is, _), Blocks), member(I, Is) ), Insts),
    findall(A-(A-0), member(ins(t(A), _, alloc(_), _), Insts), AllocPairs),
    list_to_assoc(AllocPairs, Addrs0),
    % edge(Pos, D, N): instruction Pos defines D as the source plus N.
    findall(X-edge(Pos, D, N),
            ( nth0(Pos, Insts, Ins),
              Ins = ins(t(D), _, _, _),
              offset_of(Ins, X, N) ),
            Edges0),
    keysort(Edges0, Edges1),
    group_pairs_by_key(Edges1, Edges),
    list_to_assoc(Edges, BySource),
    assoc_to_list(Addrs0, Seeds),
    derive_addresses(Seeds, BySource, Addrs0, Addrs).

% Follow each dependency only when its source is first resolved. Whole
% layers are processed together: as in the old fixed point, a redefined
% temp takes its earliest-resolved definition, then instruction order
% breaks ties. Cycles without an allocation seed remain unresolved.
derive_addresses([], _, Addrs, Addrs).
derive_addresses([S|Ss], BySource, Addrs0, Addrs) :-
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
    foldl(put_pair, New, Addrs0, Addrs1),
    derive_addresses(New, BySource, Addrs1, Addrs).

put_pair(K-V, Assoc0, Assoc) :- put_assoc(K, Assoc0, V, Assoc).

% def_counts(+Func, -Counts): assoc temp -> number of definitions
% (parameters, phis, instructions and call results).
def_counts(func(_, _, _, Params, Blocks), Counts) :-
    findall(N, member(par(_, t(N)), Params), ParamDefs),
    findall(N,
            ( member(blk(_, Phis, Insts, _), Blocks),
              (   member(phi(t(N), _, _), Phis)
              ;   member(ins(t(N), _, _, _), Insts)
              ;   member(call(to(t(N), _), _, _), Insts)
              ;   member(call(tuple(Rs), _, _), Insts),
                  member(to(t(N), _), Rs)
              ) ),
            BlockDefs),
    append(ParamDefs, BlockDefs, Defs),
    msort(Defs, Sorted),
    clumped_pairs(Sorted, Pairs),
    list_to_assoc(Pairs, Counts).

% clumped_pairs(+Sorted, -Pairs): X-N for each run of N equal elements.
clumped_pairs([], []).
clumped_pairs([X|Xs], [X-N|Ps]) :-
    run_of(X, Xs, 1, N, Rest),
    clumped_pairs(Rest, Ps).

run_of(X, [Y|Ys], N0, N, Rest) :-
    X == Y, !,
    N1 is N0 + 1,
    run_of(X, Ys, N1, N, Rest).
run_of(_, Rest, N, N, Rest).
