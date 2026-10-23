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
    def_counts(F, Defs),
    findall(A-Size, member(ins(t(A), _, alloc(_), [Size]), Insts), Allocs),
    findall(Root-E, ( member(I, Insts), inst_event(I, Addrs, Root-E) ), Es1),
    findall(Root-esc(phi), ( member(blk(_, Phis, _, _), Blocks),
                             member(phi(_, _, Args), Phis), member(_-t(X), Args),
                             get_assoc(X, Addrs, Root-_) ), Es2),
    findall(Root-esc(jump), ( member(blk(_, _, _, J), Blocks), jump_value(J, t(X)),
                              get_assoc(X, Addrs, Root-_) ), Es3),
    % A temp derived from A that is also defined some other way.
    findall(Root-esc(redefined), ( gen_assoc(X, Addrs, Root-_),
                                   get_assoc(X, Defs, N), N > 1 ), Es4),
    append([Es1, Es2, Es3, Es4], Es),
    % Group once by allocation, preserving event order (and hence the
    % first escape reason), rather than scanning every event per alloc.
    keysort(Es, Sorted), group_pairs_by_key(Sorted, Pairs),
    list_to_assoc(Pairs, Events),
    maplist(classify(Events), Allocs, Classes).

classify(Events, A-Size, A-Class) :-
    ( get_assoc(A, Events, Es) -> true ; Es = [] ),
    (   memberchk(esc(Why), Es) -> Class = escapes(Why)
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
inst_event(store(W, V, A), Addrs, E) :- !,
    (   V = t(X), get_assoc(X, Addrs, Root-_), E = Root-esc(stored)
    ;   A = t(X), get_assoc(X, Addrs, Root-Off), E = Root-acc(acc(Off, W))
    ).
inst_event(I, Addrs, Root-esc(Why)) :-
    \+ ( offset_of(I, Y, _), get_assoc(Y, Addrs, _) ),  % derived address
    inst_values(I, Why, Vs),
    member(t(X), Vs),
    get_assoc(X, Addrs, Root-_).

inst_values(ins(_, _, Op, Args), Op, Args).
inst_values(call(_, F, Args), call, [F|Vs]) :- findall(V, member(arg(_, V), Args), Vs).

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
    findall(A-(A-0), member(ins(t(A), _, alloc(_), _), Insts), Ps0),
    list_to_assoc(Ps0, A0),
    findall(I, ( member(I, Insts), I = ins(_, _, _, _), offset_of(I, _, _) ), Offs),
    derive(Offs, A0, Addrs).

% Close the map under constant offsets. Each round adds at least one
% temp, and there are finitely many, so this terminates.
derive(Offs, A0, A) :-
    findall(D-(Root-O),
            ( member(I, Offs), I = ins(t(D), _, _, _), offset_of(I, X, N),
              \+ get_assoc(D, A0, _),
              get_assoc(X, A0, Root-O0), O is O0 + N ),
            New0),
    (   New0 == [] -> A = A0
    ;   sort(1, @<, New0, New),   % one entry per temp; redefinitions are caught later
        foldl(put_pair, New, A0, A1),
        derive(Offs, A1, A)
    ).

put_pair(K-V, A0, A) :- put_assoc(K, A0, V, A).

% def_counts(+Func, -Counts): assoc temp -> number of definitions
% (parameters, phis, instructions and call results).
def_counts(func(_, _, _, Params, Blocks), Counts) :-
    findall(N, member(par(_, t(N)), Params), D0),
    findall(N, ( member(blk(_, Phis, Is, _), Blocks),
                 (   member(phi(t(N), _, _), Phis)
                 ;   member(ins(t(N), _, _, _), Is)
                 ;   member(call(to(t(N), _), _, _), Is)
                 ;   member(call(tuple(Rs), _, _), Is), member(to(t(N), _), Rs)
                 ) ), D1),
    append(D0, D1, Ds),
    msort(Ds, S),
    clumped_pairs(S, Ps),
    list_to_assoc(Ps, Counts).

clumped_pairs([], []).
clumped_pairs([X|Xs], [X-N|Ps]) :- run_of(X, Xs, 1, N, Rest), clumped_pairs(Rest, Ps).
run_of(X, [Y|Ys], N0, N, Rest) :- X == Y, !, N1 is N0 + 1, run_of(X, Ys, N1, N, Rest).
run_of(_, Rest, N, N, Rest).
