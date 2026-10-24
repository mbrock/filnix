/*  Pizlonation: from the unchecked IR to the checked IR (ir.pl), the
    form the Fil-C backend compiles, named after Fil-C's LLVM pass.

    The checks Fil-C requires are implicit in the unchecked stage, where
    a load or store at a p address means "check, then access". This pass
    states them: each such access becomes a check, whose class a result
    is the proven address, and the raw access that reads it.

      let(tmp(D), K, load(T), [A])
          ->  let(tmp(Q), a, check(0, S, read, Al), [A]),
              let(tmp(D), K, raw_load(T, 0), [tmp(Q)])
      store(W, V, A)
          ->  let(tmp(Q), a, check(0, S, write, Al), [A]),
              raw_store(W, 0, V, tmp(Q))

    S and Al are the access's size and alignment (ir:access_size_align/3).
    And every edge that does not go forward in block order gets a
    pollcheck, poll(L), so every cycle polls.

    This is the naive pass: one check per access, right before it, and
    every backward edge polls. Merging checks needs a model of free in
    the interpreter first (docs/pizlonation.md).

    setjmp's jmp_buf store and va_arg's cursor stay opaque: the backend
    checks them inside the instruction, as the runtime helpers they call
    do.
*/
:- module(pizlonate, [pizlonate_module/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(format)).
:- use_module(ir).
:- use_module(cfg, [inst_def/2]).

%! pizlonate_module(+M0, -M) is det.
%
%  M is the unchecked module M0 with every check explicit and a poll on
%  every edge to a block at or before its source in block order. In a
%  plain module, whose addresses are not Fil-C pointers, only the polls
%  are added.

pizlonate_module(M0, module(Items)) :-
    module_mode(M0, Mode),
    M0 = module(Items0),
    maplist(pizlonated_item(Mode), Items0, Items).

pizlonated_item(Mode, func(Name, Linkage, Ret, Params, Blocks0),
                func(Name, Linkage, Ret, Params, Blocks)) :-
    func_temp_names(Params, Blocks0, Names),
    findall(L-I, nth0(I, Blocks0, block(L, _, _, _)), Pairs),
    list_to_assoc(Pairs, Index),
    pizlonated_blocks(Blocks0, p(Mode, Names, Index), 0, 0, Blocks).
pizlonated_item(_, data(Name, Linkage, Align, Items),
                data(Name, Linkage, Align, Items)).

% func_temp_names(+Params, +Blocks, -Names): the assoc of every temp
% name the function defines, so a fresh name avoids them. A valid
% function reads only temps it defines.
func_temp_names(Params, Blocks, Names) :-
    findall(N-t,
            (   member(param(_, tmp(N)), Params)
            ;   member(block(_, Phis, Insts, _), Blocks),
                (   member(phi(tmp(N), _, _), Phis)
                ;   member(Inst, Insts), inst_def(Inst, N)
                )
            ),
            Pairs0),
    sort(Pairs0, Pairs),
    list_to_assoc(Pairs, Names).

% pizlonated_blocks(+Blocks0, +P, +I, +N, -Blocks): Blocks are Blocks0,
% the first at index I, checked; P is p(Mode, Names, Index), and N
% counts fresh names. Plain recursion: Trealla copies a closure's
% arguments at every call.
pizlonated_blocks([], _, _, _, []).
pizlonated_blocks([block(L, Phis, Insts0, Jump0)|Bs0], P, I, N0,
                  [block(L, Phis, Insts, Jump)|Bs]) :-
    P = p(Mode, Names, Index),
    checked_insts(Insts0, Mode, Names, N0, N, Insts),
    polled_jump(Jump0, I, Index, Jump),
    I1 is I + 1,
    pizlonated_blocks(Bs0, P, I1, N, Bs).

% checked_insts(+Insts0, +Mode, +Names, +N0, -N, -Insts).
checked_insts([], _, _, N, N, []).
checked_insts([Inst0|Insts0], Mode, Names, N0, N, Insts) :-
    (   Mode == filc, checked_access(Inst0, Q, Insts, Insts1)
    ->  fresh_name(Names, N0, N1, Q)
    ;   Insts = [Inst0|Insts1], N1 = N0
    ),
    checked_insts(Insts0, Mode, Names, N1, N, Insts1).

% checked_access(+Access, ?Q, -Insts, ?Insts1): Insts less Insts1 are
% Access's check, defining tmp(Q), and its raw access.
checked_access(let(D, K, load(T), [A]), Q,
               [let(tmp(Q), a, check(0, Size, read, Align), [A]),
                let(D, K, raw_load(T, 0), [tmp(Q)])|Is], Is) :-
    access_size_align(T, Size, Align), !.
checked_access(store(W, V, A), Q,
               [let(tmp(Q), a, check(0, Size, write, Align), [A]),
                raw_store(W, 0, V, tmp(Q))|Is], Is) :-
    access_size_align(W, Size, Align), !.

% fresh_name(+Names, +N0, -N, -Q): Q is chkI for the least I >= N0 not
% among Names, and N is I + 1.
fresh_name(Names, N0, N, Q) :-
    format(atom(Q0), "chk~d", [N0]),
    N1 is N0 + 1,
    (   get_assoc(Q0, Names, _)
    ->  fresh_name(Names, N1, N, Q)
    ;   Q = Q0, N = N1
    ).

% polled_jump(+Jump0, +From, +Index, -Jump): Jump is Jump0, ending the
% block at index From, with poll(L) for each target L at or before it.
polled_jump(goto(L), From, Index, goto(T)) :-
    polled_target(L, From, Index, T).
polled_jump(branch(V, L1, L2), From, Index, branch(V, T1, T2)) :-
    polled_target(L1, From, Index, T1),
    polled_target(L2, From, Index, T2).
polled_jump(ret(V), _, _, ret(V)).
polled_jump(rets(Vs), _, _, rets(Vs)).
polled_jump(ret, _, _, ret).
polled_jump(unreachable, _, _, unreachable).

% Checked IR (a poll target, and no load or store) passes unchanged.
polled_target(poll(L), _, _, poll(L)) :- !.
polled_target(L, From, Index, T) :-
    get_assoc(L, Index, To),
    (   To =< From -> T = poll(L) ; T = L ).
