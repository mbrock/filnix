/*  checkclass.pl: what filcc's forward check scheduling would do with
    each check that nanofil -O keeps (docs/perf.md item 16).

    Usage, from nanofil/src (checkclass.py runs it per object):

        ../bin/nanofil --script ../bench/profile/checkclass.pl FILE.i

    Compiles FILE as `nanofil -O cc` does (inlining small,
    simplification full, pizlonation, then check reuse and renewal, the
    -O default), and prints one tab-separated line per heap check,
    renewal and local check that remains:

        Function Block Index Op Class Offset Loop Rights Use

    Class is what FilPizlonator's forward propagation
    (removeRedundantChecksUsingForwardAI) would know before the access,
    restated over nanofil's IR. A check's *canonical pointer* is the
    root its address reaches through single-definition `add`, `sub` and
    `copy` flights by constant offsets. A variable offset makes a new
    root, `vi(Base, Offset, Sign, Index)`, where Index is the index's
    value number: its pure single-definition lets expanded down to
    leaves. So two flights that compute the same index from the same
    values share a root, as LLVM's GVN makes them one GEP. Facts per
    root: the lowest offset whose lower bound is known, the highest
    whose upper bound is known, whether the object may have been freed
    since (a call, an allocation, or a poll edge clears it) and whether
    write rights are known. Spatial facts survive calls and polls, as
    filcc's do; a redefinition of any temporary the root mentions kills
    its facts. At a join a fact holds if it holds on every incoming edge
    (bounds: the weaker one).

    | Class | Before the access |
    |---|---|
    | `first` | nothing is known of the root |
    | `covered` | bounds, rights and not-freed are all known: filcc deletes the check |
    | `flags` | bounds are known, not-freed (or write rights) is not: filcc tests the flags only |
    | `partial_block` | the root was checked earlier in this block with no call since, but not this range |
    | `partial` | the root was checked on every path, but not this range |

    `covered_hull` and `flags_hull`: as `covered` and `flags`, but no one
    earlier check covers the range, only the hull of several (filcc
    keeps the lower bound at the least offset and the upper at the
    greatest). Use is `pointer` when the access loads or stores a
    pointer, `scalar` otherwise.

    Offset is `const`, `var` (a variable index) or `base` (a variable
    index whose base root has facts). Loop is `inv` when the check is in
    a natural loop and no temporary its root mentions is defined in the
    innermost one, `loop` when in a loop otherwise, `none` outside
    loops. Nothing is changed or trusted: this only measures.
*/
:- use_module('../../src/ir').
:- use_module('../../src/c_lex').
:- use_module('../../src/c_parse').
:- use_module('../../src/c_lower').
:- use_module('../../src/opt').
:- use_module('../../src/pizlonate').
:- use_module('../../src/check_reuse').
:- use_module('../../src/cfg').
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(pairs)).
:- use_module(library(ordsets)).

:- initialization(main).

main :-
    current_prolog_flag(argv, [File|_]),
    once(i_file_tokens(File, Tokens)),
    once(c_parse(Tokens, Items)),
    once(c_module(Items, M0)),
    once(optimize(o1(small, full), M0, M)),
    once(pizlonate_module(M, C0)),
    once(reuse_checks(C0, C1)),
    once(renew_checks(C1, module(Is))),
    forall(member(func(N, _, _, Ps, Bs), Is),
           ( catch(func_lines(N, Ps, Bs), E,
                   format(user_error, "checkclass: ~w: ~q~n", [N, E])) -> true
           ; format(user_error, "checkclass: ~w failed~n", [N]) )),
    halt(0).

func_lines(N, Ps, Bs) :-
    single_definitions(Ps, Bs, Once),
    def_blocks(Ps, Bs, DefBlock),
    func_cfg(Bs, Cfg), Cfg = cfg(Entry, Rpo, _, _),
    cfg_idoms(Cfg, Idom),
    natural_loops(Cfg, Idom, Loops),
    blocks_assoc(Bs, ByLabel),
    edges(Bs, Edges),
    empty_assoc(E0),
    put_assoc(Entry, E0, facts([]), In0),
    fixpoint(Rpo, ByLabel, Edges, Once, In0, In),
    forall(( member(L, Rpo), get_assoc(L, In, facts(F0)), get_assoc(L, ByLabel, block(L, Phis, Insts, _)) ),
           ( kill_phis(Phis, F0, F1),
             block_lines(Insts, 0, N, L, Once, DefBlock, Loops, F1) )).

blocks_assoc(Bs, A) :-
    findall(L-B, ( member(B, Bs), B = block(L, _, _, _) ), Ps),
    list_to_assoc(Ps, A).

% edges(+Blocks, -Edges): From-To-Poll for every CFG edge.
edges(Bs, Edges) :-
    findall(F-T-Poll,
            ( member(block(F, _, _, J), Bs), jump_target(J, T),
              ( sub_term(S, J), S == poll(T) -> Poll = poll ; Poll = plain ) ),
            Edges0),
    sort(Edges0, Edges).

def_blocks(Ps, Bs, A) :-
    Bs = [block(Entry, _, _, _)|_],
    findall(N-Entry, member(param(_, tmp(N)), Ps), D0),
    findall(N-L, ( member(block(L, Phis, Insts, _), Bs),
                   ( member(phi(tmp(N), _, _), Phis) ; member(I, Insts), inst_def(I, N) ) ), D1),
    append(D0, D1, D),
    sort(1, @>=, D, DU),
    list_to_assoc(DU, A).

%% The forward analysis

fixpoint(Rpo, ByLabel, Edges, Once, In0, In) :-
    foldl(visit(ByLabel, Edges, Once), Rpo, In0-false, In1-Changed),
    (   Changed == true -> fixpoint(Rpo, ByLabel, Edges, Once, In1, In) ; In = In1 ).

visit(ByLabel, Edges, Once, L, In0-C0, In-C) :-
    (   get_assoc(L, In0, facts(F0))
    ->  get_assoc(L, ByLabel, block(L, Phis, Insts, _)),
        kill_phis(Phis, F0, F1),
        foldl(transfer(Once), Insts, F1-L, Out-_),
        findall(T-P, member(L-T-P, Edges), Succs),
        foldl(propagate(Out), Succs, In0-C0, In-C)
    ;   In = In0, C = C0 ).

propagate(Out, T-Poll, In0-C0, In-C) :-
    ( Poll == poll -> maplist(freeable, Out, Out1) ; Out1 = Out ),
    (   get_assoc(T, In0, facts(Old))
    ->  meet(Old, Out1, New),
        ( New == Old -> In = In0, C = C0 ; put_assoc(T, In0, facts(New), In), C = true )
    ;   put_assoc(T, In0, facts(Out1), In), C = true ).

% A fact: f(Root, Lo, Hi, NotFree, Write, Block). Block is where the
% root's facts were last established with no call since, or none.
freeable(f(R, Lo, Hi, _, W, _, Rs), f(R, Lo, Hi, false, W, none, Rs)).

meet(A, B, M) :-
    findall(f(R, Lo, Hi, NF, W, Bl, Rs),
            ( member(f(R, Lo1, Hi1, NF1, W1, B1, Rs1), A),
              member(f(R2, Lo2, Hi2, NF2, W2, B2, Rs2), B), R2 == R,
              Lo is max(Lo1, Lo2), Hi is min(Hi1, Hi2),
              and(NF1, NF2, NF), and(W1, W2, W),
              ord_intersection(Rs1, Rs2, Rs),
              ( B1 == B2 -> Bl = B1 ; Bl = none ) ),
            M0),
    msort(M0, M).

and(true, true, true) :- !.
and(_, _, false).

kill_phis(Phis, F0, F) :-
    foldl(kill_phi, Phis, F0, F).
kill_phi(phi(tmp(N), _, _), F0, F) :- kill_root(N, F0, F).

kill_root(N, F0, F) :- exclude(root_mentions(N), F0, F).
root_mentions(N, f(R, _, _, _, _, _, _)) :- sub_term(S, R), S == t(N), !.

transfer(Once, I, F0-L, F-L) :-
    (   check_inst(I, P, Lo, Hi, Rights)
    ->  canon(Once, P, Root, c(O)),
        A is O + Lo, B is O + Hi, establish(Root, A, B, Rights, L, F0, F1)
    ;   frees(I)
    ->  maplist(freeable, F0, F1)
    ;   F1 = F0 ),
    (   inst_def(I, D) -> kill_root(D, F1, F) ; F = F1 ).

establish(Root, A, B, Rights, L, F0, F) :-
    ( Rights == write -> W = true ; W = false ),
    (   select(f(R, Lo0, Hi0, _, W0, _, Rs0), F0, F1), R == Root
    ->  Lo is min(Lo0, A), Hi is max(Hi0, B),
        or(W0, W, W1),
        ord_add_element(Rs0, A-B, Rs),
        msort([f(Root, Lo, Hi, true, W1, L, Rs)|F1], F)
    ;   msort([f(Root, A, B, true, W, L, [A-B])|F0], F) ).

or(false, false, false) :- !.
or(_, _, true).

check_inst(let(_, a, check(Lo, Hi, R, _), [tmp(P)]), P, Lo, Hi, R).
check_inst(let(_, a, renew(Lo, Hi, R, _), [_, tmp(P)]), P, Lo, Hi, R).
check_inst(let(_, a, renew_if(Lo, Hi, R, _), [tmp(P), _]), P, Lo, Hi, R).
check_inst(let(_, a, check_limit(Lo, Hi, R, _), [tmp(P), _]), P, Lo, Hi, R).

% What may free an object: a call or an allocation (filcc's
% instructionMayFree: a call that may write memory).
frees(call(_, _, _)).
frees(let(_, _, alloc(_), _)).
frees(let(_, _, va_arg, _)).
frees(let(_, _, setjmp(_), _)).

% canon(+Once, +P, -Root, -Off): P's canonical pointer and constant offset.
canon(Once, P, Root, Off) :-
    (   get_assoc(P, Once, flight(_, Op, Args, _)),
        flight_offset(Op, Args, B, Off0)
    ->  canon(Once, B, Root0, c(K0)),
        (   Off0 = c(K)
        ->  Root = Root0, K1 is K0 + K, Off = c(K1)
        ;   Off0 = var(Sign, I),
            value_number(Once, 8, I, E),
            Root = vi(Root0, K0, Sign, E), Off = c(0) )
    ;   Root = t(P), Off = c(0) ).

flight_offset(copy, [address(tmp(B))], B, c(0)).
flight_offset(add, [address(tmp(B)), const(K)], B, c(K)) :- !.
flight_offset(sub, [address(tmp(B)), const(K)], B, c(K1)) :- !, K1 is -K.
flight_offset(add, [address(tmp(B)), I], B, var(1, I)).
flight_offset(sub, [address(tmp(B)), I], B, var(-1, I)).

value_number(_, _, const(K), K) :- !.
value_number(Once, D, tmp(N), E) :- !,
    (   D > 0, get_assoc(N, Once, let(_, K, Op, Args)), \+ impure_op(Op)
    ->  D1 is D - 1,
        maplist(value_number(Once, D1), Args, Es),
        E = op(Op, K, Es)
    ;   E = t(N) ).
value_number(_, _, A, A).

impure_op(load(_)).
impure_op(raw_load(_, _)).
impure_op(raw_load_pointer(_, _)).
impure_op(atomic_load(_)).
impure_op(cas(_)).
impure_op(raw_cas(_, _)).
impure_op(alloc(_)).
impure_op(va_arg).
impure_op(va_args).
impure_op(setjmp(_)).
impure_op(span_test(_, _)).
impure_op(limit(_)).
impure_op(check(_, _, _, _)).
impure_op(renew(_, _, _, _)).
impure_op(renew_if(_, _, _, _)).
impure_op(check_limit(_, _, _, _)).
impure_op(check_local(_, _, _, _, _)).
impure_op(check_function).

%% Classification

block_lines([], _, _, _, _, _, _, _).
block_lines([I|Is], K, N, L, Once, DefBlock, Loops, F0) :-
    (   checkish(I, Op, P, Lo, Hi, Rights)
    ->  (   P == local
        ->  Class = local, OffT = const, Root = none
        ;   canon(Once, P, Root, Off),
            classify(Off, Root, Lo, Hi, Rights, L, F0, Class),
            offset_term(Root, F0, OffT)
        ),
        loop_term(Root, L, DefBlock, Loops, LoopT),
        consumer(I, Is, Use),
        format("~w\t~w\t~w\t~w\t~w\t~w\t~w\t~w\t~w~n", [N, L, K, Op, Class, OffT, LoopT, Rights, Use])
    ;   true ),
    transfer(Once, I, F0-L, F1-L),
    K1 is K + 1,
    block_lines(Is, K1, N, L, Once, DefBlock, Loops, F1).

% consumer(+Check, +Rest, -Use): pointer when the access the proof
% serves loads or stores a pointer, else scalar.
consumer(let(tmp(Q), _, _, _), Is, Use) :-
    (   member(I, Is), sub_term(S, I), S == tmp(Q)
    ->  ( I = let(_, p, raw_load_pointer(_, _), _) -> Use = pointer
        ; I = raw_store_pointer(_, _, _, _) -> Use = pointer
        ; Use = scalar )
    ;   Use = none ).

checkish(let(_, a, check(Lo, Hi, R, _), [tmp(P)]), check, P, Lo, Hi, R).
checkish(let(_, a, renew(Lo, Hi, R, _), [_, tmp(P)]), renew, P, Lo, Hi, R).
checkish(let(_, a, renew_if(Lo, Hi, R, _), [tmp(P), _]), renew_if, P, Lo, Hi, R).
checkish(let(_, a, check_limit(Lo, Hi, R, _), [tmp(P), _]), check_limit, P, Lo, Hi, R).
checkish(let(_, a, check_local(_, _, Bytes, R, _), []), check_local, local, 0, Bytes, R).

classify(c(O), Root, Lo, Hi, Rights, L, F, Class) :-
    (   member(f(R, KLo, KHi, NF, W, Bl, Rs), F), R == Root
    ->  A is O + Lo, B is O + Hi,
        (   KLo =< A, KHi >= B
        ->  (   NF == true, ( Rights == write -> W == true ; true )
            ->  Class0 = covered
            ;   Class0 = flags ),
            % Covered by one earlier check, or only by the hull of several
            % (filcc's lower bound at the least offset, upper at the most).
            (   member(X-Y, Rs), X =< A, Y >= B -> Class = Class0
            ;   atom_concat(Class0, '_hull', Class) )
        ;   Bl == L, NF == true
        ->  Class = partial_block
        ;   Class = partial )
    ;   Class = first ).

offset_term(t(_), _, const).
offset_term(vi(R, _, _, _), F, T) :-
    ( member(f(R1, _, _, _, _, _, _), F), R1 == R -> T = base ; T = var ).

loop_term(Root, L, DefBlock, Loops, T) :-
    findall(Size-H-Body,
            ( gen_assoc(H, Loops, loop(_, Body)), ord_memberchk(L, Body), length(Body, Size) ),
            Ls),
    (   Ls == []
    ->  T = none
    ;   keysort(Ls, [_-_-Inner|_]),
        (   Root \== none,
            \+ ( sub_term(S, Root), nonvar(S), S = t(N),
                 ( get_assoc(N, DefBlock, DB) -> ord_memberchk(DB, Inner) ; true ) )
        ->  T = inv
        ;   T = loop )
    ).
