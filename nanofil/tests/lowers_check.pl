/* Hand-written frames for lowers_check (docs/lowers.md), independent of
   lower_roots.pl and frame_slots.pl: each case states the blocks and
   the frame a producer might have chosen, and whether the GC-root
   contract holds. The rejected ones are the plants: a root dead while
   its flight is live, a redefined root, setjmp, a write at a call's
   return while the flight is live, and a merge where one path does not
   hold the root. */
:- module(lowers_check_tests, [lowers_checker/0]).

:- use_module('../src/lowers_check').
:- use_module(library(lists)).

lowers_checker :-
    forall(lowers_case(Name, Expected, Params, Blocks, Frame),
           run_case(Name, Expected, Params, Blocks, Frame)).

run_case(Name, Expected, Params, Blocks, Frame) :-
    (   catch(check_lowers(Name, Params, Blocks, Frame), nanofil_error(_), fail)
    ->  Got = accept
    ;   Got = reject
    ),
    (   Got == Expected -> true
    ;   throw(error(lowers_checker(Name, Expected, Got), lowers_checker/0))
    ).

% d is r + 8 with r's lower; the frame gives d r's entry, p0.
shared(Extra, frame([], [lower(storage(pointer,0))|Roots],
                    [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(storage(pointer,0)),
                     tmp(d)-storage(address,0), lower(tmp(d))-lower(storage(pointer,0))|As])) :-
    findall(lower(storage(pointer,I)), member(I-_, Extra), Roots),
    findall(A, ( member(I-T, Extra),
                 ( A = tmp(T)-storage(pointer,I) ; A = lower(tmp(T))-lower(storage(pointer,I)) ) ),
            As).

flight(flight(tmp(d), add, [address(tmp(r)), const(8)], lower(tmp(r)))).
use_d(let(tmp(v), l, load(l), [tmp(d)])).

% Accepted: r is a parameter, dead after the flight; d is live across a
% call, which may also raise (the exception exit pops the frame).
lowers_case(across_call, accept, [param(p, tmp(r))],
            [block(start, [], [F, call(result(tmp(x), l), global(g), [arg(p, tmp(d))]), U], ret(tmp(v)))],
            Frame) :-
    flight(F), use_d(U), shared([], Frame).
% Accepted: a chain, e = d + 8, all three in r's entry.
lowers_case(chain, accept, [param(p, tmp(r))],
            [block(start, [],
                   [F, flight(tmp(e), add, [address(tmp(d)), const(8)], lower(tmp(d))),
                    call(void, global(g), []), let(tmp(v), l, load(l), [tmp(e)])],
                   ret(tmp(v)))],
            frame([], [lower(storage(pointer,0))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(storage(pointer,0)),
                   tmp(d)-storage(address,0), lower(tmp(d))-lower(storage(pointer,0)),
                   tmp(e)-storage(address,1), lower(tmp(e))-lower(storage(pointer,0))])) :-
    flight(F).
% Rejected: t reuses r's entry while d is still live (the root's slot
% was not kept for its flight).
lowers_case(dead_root, reject, [param(p, tmp(r))],
            [block(start, [], [F, call(result(tmp(t), p), global(g), []),
                               let(tmp(w), l, load(l), [tmp(t)]), U], ret(tmp(v)))],
            frame([], [lower(storage(pointer,0))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(storage(pointer,0)),
                   tmp(d)-storage(address,0), lower(tmp(d))-lower(storage(pointer,0)),
                   tmp(t)-storage(pointer,0), lower(tmp(t))-lower(storage(pointer,0))])) :-
    flight(F), use_d(U).
% Accepted: the same t with an entry of its own.
lowers_case(other_entry, accept, [param(p, tmp(r))],
            [block(start, [], [F, call(result(tmp(t), p), global(g), []),
                               let(tmp(w), l, load(l), [tmp(t)]), U], ret(tmp(v)))],
            Frame) :-
    flight(F), use_d(U), shared([1-t], Frame).
% Rejected: r is defined again while d is live.
lowers_case(redefined_root, reject, [],
            [block(start, [], [call(result(tmp(r), p), global(g), []), F,
                               call(result(tmp(r), p), global(g), []), U], ret(tmp(v)))],
            Frame) :-
    flight(F), use_d(U), shared([], Frame).
% Rejected: a call's result written to r's entry at its return, while d
% is live after it.
lowers_case(call_result_overwrites, reject, [param(p, tmp(r))],
            [block(start, [], [F, call(result(tmp(x), p), global(g), [arg(p, tmp(d))]), U],
                   ret(tmp(v)))],
            frame([], [lower(storage(pointer,0))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(storage(pointer,0)),
                   tmp(d)-storage(address,0), lower(tmp(d))-lower(storage(pointer,0)),
                   tmp(x)-storage(pointer,0), lower(tmp(x))-lower(storage(pointer,0))])) :-
    flight(F), use_d(U).
% Rejected: the across_call frame in a function that calls setjmp:
% longjmp restores lowers[], which the analysis does not model.
lowers_case(setjmp, reject, [param(p, tmp(r)), param(p, tmp(buf))],
            [block(start, [], [let(tmp(j), w, setjmp(setjmp), [tmp(buf), const(0)]), F,
                               call(void, global(g), []), U], ret(tmp(v)))],
            frame([], [lower(storage(pointer,0)), lower(storage(pointer,1))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(storage(pointer,0)),
                   tmp(d)-storage(address,0), lower(tmp(d))-lower(storage(pointer,0)),
                   tmp(buf)-storage(pointer,1), lower(tmp(buf))-lower(storage(pointer,1))])) :-
    flight(F), use_d(U).
% Accepted: d is defined in both arms, sharing r's entry in one and
% written to it from q in the other; either way the entry holds d.
lowers_case(merge, accept, [param(p, tmp(r)), param(p, tmp(q)), param(w, tmp(c))],
            [block(start, [], [], branch(tmp(c), a, b)),
             block(a, [], [F], goto(join)),
             block(b, [], [flight(tmp(d), add, [address(tmp(q)), const(8)], lower(tmp(q)))], goto(join)),
             block(join, [], [call(void, global(g), []), U], ret(tmp(v)))],
            Frame) :-
    flight(F), use_d(U), shared([1-q], Frame).
% Rejected: the same, but r is still live at the join, and on b's path
% its entry holds d's lower from q.
lowers_case(merge_root_live, reject, [param(p, tmp(r)), param(p, tmp(q)), param(w, tmp(c))],
            [block(start, [], [], branch(tmp(c), a, b)),
             block(a, [], [F], goto(join)),
             block(b, [], [flight(tmp(d), add, [address(tmp(q)), const(8)], lower(tmp(q)))], goto(join)),
             block(join, [], [call(void, global(g), []), U, let(tmp(y), l, load(l), [tmp(r)])], ret(tmp(v)))],
            Frame) :-
    flight(F), use_d(U), shared([1-q], Frame).
% Accepted: the same merge with d's own entry.
lowers_case(merge_own, accept, [param(p, tmp(r)), param(p, tmp(q)), param(w, tmp(c))],
            [block(start, [], [], branch(tmp(c), a, b)),
             block(a, [], [F], goto(join)),
             block(b, [], [flight(tmp(d), add, [address(tmp(q)), const(8)], lower(tmp(q)))], goto(join)),
             block(join, [], [call(void, global(g), []), U], ret(tmp(v)))],
            frame([], [lower(storage(pointer,0)), lower(storage(pointer,1)), lower(storage(pointer,2))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(storage(pointer,0)),
                   tmp(q)-storage(pointer,1), lower(tmp(q))-lower(storage(pointer,1)),
                   tmp(d)-storage(pointer,2), lower(tmp(d))-lower(storage(pointer,2))])) :-
    flight(F), use_d(U).
% Accepted: a loop pointer p (a phi, with an entry of its own) and
% q = p + 8, which shares p's entry and is live after the loop.
lowers_case(loop_phi_own, accept, [param(p, tmp(r)), param(w, tmp(c))],
            [block(start, [], [], goto(loop)),
             block(loop, [phi(tmp(p), p, [start-tmp(r), loop-tmp(q)])],
                   [flight(tmp(q), add, [address(tmp(p)), const(8)], lower(tmp(p))),
                    call(void, global(g), [])],
                   branch(tmp(c), poll(loop), out)),
             block(out, [], [let(tmp(v), l, load(l), [tmp(q)])], ret(tmp(v)))],
            frame([], [lower(storage(pointer,0)), lower(storage(pointer,1))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(storage(pointer,0)),
                   tmp(p)-storage(pointer,1), lower(tmp(p))-lower(storage(pointer,1)),
                   tmp(q)-storage(address,0), lower(tmp(q))-lower(storage(pointer,1))])).
% Accepted: the loop pointer p and q = p + 8 both share r's entry, so
% the back edge copies no lower.
lowers_case(loop_phi_shared, accept, [param(p, tmp(r)), param(w, tmp(c))],
            [block(start, [], [], goto(loop)),
             block(loop, [phi(tmp(p), p, [start-tmp(r), loop-tmp(q)])],
                   [flight(tmp(q), add, [address(tmp(p)), const(8)], lower(tmp(p))),
                    call(void, global(g), [])],
                   branch(tmp(c), poll(loop), out)),
             block(out, [], [let(tmp(v), l, load(l), [tmp(q)])], ret(tmp(v)))],
            frame([], [lower(storage(pointer,0))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(storage(pointer,0)),
                   tmp(p)-storage(address,0), lower(tmp(p))-lower(storage(pointer,0)),
                   tmp(q)-storage(address,1), lower(tmp(q))-lower(storage(pointer,0))])).
% Rejected: the phi's inputs derive from c, which the loop defines after
% the phi: the phi still holds the previous iteration's c when c is
% written again (FilPizlonator's dominance condition).
lowers_case(loop_phi_inner_root, reject, [param(w, tmp(k))],
            [block(start, [], [call(result(tmp(a), p), global(g), [])], goto(loop)),
             block(loop, [phi(tmp(p), p, [start-tmp(a), loop-tmp(x)])],
                   [call(result(tmp(c), p), global(g), []),
                    flight(tmp(x), add, [address(tmp(c)), const(8)], lower(tmp(c))),
                    let(tmp(v), l, load(l), [tmp(p)])],
                   branch(tmp(k), poll(loop), out)),
             block(out, [], [], ret(tmp(v)))],
            frame([], [lower(storage(pointer,0))],
                  [tmp(a)-storage(pointer,0), lower(tmp(a))-lower(storage(pointer,0)),
                   tmp(c)-storage(pointer,0), lower(tmp(c))-lower(storage(pointer,0)),
                   tmp(p)-storage(address,0), lower(tmp(p))-lower(storage(pointer,0)),
                   tmp(x)-storage(address,1), lower(tmp(x))-lower(storage(pointer,0))])).
% Rejected: an entry holds an unrelated lower at the loop's back edge.
lowers_case(loop_overwrite, reject, [param(p, tmp(r)), param(w, tmp(c))],
            [block(start, [], [], goto(loop)),
             block(loop, [phi(tmp(p), p, [start-tmp(r), loop-tmp(q)])],
                   [flight(tmp(q), add, [address(tmp(p)), const(8)], lower(tmp(p))),
                    call(result(tmp(t), p), global(g), []),
                    let(tmp(w), l, load(l), [tmp(t)])],
                   branch(tmp(c), poll(loop), out)),
             block(out, [], [let(tmp(v), l, load(l), [tmp(q)])], ret(tmp(v)))],
            frame([], [lower(storage(pointer,0)), lower(storage(pointer,1))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(storage(pointer,0)),
                   tmp(p)-storage(pointer,1), lower(tmp(p))-lower(storage(pointer,1)),
                   tmp(q)-storage(address,0), lower(tmp(q))-lower(storage(pointer,1)),
                   tmp(t)-storage(pointer,1), lower(tmp(t))-lower(storage(pointer,1))])).
% Rejected: a temporary's lower aliased to a jmpbuf root, which setjmp
% writes and longjmp's restore skips (review finding).
lowers_case(jmpbuf_alias, reject, [param(p, tmp(r))],
            [block(start, [], [U0], ret(tmp(v)))],
            frame([], [lower(tmp(hidden(setjmp_buf(j))))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(tmp(hidden(setjmp_buf(j))))])) :-
    U0 = let(tmp(v), l, load(l), [tmp(r)]).
% Rejected: a temporary's lower aliased to a shadow root, which edges
% write without this function's definitions.
lowers_case(shadow_entry, reject, [param(p, tmp(r))],
            [block(start, [], [U0], ret(tmp(v)))],
            frame([], [lower(shadow_slot(p,0))],
                  [tmp(r)-storage(pointer,0), lower(tmp(r))-lower(shadow_slot(p,0))])) :-
    U0 = let(tmp(v), l, load(l), [tmp(r)]).
