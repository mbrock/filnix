/*  Shared check parts: a heap check of an object an earlier check
    already tested skips the null test, and right after a check of the
    same object reuses the upper it loaded (docs/perf.md item 17).

    A check `test lower; jz; cmp lower, ptr; jb; mov -16(lower), up;
    sub $Size, up; cmp up, ptr; ja` (split bounds, local selection) has
    two parts that depend only on the object: the null test of its
    lower and the load of its upper. A capability's lower never changes,
    so once a check of one lower has passed, the null test of any later
    check of that lower is dead. Its upper does change, when the object
    is freed (free sets upper = lower), so a loaded upper is reused only
    while nothing could have freed the object, and only while the
    register still holds it. Every check stays where it was, with the
    same tests otherwise, failure label, pointer and lower.

    ## Facts

    | Fact | Holds here when |
    |---|---|
    | `tested(R)` | a full check of a pointer whose lower is R's passed at a point that dominates here |
    | `upper(R)` | the last instruction that touched the object state is a full check of R's lower, and everything since is transparent |
    | `def(Reg, Size)` (machine) | Reg = upper − Size as that check computed it, and no line since wrote Reg or could have freed |

    R is a lower root: a single-definition temporary (parameter, phi or
    instruction) reached from the checked pointer through
    single-definition flights' lower donors (ir.pl's `lower_chain/3`).
    Every name on the way has one definition, so at any point they all
    dominate, the pointer's lower is R's current one (docs/m7.md, round
    4's dominance argument). A pointer with no such root has no fact.

    ## Transfer, merge and invalidators

    - A full check of class R skips its null test under `tested(R)`,
      then adds `tested(R)`, and sets `upper(R)` if its access is
      transparent, otherwise no `upper`.
    - A transparent instruction keeps both facts; any other instruction
      clears `upper`. `tested` has no invalidator: it is a fact about a
      value. Functions with setjmp are left alone.
    - A block starts with the `tested` facts at the end of its immediate
      dominator (`--share=null` and `upper`; `block` starts empty), and
      no `upper`.
    - Transparent (`share_transparent/1`): arithmetic, comparisons,
      conversions, flights, scalar raw accesses and raw pointer loads
      (fused, reused or renewed). Everything else clears `upper`: calls,
      allocations, getters, pointer stores (ensure-aux may exit), cas,
      atomic pointer accesses, fences, va_arg, ABI actions and fixed asm.
    - At the machine level (`shared_uppers/2`) `def(Reg, Size)` is cleared
      by any line that writes Reg, a label, a call, an unconditional jump,
      a fence, a locked instruction, and any line amd64_contract does not
      audit. A conditional jump keeps it on its fall-through.

    An upper is reused only when both levels agree. Under `upper(R)` the
    check emits the placeholder `upper_reuse(r9, Size)`, and every check
    with Size =< 16 marks `upper_def(Reg, Size)` after computing it; Reg
    is %r9 for a check whose upper a later one reuses (flight arithmetic
    between two checks writes %rdx; only calls, pointer stores and cas
    write %r9) and %rdx, the reference's, otherwise. The machine pass turns each placeholder into the adjustment from the
    earlier size, or back into the load where `def` does not hold, and
    deletes the markers.

    `--share=none|block|null|upper` (NANOFIL_SHARE) selects this; the
    default is none. Only the split bounds with local selection share.
*/
:- module(check_share, [share_mode/1, shared_blocks/4, share_transparent/1,
                        share_bounds//4, upper_adjust//3, shared_uppers/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(dcgs)).
:- use_module(ir, [op_kind/2, pointer_memory_effects/2, single_definitions/3]).
:- use_module(cfg, [func_cfg/2, cfg_idoms/2]).
:- use_module(amd64_contract, [instruction_effects/2]).

%! share_mode(-Mode) is det.
%
%  Mode is NANOFIL_SHARE (main.pl's --share=): none, the default; block,
%  null tests shared within a block; null, also from dominating blocks;
%  upper, also the loaded upper right after a check of the same object.
share_mode(Mode) :-
    (   getenv('NANOFIL_SHARE', Mode0), memberchk(Mode0, [none, block, null, upper])
    ->  Mode = Mode0
    ;   Mode = none
    ).

%! shared_blocks(+Mode, +Params-Checked, +Blocks0, -Blocks) is det.
%
%  Blocks are the fused Blocks0 (filc_amd64's fused_blocks/5) with each
%  heap `fused(check(Lo, Hi, Rights, Align), Access)` written
%  `fused(shared(Null, Upper, check(Lo, Hi, Rights, Align)), Access)`:
%  Null is known when `tested` holds for its lower root, else test;
%  Upper is reuse when `upper` holds and its size is at most 16, else
%  load. Lower roots are found in Checked, the blocks before fusion:
%  a fused access hides its destination's definition from
%  single_definitions/3. Mode none, and a function with setjmp, change
%  nothing.
shared_blocks(none, _, Blocks, Blocks) :- !.
shared_blocks(_, _, Blocks, Blocks) :-
    member(block(_, _, Is, _), Blocks), member(let(_, _, setjmp(_), _), Is), !.
shared_blocks(Mode, Params-Checked, Blocks0, Blocks) :-
    single_definitions(Params, Checked, Once),
    empty_assoc(None),
    (   Mode == block
    ->  maplist(shared_block(Mode, Once, None), Blocks0, Blocks, _)
    ;   func_cfg(Blocks0, Cfg), cfg_idoms(Cfg, Idom), Cfg = cfg(_, Rpo, _, _),
        findall(L-B, ( member(B, Blocks0), B = block(L, _, _, _) ), LBs),
        list_to_assoc(LBs, ByLabel),
        foldl(dominated_block(Mode, Once, Idom, ByLabel), Rpo, None-None, Done-_),
        maplist(walked_block(Mode, Once, Done), Blocks0, Blocks)
    ).

% dominated_block(+Mode, +Once, +Idom, +ByLabel, +L, +Done0-Exits0, -Done-Exits):
% L, in reverse postorder, walked from the tested facts at the end of
% its immediate dominator, which comes earlier.
dominated_block(Mode, Once, Idom, ByLabel, L, Done0-Exits0, Done-Exits) :-
    (   get_assoc(L, Idom, D) -> get_assoc(D, Exits0, Tested0) ; empty_assoc(Tested0) ),
    get_assoc(L, ByLabel, Block0),
    shared_block(Mode, Once, Tested0, Block0, Block, Tested),
    put_assoc(L, Done0, Block, Done),
    put_assoc(L, Exits0, Tested, Exits).

% An unreachable block is walked from no facts.
walked_block(Mode, Once, Done, Block0, Block) :-
    Block0 = block(L, _, _, _),
    (   get_assoc(L, Done, Block) -> true
    ;   empty_assoc(None), shared_block(Mode, Once, None, Block0, Block, _)
    ).

shared_block(Mode, Once, Tested0, block(L, Ps, Is0, J), block(L, Ps, Is, J), Tested) :-
    shared_insts(Is0, Mode, Once, none, Tested0, Tested, Is1),
    reverse(Is1, Rev1), foldl(producer, Rev1, []-false, Rev-_), Is = Rev.

% producer(+I, +Is0-Need0, -Is-Need), over a block backwards: a check
% whose upper a later check reuses (Need) computes it into %r9; every
% other loaded upper stays in %rdx, as the reference has it, so the
% register pass still sees %rdx die at the check.
producer(fused(shared(N, Up0, C), A), Is-Need0, [fused(shared(N, Up, C), A)|Is]-Need) :- !,
    (   Up0 = reuse(_) -> Up = Up0, Need = true
    ;   ( Need0 == true -> Up = load(r9) ; Up = load(rdx) ), Need = false
    ).
producer(I, Is-Need, [I|Is]-Need).

% shared_insts(+Is0, +Mode, +Once, +Upper, +Tested0, -Tested, -Is):
% Upper is the lower root of upper(R), or none.
shared_insts([], _, _, _, Tested, Tested, []).
shared_insts([I0|Is0], Mode, Once, Upper0, Tested0, Tested, [I|Is]) :-
    (   I0 = fused(Check, Access), Check = check(_, Size, _, _)
    ->  (   access_pointer(Access, P), lower_root(Once, P, R)
        ->  ( get_assoc(R, Tested0, _) -> Null = known ; Null = test ),
            (   Mode == upper, Upper0 == R, Size =< 16 -> Up = reuse(r9) ; Up = load(rdx) ),
            put_assoc(R, Tested0, true, Tested1),
            ( share_transparent(I0) -> Upper1 = R ; Upper1 = none )
        ;   Null = test, Up = load(rdx), Tested1 = Tested0, Upper1 = none
        ),
        I = fused(shared(Null, Up, Check), Access)
    ;   I = I0, Tested1 = Tested0,
        ( share_transparent(I0) -> Upper1 = Upper0 ; Upper1 = none )
    ),
    shared_insts(Is0, Mode, Once, Upper1, Tested1, Tested, Is).

% lower_root(+Once, +P, -R): R is P's lower root, following
% single-definition flights to the first name that is not one.
% The depth bound stops a cycle of flights in unreachable code, as
% ir:lower_chain/4's does.
lower_root(Once, P, R) :- lower_root(Once, P, R, 0).

lower_root(Once, tmp(X), R, Depth) :-
    get_assoc(X, Once, Def),
    (   Depth < 64, Def = flight(_, _, _, lower(D)), Depth1 is Depth + 1,
        lower_root(Once, D, R0, Depth1)
    ->  R = R0
    ;   R = X
    ).

access_pointer(let(_, _, raw_load(_, _), [P]), P).
access_pointer(raw_store(_, _, _, P), P).
access_pointer(let(_, p, raw_load_pointer(_, _), [P]), P).
access_pointer(raw_store_pointer(_, _, P, _), P).
access_pointer(let(_, _, raw_cas(_, _), [P|_]), P).
access_pointer(touch(P), P).

%! share_transparent(+Inst) is semidet.
%
%  Inst, a fused instruction (filc_amd64's fused_blocks/5), cannot free
%  or reallocate an object, reaches no safepoint, calls nothing and does
%  not synchronize with another thread: the `upper` fact survives it.
%  Stated here, apart from check_reuse's transfer function, for the
%  emitter's own fact.
share_transparent(flight(_, _, _, _)).
share_transparent(loc(_, _)).
share_transparent(reused(Access)) :- transparent_access(Access).
share_transparent(fused(Check, Access)) :-
    Check \== check_function, transparent_access(Access).
share_transparent(let(_, _, Op, Args)) :-
    op_kind(Op, Kind), transparent_kind(Kind, Args).

transparent_access(let(_, _, raw_load(T, _), _)) :- T \== p.
transparent_access(raw_store(W, _, _, _)) :- W \== p.
transparent_access(let(_, p, raw_load_pointer(_, Es), _)) :-
    ( pointer_memory_effects(load, Es) ; pointer_memory_effects(local_load, Es) ), !.
transparent_access(touch(_)).

transparent_kind(additive, _).
transparent_kind(alu, _).
transparent_kind(shift, _).
transparent_kind(neg, _).
transparent_kind(cmp, _).
transparent_kind(ext, _).
transparent_kind(float_convert, _).
transparent_kind(float_to_int, _).
transparent_kind(int_to_float, _).
transparent_kind(cast, _).
transparent_kind(ptoi, _).
transparent_kind(copy, Args) :- \+ memberchk(global(_), Args).

%! share_bounds(+Null, +Upper, +Size, +Fail)// is det.
%
%  The split bounds check (filc_amd64's bounds_check//4, local
%  selection) of the pointer in %rax with its lower in %rcx, jumping to
%  Fail unless lower =< ptr =< upper − Size: the null test unless Null
%  is known, then upper − Size into register R, loaded (Upper =
%  load(R)) or the placeholder `upper_reuse(R, Size)` that
%  shared_uppers/2 resolves (Upper = reuse(R)), and for Size =< 16 the
%  marker `upper_def(R, Size)`. R is %rdx, as the reference check has
%  it, or %r9 for a check whose upper a later one reuses: only calls,
%  pointer stores and cas write %r9, where flight arithmetic writes %rdx.
%  tests/share_smt.py proves the resolved lines against Fil-C's
%  condition.
share_bounds(Null, Upper, Size, Fail) -->
    { upper_reg(Upper, R) },
    null_test(Null, Fail),
    [ins(cmp, q, [reg(rcx), reg(rax)]),
     ins(jb, none, [sym(Fail)])],
    upper_part(Upper, Size, Fail),
    (   { Size =< 16 } -> [upper_def(R, Size)] ; [] ),
    [ins(cmp, q, [reg(R), reg(rax)]),
     ins(ja, none, [sym(Fail)])].

upper_reg(load(R), R).
upper_reg(reuse(R), R).

null_test(test, Fail) -->
    [ins(test, q, [reg(rcx), reg(rcx)]),
     ins(jz, none, [sym(Fail)])].
null_test(known, _) --> [].

% The upper load and borrow test as filc_amd64's split shape emits them
% under local selection (item 6a: no borrow test for Size =< 16).
upper_part(load(R), Size, Fail) -->
    upper_load(R, Size),
    (   { Size =< 16 } -> [] ; [ins(jb, none, [sym(Fail)])] ).
upper_part(reuse(R), Size, _) --> [upper_reuse(R, Size)].

upper_load(R, Size) -->
    [ins(mov, q, [mem(-16, rcx), reg(R)]),
     ins(sub, q, [imm(Size), reg(R)])].

%! upper_adjust(+R, +Size0, +Size)// is det.
%
%  From R = upper − Size0 to upper − Size, both at most 16. Neither
%  borrows: a nonnull lower has its 16-byte header below it and upper >=
%  lower (docs/perf.md item 6a).
upper_adjust(_, Size, Size) --> !, [].
upper_adjust(R, Size0, Size) -->
    { D is Size0 - Size },
    [ins(lea, q, [mem(D, R), reg(R)])].

%! shared_uppers(+Lines0, -Lines) is det.
%
%  Lines are a function body's Lines0 with each `upper_reuse(R, Size)`
%  replaced by upper_adjust//3 from the `upper_def(R, Size0)` before it,
%  where that marker's R still holds (`def`, above), and otherwise by
%  the upper load, and with the markers deleted.
shared_uppers(Lines0, Lines) :- shared_uppers(Lines0, none, Lines).

shared_uppers([], _, []).
shared_uppers([upper_def(R, Size)|Ls0], _, Ls) :- !,
    shared_uppers(Ls0, def(R, Size), Ls).
shared_uppers([upper_reuse(R, Size)|Ls0], Def, Ls) :- !,
    (   Def = def(R0, Size0), R0 == R -> phrase(upper_adjust(R, Size0, Size), Ls, Ls1)
    ;   phrase(upper_load(R, Size), Ls, Ls1)
    ),
    shared_uppers(Ls0, def(R, Size), Ls1).
shared_uppers([L|Ls0], Def0, [L|Ls]) :-
    ( Def0 = def(R, _), keeps_upper(L, R) -> Def = Def0 ; Def = none ),
    shared_uppers(Ls0, Def, Ls).

% keeps_upper(+Line, +R): Line falls through or branches conditionally,
% writes no part of R, is not a fence or locked, and is audited.
keeps_upper(Line, R) :-
    Line = ins(Op, _, _),
    \+ memberchk(Op, [jmp, mfence, 'lock cmpxchg']),
    instruction_effects(Line, effect(_, Writes, _, _, Flow)),
    memberchk(Flow, [next, branch]),
    \+ memberchk(write(R, _), Writes).
