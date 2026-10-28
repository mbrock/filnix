/* Hand-written fixtures for amd64_regs_check, independent of the
   allocator. Each negative case gives the checker the stream its map
   determines, so only an obligation (or the comparison, where the
   proposal differs) can reject it. */
:- module(regs_check_tests, [regs_checker/0, operands_checker/0]).

:- use_module('../src/amd64_regs_check').
:- use_module(library(assoc)).
:- use_module(library(lists)).

regs_checker :-
    forall(regs_case(Name, Homes, Map, Saves, Body, Expected),
           run_case(Name, Homes, Map, Saves, Body, Expected)),
    forall(raw_case(Name, Homes, Map, Saves, Before),
           run_raw(Name, Homes, Map, Saves, Before)),
    good_stream,
    proposal_cases.

% Whole streams the checker must reject, each with the stream its map
% determines (or the reference itself when there is none).
run_raw(Name, Homes, Map, Saves, Before) :-
    (   determined(Map, Saves, Before, After) -> true ; After = Before ),
    (   \+ check_regs(regs_metadata(false,f,Homes,Saves), Map, Before, After)
    ->  true
    ;   throw(error(regs_checker(Name, no), regs_checker/0))
    ).

frame([ins(push,q,[reg(rbp)]), ins(mov,q,[reg(rsp),reg(rbp)]), ins(sub,q,[imm(32),reg(rsp)])]).
check([ins(cmp,q,[reg(rsp),mem(0,rdi)]), ins(jae,none,[plt(filc_stack_overflow_failure)])]).

% A home written before the saves: the caller's rbx would be lost.
raw_case(home_write_before_saves, Hs, [-8-rbx], [save(rbx,-24)], B) :-
    homes(Hs), frame(F), check(C), exit(E),
    append([[label(f)], F, [ins(mov,q,[imm(5),mem(-8,rbp)])], C,
            [ins(mov,q,[mem(-8,rbp),reg(rax)])], E], B).
% A back edge into the prologue runs the saves again with rbx changed.
raw_case(back_edge_into_prologue, Hs, [-8-rbx], [save(rbx,-24)], B) :-
    homes(Hs), frame(F), check(C), exit(E),
    append([[label(f)], F, [label(top)], C,
            [ins(mov,q,[reg(rdx),mem(-8,rbp)]), ins(mov,q,[mem(-8,rbp),reg(rax)]),
             ins(test,q,[reg(rax),reg(rax)]), ins(jnz,none,[sym(top)])], E], B).
% A jump past the saves restores an uninitialized save slot.
raw_case(jump_past_saves, Hs, [-8-rbx], [save(rbx,-24)], B) :-
    homes(Hs), frame(F), check(C), exit(E),
    append([[label(f)], F, [ins(test,q,[reg(rdi),reg(rdi)]), ins(jnz,none,[sym(skip)])], C,
            [label(skip), ins(mov,q,[reg(rdx),mem(-8,rbp)]),
             ins(mov,q,[mem(-8,rbp),reg(rax)])], E], B).
% Overlapping homes: the reference reads eax's bits in the high half.
raw_case(overlapping_homes, [home(-8,[l]), home(-4,[w])], [-8-r10, -4-r11], [], B) :-
    exit(E), whole_list([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
                         ins(mov,l,[reg(eax),mem(-4,rbp)]),
                         ins(mov,q,[mem(-8,rbp),reg(rax)])|E], B).
% Every description of a mapped home must be scalar.
raw_case(duplicate_pointer_home, [home(-8,[p]), home(-8,[l])], [-8-r10], [], B) :-
    exit(E), whole_list([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
                         ins(mov,q,[mem(-8,rbp),reg(rax)])|E], B).
% movq $2^32 has no memory form; the register form would be movabs.
raw_case(wide_immediate, Hs, [-8-r10], [], B) :-
    homes(Hs), exit(E),
    whole_list([ins(mov,q,[imm(4294967296),mem(-8,rbp)]),
                ins(mov,q,[mem(-8,rbp),reg(rax)])|E], B).
% A call into the body returns into the wrong context.
raw_case(call_into_body, Hs, [-8-rbx], [save(rbx,-24)], B) :-
    homes(Hs), exit(E),
    append([[ins(mov,q,[reg(rdx),mem(-8,rbp)]), ins(call,none,[sym(inner)]),
             ins(mov,q,[mem(-8,rbp),reg(rax)])], E, [label(inner), ins(ud2,none,[])]], Body),
    whole_list(Body, B).

whole_list(Body, B) :- whole(Body, B).

% A function: label, prologue and stack check, Body.
whole(Body, [label(f), ins(push,q,[reg(rbp)]), ins(mov,q,[reg(rsp),reg(rbp)]),
             ins(sub,q,[imm(32),reg(rsp)]), ins(cmp,q,[reg(rsp),mem(0,rdi)]),
             ins(jae,none,[plt(filc_stack_overflow_failure)])|Body]).

run_case(Name, Homes, Map, Saves, Body, Expected) :-
    whole(Body, Before),
    (   determined(Map, Saves, Before, After) -> true ; After = Before ),
    (   Expected == yes, check_regs(regs_metadata(false,f,Homes,Saves), Map, Before, After)
    ->  true
    ;   Expected == no, \+ check_regs(regs_metadata(false,f,Homes,Saves), Map, Before, After)
    ->  true
    ;   throw(error(regs_checker(Name, Expected), regs_checker/0))
    ).

% The stream the map determines, when there is one.
determined(Map, Saves, [label(f)|Body], [label(f)|After]) :-
    list_to_assoc(Map, Mapped),
    allocated_stream(Body, Mapped, Saves, After).

exit([ins(leave,none,[]), ins(ret,none,[])]).

% -8 lives across a call; -16 does not.
across_call(Body) :-
    exit(Exit),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(call,none,[sym(g)]),
            ins(mov,l,[mem(-8,rbp),reg(eax)]),
            ins(mov,q,[reg(rax),mem(-16,rbp)]),
            ins(mov,q,[mem(-16,rbp),reg(rdx)])], Exit, Body).

homes([home(-8,[w]), home(-16,[w,l])]).

% A home lives across lock cmpxchg through another register; it cannot
% be cmpxchg's memory operand, which is no whole move of it.
regs_case(cmpxchg_beside_home, Hs, [-8-r10], [], B, yes) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins('lock cmpxchg',q,[reg(rcx),mem(0,rsi)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)])], E, B).
regs_case(cmpxchg_on_home, Hs, [-8-r10], [], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins('lock cmpxchg',q,[reg(rcx),mem(-8,rbp)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)])], E, B).
regs_case(callee_saved_across_call, Hs, [-16-r10, -8-rbx], [save(rbx,-24)], B, yes) :-
    homes(Hs), across_call(B).
regs_case(scratch_across_call, Hs, [-16-r10, -8-r11], [], B, no) :-
    homes(Hs), across_call(B).
% Both homes in rbx while both are live.
regs_case(shared_register_conflict, Hs, [-16-rbx, -8-rbx], [save(rbx,-24)], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(mov,q,[reg(rcx),mem(-16,rbp)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)]),
            ins(mov,q,[mem(-16,rbp),reg(rax)])], E, B).
% Sharing is fine once the first home is dead.
regs_case(shared_register_disjoint, Hs, [-16-r10, -8-r10], [], B, yes) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)]),
            ins(mov,q,[reg(rcx),mem(-16,rbp)]),
            ins(mov,q,[mem(-16,rbp),reg(rax)])], E, B).
% A 32-bit store to memory keeps the high half; to a register it zeroes it.
regs_case(movl_store_high_half_live, Hs, [-8-r10], [], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(mov,l,[reg(eax),mem(-8,rbp)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)])], E, B).
regs_case(movl_store_high_half_dead, Hs, [-8-r10], [], B, yes) :-
    homes(Hs), exit(E),
    append([ins(mov,l,[reg(eax),mem(-8,rbp)]),
            ins(mov,l,[mem(-8,rbp),reg(ecx)])], E, B).
% A read before any write sees the slot, which the register cannot.
regs_case(live_at_entry, Hs, [-8-r10], [], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[mem(-8,rbp),reg(rax)])], E, B).
% Liveness follows the back edge: -8 is read at the top of the loop, so it
% is live while -16 is written below the read.
regs_case(loop_back_edge, Hs, [-16-r10, -8-r10], [], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            label(top),
            ins(mov,q,[mem(-8,rbp),reg(rax)]),
            ins(mov,q,[reg(rcx),mem(-16,rbp)]),
            ins(mov,q,[mem(-16,rbp),reg(rax)]),
            ins(test,q,[reg(rax),reg(rax)]),
            ins(jnz,none,[sym(top)])], E, B).
regs_case(unknown_jump, Hs, [-8-r10], [], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(jmp,none,[sym(elsewhere)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)])], E, B).
regs_case(falls_off_the_end, Hs, [-8-r10], [], B, no) :-
    homes(Hs),
    B = [ins(mov,q,[reg(rdx),mem(-8,rbp)]), ins(mov,q,[mem(-8,rbp),reg(rax)])].
regs_case(names_an_allocatable_register, Hs, [-8-r10], [], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(mov,q,[reg(rbx),reg(rax)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)])], E, B).
regs_case(address_of_home, Hs, [-8-r10], [], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(lea,q,[mem(-8,rbp),reg(rax)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)])], E, B).
regs_case(save_slot_touched, Hs, [-8-rbx], [save(rbx,-24)], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(mov,q,[reg(rax),mem(-24,rbp)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)])], E, B).
% A partial access of a mapped home has no whole-register form.
regs_case(high_half_access, Hs, [-8-r10], [], B, no) :-
    homes(Hs), exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(mov,l,[mem(-4,rbp),reg(eax)])], E, B).
regs_case(pointer_home, [home(-8,[w,p])], [-8-r10], [], B, no) :-
    exit(E),
    append([ins(mov,q,[reg(rdx),mem(-8,rbp)]),
            ins(mov,q,[mem(-8,rbp),reg(rax)])], E, B).
regs_case(missing_save, Hs, [-8-rbx], [], B, no) :-
    homes(Hs), across_call(B).

% The determined stream, written out by hand.
good_stream :-
    homes(Hs), across_call(Body), whole(Body, Before),
    whole([ins(mov,q,[reg(rbx),mem(-24,rbp)]),
           ins(mov,q,[reg(rdx),reg(rbx)]),
           ins(call,none,[sym(g)]),
           ins(mov,l,[reg(ebx),reg(eax)]),
           ins(mov,q,[reg(rax),reg(r10)]),
           ins(mov,q,[reg(r10),reg(rdx)]),
           ins(mov,q,[mem(-24,rbp),reg(rbx)]),
           ins(leave,none,[]), ins(ret,none,[])], After),
    (   check_regs(regs_metadata(false,f,Hs,[save(rbx,-24)]), [-16-r10,-8-rbx],
                   Before, After)
    ->  true
    ;   throw(error(regs_checker(good_stream, yes), regs_checker/0))
    ),
    shared_analysis(Hs, Before, After).

% check_regs/5 takes the allocator's analysis; it must be of the very
% body and cover every mapped home.
shared_analysis(Hs, Before, After) :-
    Meta = regs_metadata(false,f,Hs,[save(rbx,-24)]), Map = [-16-r10,-8-rbx],
    impl_body(f, Before, _, Body),
    body_analysis(Body, [-16,-8], Full),
    body_analysis(Body, [-16], Partial),
    (   check_regs(Meta, Map, Before, After, Full) -> true
    ;   throw(error(regs_checker(shared_analysis, yes), regs_checker/0))
    ),
    forall(member(Name-A, [partial_analysis-Partial, no_analysis-none]),
           (   \+ check_regs(Meta, Map, Before, After, A) -> true
           ;   throw(error(regs_checker(Name, no), regs_checker/0)) )),
    % live_at_entry's stream, given the analysis of the same body with the
    % entry read turned into a write: that analysis sees nothing live at
    % entry, so only the check that it is of this body rejects it.
    exit(E), whole([ins(mov,q,[mem(-8,rbp),reg(rax)])|E], Bad),
    whole([ins(mov,q,[reg(rax),mem(-8,rbp)])|E], Good),
    impl_body(f, Good, _, GoodBody), body_analysis(GoodBody, [-8], GoodA),
    determined([-8-r10], [], Bad, BadAfter),
    (   \+ check_regs(regs_metadata(false,f,Hs,[]), [-8-r10], Bad, BadAfter, GoodA)
    ->  true
    ;   throw(error(regs_checker(other_body, no), regs_checker/0))
    ).

% Proposals that differ from the determined stream.
proposal_cases :-
    homes(Hs), across_call(Body), whole(Body, Before),
    Meta = regs_metadata(false,f,Hs,[save(rbx,-24)]), Map = [-16-r10,-8-rbx],
    determined(Map, [save(rbx,-24)], Before, After),
    % No restore before the leave.
    once(append(Front, [ins(mov,q,[mem(-24,rbp),reg(rbx)])|Back], After)),
    append(Front, Back, NoRestore),
    % r11 where the map says r10.
    once(append(F2, [ins(mov,q,[reg(rax),reg(r10)])|B2], After)),
    append(F2, [ins(mov,q,[reg(rax),reg(r11)])|B2], WrongRegister),
    % A setjmp function admits only identity.
    forall(member(Name-(M-A), [no_restore-(Meta-NoRestore),
                               wrong_register-(Meta-WrongRegister),
                               setjmp-(regs_metadata(true,f,Hs,[])-After)]),
           (   ( M = regs_metadata(true,_,_,_) -> Map1 = [] ; Map1 = Map ),
               (   \+ check_regs(M, Map1, Before, A) -> true
               ;   throw(error(regs_checker(Name, no), regs_checker/0)) ) )).

%% The operand checker (docs/perf.md, step 3b)

% operand_case(Name, A, B, Expected): A is a reference body (3a's stream
% for an empty map), B a proposed operand rewrite of it; Expected says
% whether check_operands/3 must accept it, with liveness computed from A.
operands_checker :-
    forall(operand_case(Name, A0, B0, Expected),
           ( ob(A0, A), ob(B0, B), operand_run(Name, A, B, Expected, same) )),
    forall(operand_raw_case(Name, A, B, Expected),
           operand_run(Name, A, B, Expected, same)),
    forall(operand_live_case(Name, A0, Edit),
           ( ob(A0, A), operand_run(Name, A, A, no, Edit) )),
    saves_case,
    forall(cell_case(Name, Cells, A0, B0, Expected),
           ( ob(A0, A), ob(B0, B), cell_run(Name, Cells, A, B, Expected) )).

% Frame cells (docs/perf.md, 5a-loads): a load of a cell is a move of
% its value, which paired stores set and every boundary resets.
cell_run(Name, Cells, A, B, Expected) :-
    body_analysis(A, [], An), operand_lives(An, [], A, Lives),
    ( check_operands(A, B, Lives, Cells) -> Got = yes ; Got = no ),
    (   Got == Expected -> true
    ;   throw(error(operands_checker(Name, Expected), operands_checker/0))
    ).

cell_case(forwarded_load, cells([-16,-8],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,q,[mem(-8,rbp),reg(rdx)])],
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,q,[reg(r12),reg(rdx)])], yes).
cell_case(not_a_cell, cells([-16],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,q,[mem(-8,rbp),reg(rdx)])],
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,q,[reg(r12),reg(rdx)])], no).
cell_case(stored_in_between, cells([-8],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,q,[reg(r13),mem(-8,rbp)]),
     ins(mov,q,[mem(-8,rbp),reg(rdx)])],
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,q,[reg(r13),mem(-8,rbp)]),
     ins(mov,q,[reg(r12),reg(rdx)])], no).
cell_case(across_call, cells([-8],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(call,none,[sym(f)]),
     ins(mov,q,[mem(-8,rbp),reg(rdx)])],
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(call,none,[sym(f)]),
     ins(mov,q,[reg(r12),reg(rdx)])], no).
cell_case(across_label, cells([-8],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), label(l), ins(mov,q,[mem(-8,rbp),reg(rdx)])],
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), label(l), ins(mov,q,[reg(r12),reg(rdx)])], no).
% A 32-bit store keeps the cell's high half; a 32-bit load zero-extends.
cell_case(movl_store_keeps_high, cells([-8],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,l,[reg(r13d),mem(-8,rbp)]),
     ins(mov,q,[mem(-8,rbp),reg(rdx)])],
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,l,[reg(r13d),mem(-8,rbp)]),
     ins(mov,l,[reg(r13d),reg(edx)])], no).
cell_case(movl_load_after_movl_store, cells([-8],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,l,[reg(r13d),mem(-8,rbp)]),
     ins(mov,l,[mem(-8,rbp),reg(edx)])],
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,l,[reg(r13d),mem(-8,rbp)]),
     ins(mov,l,[reg(r13d),reg(edx)])], yes).
cell_case(byte_store, cells([-8],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,b,[reg(r13b),mem(-8,rbp)]),
     ins(mov,q,[mem(-8,rbp),reg(rdx)])],
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,b,[reg(r13b),mem(-8,rbp)]),
     ins(mov,q,[reg(r12),reg(rdx)])], no).
cell_case(address_taken, cells([-8],[]),
    [ins(lea,q,[mem(-8,rbp),reg(rsi)]),
     ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,q,[mem(-8,rbp),reg(rdx)])],
    [ins(lea,q,[mem(-8,rbp),reg(rsi)]),
     ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mov,q,[reg(r12),reg(rdx)])], no).
cell_case(inside_local, cells([-16],[-32-24]),
    [ins(mov,q,[reg(r12),mem(-16,rbp)])], [ins(mov,q,[reg(r12),mem(-16,rbp)])], no).
cell_case(beside_local, cells([-8],[-32-24]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)])], [ins(mov,q,[reg(r12),mem(-8,rbp)])], yes).
cell_case(unaligned, cells([-12],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)])], [ins(mov,q,[reg(r12),mem(-8,rbp)])], no).
cell_case(duplicate, cells([-8,-8],[]),
    [ins(mov,q,[reg(r12),mem(-8,rbp)])], [ins(mov,q,[reg(r12),mem(-8,rbp)])], no).

% The whole body: a frame, the lines, rax zeroed by a move (xor would
% read it), leave and ret.
ob(Lines, Body) :-
    append([[ins(push,q,[reg(rbp)]), ins(mov,q,[reg(rsp),reg(rbp)])], Lines,
            [ins(mov,l,[imm(0),reg(eax)]), ins(leave,none,[]), ins(ret,none,[])]], Body).

operand_run(Name, A, B, Expected, Edit) :-
    body_analysis(A, [], An), operand_lives(An, [], A, Lives0),
    edit_lives(Edit, A, Lives0, Lives),
    ( check_operands(A, B, Lives) -> Got = yes ; Got = no ),
    (   Got == Expected -> true
    ;   throw(error(operands_checker(Name, Expected), operands_checker/0))
    ).

% edit_lives(+Edit, +A, +Lives0, -Lives): dead(Bit, Label) clears Bit
% after the label, as wrong liveness would.
edit_lives(same, _, Lives, Lives).
edit_lives(dead(Bit, L), A, Lives0, Lives) :-
    maplist(edit_live(Bit, L), A, Lives0, Lives).
edit_live(Bit, L, Line, live(I,O0,E), live(I,O,E)) :-
    ( Line == label(L) -> O is O0 /\ \ (1 << Bit) ; O = O0 ).

r(N, reg(N)).
mv(S, A, B, ins(mov,S,[A,B])).

% Accepted rewrites: a forwarded copy and immediate, a retargeted load
% and two-address result, a forwarded base, a narrowed copy, and a
% setcc into another register whose upper bits nothing reads.
operand_case(forward_copy,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(add,q,[reg(r12),reg(rbx)])], yes).
operand_case(forward_l_copy,
    [ins(mov,l,[reg(r12d),reg(eax)]), ins(add,l,[reg(eax),reg(ebx)])],
    [ins(add,l,[reg(r12d),reg(ebx)])], yes).
operand_case(forward_imm,
    [ins(mov,q,[imm(-1),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(add,q,[imm(-1),reg(rbx)])], yes).
operand_case(shift_count,
    [ins(mov,l,[imm(3),reg(ecx)]), ins(shl,l,[reg(cl),reg(ebx)]), ins(mov,l,[imm(0),reg(ecx)])],
    [ins(shl,l,[imm(3),reg(ebx)]), ins(mov,l,[imm(0),reg(ecx)])], yes).
operand_case(retarget_load,
    [ins(mov,q,[mem(-8,rbp),reg(rax)]), ins(mov,q,[reg(rax),reg(rbx)])],
    [ins(mov,q,[mem(-8,rbp),reg(rbx)])], yes).
operand_case(two_address,
    [ins(mov,q,[reg(rbx),reg(rax)]), ins(sub,q,[reg(r12),reg(rax)]), ins(mov,q,[reg(rax),reg(rbx)])],
    [ins(sub,q,[reg(r12),reg(rbx)])], yes).
operand_case(forward_base,
    [ins(mov,q,[reg(r12),reg(rcx)]), ins(mov,q,[mem(8,rcx),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)]),
     ins(mov,l,[imm(0),reg(ecx)])],
    [ins(mov,q,[mem(8,r12),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)]), ins(mov,l,[imm(0),reg(ecx)])], yes).
operand_case(setcc_elsewhere,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(cmp,q,[imm(0),reg(rbx)]), ins(sete,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)]), ins(mov,l,[imm(0),reg(ecx)])],
    [ins(cmp,q,[imm(0),reg(rbx)]), ins(sete,none,[reg(cl)]),
     ins(movzb,l,[reg(cl),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)]), ins(mov,l,[imm(0),reg(ecx)])], yes).
% lock cmpxchg: New may be forwarded; %rax is read (Expected) and
% written (the old value) implicitly, so neither move of it can go.
operand_case(cmpxchg_forward_new,
    [ins(mov,q,[reg(r12),reg(rcx)]), ins('lock cmpxchg',q,[reg(rcx),mem(0,rdx)]),
     ins(mov,l,[imm(0),reg(ecx)])],
    [ins('lock cmpxchg',q,[reg(r12),mem(0,rdx)]), ins(mov,l,[imm(0),reg(ecx)])], yes).
operand_case(cmpxchg_drops_expected,
    [ins(mov,q,[reg(r12),reg(rax)]), ins('lock cmpxchg',q,[reg(rcx),mem(0,rdx)]),
     ins(mov,q,[reg(rax),reg(rbx)])],
    [ins('lock cmpxchg',q,[reg(rcx),mem(0,rdx)]), ins(mov,q,[reg(rax),reg(rbx)])], no).
operand_case(cmpxchg_forwards_old_rax,
    [ins(mov,q,[reg(r12),reg(rax)]), ins('lock cmpxchg',q,[reg(rcx),mem(0,rdx)]),
     ins(mov,q,[reg(rax),reg(rbx)])],
    [ins(mov,q,[reg(r12),reg(rax)]), ins('lock cmpxchg',q,[reg(rcx),mem(0,rdx)]),
     ins(mov,q,[reg(r12),reg(rbx)])], no).
% A forwarded read of a register redefined in between.
operand_case(redefined_source,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(mov,q,[imm(5),reg(r12)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(mov,q,[imm(5),reg(r12)]), ins(add,q,[reg(r12),reg(rbx)])], no).
% A movl copy used at 64 bits.
operand_case(l_copy_at_q,
    [ins(mov,l,[reg(r12d),reg(eax)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(add,q,[reg(r12),reg(rbx)])], no).
% Swapped sub operands.
operand_case(swapped_sub,
    [ins(mov,q,[reg(rbx),reg(rax)]), ins(sub,q,[reg(r12),reg(rax)]), ins(mov,q,[reg(rax),reg(rbx)])],
    [ins(mov,q,[reg(r12),reg(rax)]), ins(sub,q,[reg(rbx),reg(rax)]), ins(mov,q,[reg(rax),reg(rbx)])], no).
% A different displacement, and a different base value.
operand_case(displacement,
    [ins(mov,q,[mem(-8,rbp),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(mov,q,[mem(-16,rbp),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])], no).
operand_case(base_value,
    [ins(mov,q,[reg(r12),reg(rcx)]), ins(mov,q,[mem(8,rcx),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)]),
     ins(mov,l,[imm(0),reg(ecx)])],
    [ins(mov,q,[mem(8,r13),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)]), ins(mov,l,[imm(0),reg(ecx)])], no).
% A deleted and an added memory access.
operand_case(deleted_access,
    [ins(mov,q,[mem(-8,rbp),reg(rax)]), ins(mov,q,[reg(rax),reg(rbx)])],
    [ins(mov,q,[reg(rax),reg(rbx)])], no).
operand_case(added_access,
    [ins(mov,q,[reg(r12),reg(rbx)])],
    [ins(mov,q,[mem(-8,rbp),reg(rcx)]), ins(mov,q,[reg(r12),reg(rbx)])], no).
% A live scratch register left different: into a fail block, into a call
% (which uses every scratch register), and at ret (rdx, rcx).
operand_case(into_fail_block,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(cmp,q,[imm(0),reg(rbx)]), ins(je,none,[sym(fail)]),
     ins(mov,l,[imm(0),reg(eax)]), ins(leave,none,[]), ins(ret,none,[]),
     label(fail), ins(mov,q,[reg(rax),mem(-8,rbp)]), ins(ud2,none,[])],
    [ins(cmp,q,[imm(0),reg(rbx)]), ins(je,none,[sym(fail)]),
     ins(mov,l,[imm(0),reg(eax)]), ins(leave,none,[]), ins(ret,none,[]),
     label(fail), ins(mov,q,[reg(rax),mem(-8,rbp)]), ins(ud2,none,[])], no).
operand_case(into_call,
    [ins(mov,q,[reg(r12),reg(rcx)]), ins(call,none,[sym(f)])],
    [ins(call,none,[sym(f)])], no).
operand_case(at_ret,
    [ins(mov,q,[reg(r12),reg(rdx)])],
    [], no).
% A two-word result's second word returns in rcx.
operand_case(at_ret_rcx,
    [ins(mov,q,[reg(r12),reg(rcx)])],
    [], no).
% A home register different at a label.
operand_case(home_at_label,
    [ins(mov,q,[reg(r12),reg(rbx)]), label(m)],
    [label(m)], no).
% Immediates: outside imm32 for q, and 0xffffffff for -1 at 64 bits.
operand_case(q_imm_range,
    [ins(movabs,q,[imm(0x100000000),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(add,q,[imm(0x100000000),reg(rbx)])], no).
operand_case(ffffffff_for_minus_one,
    [ins(mov,l,[imm(0xffffffff),reg(eax)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(add,q,[imm(-1),reg(rbx)])], no).
operand_case(movq_ffffffff,
    [ins(mov,q,[imm(-1),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(mov,q,[imm(0xffffffff),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])], no).
% Boundary identity: a retargeted stack adjustment, a different jcc target.
operand_case(retargeted_rsp,
    [ins(mov,q,[imm(16),reg(rax)]), ins(sub,q,[reg(rax),reg(rsp)])],
    [ins(sub,q,[imm(16),reg(rsp)])], no).
operand_case(rsp_amount,
    [ins(sub,q,[imm(16),reg(rsp)])],
    [ins(sub,q,[imm(32),reg(rsp)])], no).
operand_case(jcc_target,
    [ins(cmp,q,[imm(0),reg(rbx)]), ins(je,none,[sym(l1)]), label(l1), label(l2)],
    [ins(cmp,q,[imm(0),reg(rbx)]), ins(je,none,[sym(l2)]), label(l1), label(l2)], no).
% A register operand swapped for a memory operand.
operand_case(reg_for_mem,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(add,q,[mem(-8,rbp),reg(rbx)])], no).
% %ah has no audited effects.
operand_case(high_byte,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(mov,b,[reg(al),mem(-1,rbp)])],
    [ins(mov,q,[reg(r12),reg(rax)]), ins(mov,b,[reg(ah),mem(-1,rbp)])], no).
% An 8-bit write merged over different upper bits.
operand_case(merge_upper,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(cmp,q,[imm(0),reg(rbx)]), ins(sete,none,[reg(al)]),
     ins(mov,q,[reg(rax),reg(r13)])],
    [ins(mov,q,[reg(r14),reg(rax)]), ins(cmp,q,[imm(0),reg(rbx)]), ins(sete,none,[reg(al)]),
     ins(mov,q,[reg(rax),reg(r13)])], no).
operand_case(merge_upper_low,
    [ins(mov,l,[reg(r12d),reg(eax)]), ins(cmp,q,[imm(0),reg(rbx)]), ins(sete,none,[reg(al)]),
     ins(mov,q,[reg(rax),reg(r13)])],
    [ins(mov,l,[reg(r14d),reg(eax)]), ins(cmp,q,[imm(0),reg(rbx)]), ins(sete,none,[reg(al)]),
     ins(mov,q,[reg(rax),reg(r13)])], no).
% A two-address destination is a source too.
operand_case(two_address_source,
    [ins(mov,q,[reg(rbx),reg(rax)]), ins(add,q,[reg(r12),reg(rax)]), ins(mov,q,[reg(rax),reg(rbx)])],
    [ins(mov,q,[reg(r13),reg(rax)]), ins(add,q,[reg(r12),reg(rax)]), ins(mov,q,[reg(rax),reg(rbx)])], no).
% A form the contract does not audit (an immediate as cmp's second
% operand) on equal values.
operand_case(unaudited_form,
    [ins(mov,q,[imm(5),reg(rax)]), ins(cmp,q,[reg(rbx),reg(rax)]), ins(sete,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])],
    [ins(cmp,q,[reg(rbx),imm(5)]), ins(sete,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])], no).
% An implicit operand (idiv's rax) different.
operand_case(implicit_operand,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(mov,q,[imm(0),reg(rdx)]), ins(idiv,q,[reg(rbx)]),
     ins(mov,q,[reg(rax),reg(r13)])],
    [ins(mov,q,[reg(r14),reg(rax)]), ins(mov,q,[imm(0),reg(rdx)]), ins(idiv,q,[reg(rbx)]),
     ins(mov,q,[reg(rax),reg(r13)])], no).
% movl for movq into rdi before a call.
operand_case(movl_argument,
    [ins(mov,q,[reg(r12),reg(rdi)]), ins(call,none,[sym(f)])],
    [ins(mov,l,[reg(r12d),reg(edi)]), ins(call,none,[sym(f)])], no).

% A div's flags are distinct per stream; a later shift by %cl (whose zero
% count would keep them) does not make them live at the jump between.
operand_case(div_then_shift,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(cqto,none,[]), ins(idiv,q,[reg(rbx)]),
     ins(mov,q,[reg(rax),reg(r13)]), ins(jmp,none,[sym(l)]), label(l),
     ins(mov,l,[imm(0),reg(edx)]), ins(shl,l,[reg(cl),reg(r13d)])],
    [ins(mov,q,[reg(r12),reg(rax)]), ins(cqto,none,[]), ins(idiv,q,[reg(rbx)]),
     ins(mov,q,[reg(rax),reg(r13)]), ins(jmp,none,[sym(l)]), label(l),
     ins(mov,l,[imm(0),reg(edx)]), ins(shl,l,[reg(cl),reg(r13d)])], yes).
% A shift on flags that differ (dead at the label) keeps them different
% for a zero count, so a read after it rejects even identical streams.
operand_case(shift_keeps_flags,
    [label(l), ins(shl,l,[reg(cl),reg(ebx)]), ins(sete,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])],
    [label(l), ins(shl,l,[reg(cl),reg(ebx)]), ins(sete,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])], no).

% Control: a call falls through, so the region after it is compared; a
% label after unreachable lines is reached, so the state is live again;
% a jmp compares what is live into its target; unreachable lines pair by
% mnemonic.
operand_case(after_call,
    [ins(call,none,[sym(f)]), ins(mov,q,[reg(r12),reg(rdx)])],
    [ins(call,none,[sym(f)])], no).
operand_case(after_unreachable_label,
    [ins(jmp,none,[sym(l)]), label(l), ins(mov,q,[reg(r12),reg(rdx)])],
    [ins(jmp,none,[sym(l)]), label(l)], no).
operand_case(live_into_jmp,
    [ins(mov,q,[reg(r12),reg(rdx)]), ins(jmp,none,[sym(l)]), label(l)],
    [ins(jmp,none,[sym(l)]), label(l)], no).
operand_case(unreachable_mnemonic,
    [ins(jmp,none,[sym(l)]), ins(add,q,[reg(r12),reg(rbx)]), label(l)],
    [ins(jmp,none,[sym(l)]), ins(sub,q,[reg(r12),reg(rbx)]), label(l)], no).
% The stack-overflow jump uses every scratch register.
operand_case(stack_check_uses,
    [ins(mov,q,[reg(r12),reg(rsi)]), ins(cmp,q,[reg(rsp),mem(0,rdi)]),
     ins(jae,none,[plt(filc_stack_overflow_failure)]), ins(mov,l,[imm(0),reg(esi)])],
    [ins(cmp,q,[reg(rsp),mem(0,rdi)]),
     ins(jae,none,[plt(filc_stack_overflow_failure)]), ins(mov,l,[imm(0),reg(esi)])], no).
% Indexed memory: the index register's value and the displacement.
operand_case(index_value,
    [ins(mov,q,[reg(r12),reg(rcx)]), ins(mov,q,[mem(8,rbx,rcx),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)]),
     ins(mov,l,[imm(0),reg(ecx)])],
    [ins(mov,q,[mem(8,rbx,r13),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)]), ins(mov,l,[imm(0),reg(ecx)])], no).
operand_case(index_displacement,
    [ins(mov,q,[mem(8,rbx,r12),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(mov,q,[mem(16,rbx,r12),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])], no).
% An XMM destination retargeted leaves the original XMM register
% different at the boundary.
operand_case(xmm_retarget,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(movq,none,[reg(rax),reg(xmm0)])],
    [ins(mov,q,[reg(r12),reg(rax)]), ins(movq,none,[reg(rax),reg(xmm1)])], no).
% Implicit reads: div's rdx and cltd's eax.
operand_case(div_reads_rdx,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(mov,q,[reg(r13),reg(rdx)]), ins(idiv,q,[reg(rbx)]),
     ins(mov,q,[reg(rax),reg(r14)]), ins(mov,l,[imm(0),reg(edx)])],
    [ins(mov,q,[reg(r12),reg(rax)]), ins(mov,q,[reg(r15),reg(rdx)]), ins(idiv,q,[reg(rbx)]),
     ins(mov,q,[reg(rax),reg(r14)]), ins(mov,l,[imm(0),reg(edx)])], no).
operand_case(cltd_reads_eax,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(cltd,none,[]), ins(mov,q,[reg(rdx),reg(r14)]),
     ins(mov,l,[imm(0),reg(edx)])],
    [ins(mov,q,[reg(r13),reg(rax)]), ins(cltd,none,[]), ins(mov,q,[reg(rdx),reg(r14)]),
     ins(mov,l,[imm(0),reg(edx)])], no).
% Flags live at a boundary are compared there: imul's undefined flags
% read after a jump reject even identical streams.
operand_case(flags_at_boundary,
    [ins(imul,q,[reg(r12),reg(rbx)]), ins(jmp,none,[sym(l)]), label(l), ins(sets,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])],
    [ins(imul,q,[reg(r12),reg(rbx)]), ins(jmp,none,[sym(l)]), label(l), ins(sets,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])], no).
% SSE arithmetic preserves the flags: it neither launders imul's
% undefined flags nor spoils a compare's.
operand_case(sse_keeps_undefined,
    [ins(imul,q,[reg(r12),reg(rbx)]), ins(add,sd,[reg(xmm1),reg(xmm0)]), ins(sets,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])],
    [ins(imul,q,[reg(r12),reg(rbx)]), ins(add,sd,[reg(xmm1),reg(xmm0)]), ins(sets,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])], no).
operand_case(sse_keeps_defined,
    [ins(cmp,q,[reg(r12),reg(rbx)]), ins(div,sd,[reg(xmm1),reg(xmm0)]), ins(sete,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])],
    [ins(cmp,q,[reg(r12),reg(rbx)]), ins(div,sd,[reg(xmm1),reg(xmm0)]), ins(sete,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])], yes).

% A fence pairs with itself; a copy forwarded across it is accepted, a
% fence moved past a store is not.
operand_case(across_fence,
    [ins(mov,q,[reg(r12),reg(rax)]), ins(mfence,none,[]), ins(add,q,[reg(rax),reg(rbx)])],
    [ins(mfence,none,[]), ins(add,q,[reg(r12),reg(rbx)])], yes).
operand_case(fence_moved,
    [ins(mov,q,[reg(r12),mem(-8,rbp)]), ins(mfence,none,[])],
    [ins(mfence,none,[]), ins(mov,q,[reg(r12),mem(-8,rbp)])], no).

% Whole bodies: ret uses rax (ob/2 would write it first).
operand_raw_case(ret_uses_rax,
    [ins(push,q,[reg(rbp)]), ins(mov,q,[reg(rsp),reg(rbp)]), ins(mov,q,[reg(r12),reg(rax)]),
     ins(leave,none,[]), ins(ret,none,[])],
    [ins(push,q,[reg(rbp)]), ins(mov,q,[reg(rsp),reg(rbp)]),
     ins(leave,none,[]), ins(ret,none,[])], no).

% 3a's save and restore lines in A, which the reference's liveness does
% not have: operand_lives/4 must align them, and a rewrite around them is
% accepted.
saves_case :-
    ob([ins(mov,q,[reg(r12),reg(rax)]), ins(add,q,[reg(rax),reg(r13)])], R),
    Save = ins(mov,q,[reg(rbx),mem(-8,rbp)]), Restore = ins(mov,q,[mem(-8,rbp),reg(rbx)]),
    R = [P1,P2|Rest], append(Mid, [Leave,Ret], Rest),
    append([[P1,P2,Save], Mid, [Restore,Leave,Ret]], A),
    append([[P1,P2,Save], [ins(add,q,[reg(r12),reg(r13)]), ins(mov,l,[imm(0),reg(eax)])],
            [Restore,Leave,Ret]], B),
    body_analysis(R, [], An),
    (   operand_lives(An, [save(rbx,-8)], A, Lives), check_operands(A, B, Lives) -> true
    ;   throw(error(operands_checker(saves, yes), operands_checker/0))
    ).

% Identical streams under wrong liveness: a register read after a region
% start where it is said dead, and the flags likewise (both start
% distinct per stream, so the reads differ).
operand_live_case(dead_register,
    [label(m), ins(mov,q,[reg(r8),reg(rax)]), ins(add,q,[reg(rax),reg(rbx)])], dead(5, m)).
operand_live_case(dead_flags,
    [ins(cmp,q,[imm(0),reg(rbx)]), label(m), ins(sete,none,[reg(al)]),
     ins(movzb,l,[reg(al),reg(eax)]), ins(mov,q,[reg(rax),reg(r13)])], dead(7, m)).
