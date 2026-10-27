/* Hand-written fixtures for amd64_regs_check, independent of the
   allocator. Each negative case gives the checker the stream its map
   determines, so only an obligation (or the comparison, where the
   proposal differs) can reject it. */
:- module(regs_check_tests, [regs_checker/0]).

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
