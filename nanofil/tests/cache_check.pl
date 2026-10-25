/* Hand-authored translation-validation tests, independent of allocation.
   Every ordinary fixture's original forms must be known to the machine
   contract, so an accidental whole-function fallback cannot make a
   negative symbolic test pass. Fallbacks have their own separate tests. */
:- module(cache_check_tests, [cache_checker/0]).

:- use_module('../src/amd64_cache_check').
:- use_module('../src/amd64_contract', [instruction_effects/2]).
:- use_module(library(lists)).
:- discontiguous(checker_case/5).

cache_checker :-
    forall(checker_case(Name, Homes, Before, After, Expected),
           run_case(Name, Homes, Before, After, Expected)),
    fallback_cases,
    setjmp_case,
    semidet_case,
    frame_cases.

run_case(Name, Homes, Before, After, Expected) :-
    framed(Before, WholeBefore), framed(After, WholeAfter),
    (   maplist(known_line, WholeBefore),
        check_cache(cache_metadata(false,Homes), WholeBefore, WholeBefore),
        expectation(Expected, cache_metadata(false,Homes),
                    WholeBefore, WholeAfter)
    ->  true
    ;   throw(error(cache_checker(Name,Expected), cache_checker/0))
    ).

known_line(Line) :- once(instruction_effects(Line, _)).
expectation(yes, Metadata, Before, After) :-
    check_cache(Metadata, Before, After).
expectation(no, Metadata, Before, After) :-
    \+ check_cache(Metadata, Before, After).

% Fixtures below are instruction bodies; the public checker gets the
% original function's frame setup, not an implicit assumption of one.
framed(Body, [ins(push,q,[reg(rbp)]),
              ins(mov,q,[reg(rsp),reg(rbp)])|Body]).

checker_case(empty, [], [], [], yes).
checker_case(reads_both_widths, [home(-8,[w,l])], [
    ins(mov,q,[mem(-8,rbp),reg(rax)]),
    ins(mov,l,[mem(-8,rbp),reg(ecx)]),
    ins(mov,q,[mem(-8,rbp),reg(rdx)])
], [
    ins(mov,q,[mem(-8,rbp),reg(r10)]),
    ins(mov,q,[reg(r10),reg(rax)]),
    ins(mov,l,[reg(r10d),reg(ecx)]),
    ins(mov,q,[reg(r10),reg(rdx)])
], yes).

% The third interval stays in memory, without forcing either cache out.
checker_case(two_registers_and_stack, Homes, [
    ins(mov,q,[reg(rdi),mem(-8,rbp)]),
    ins(mov,q,[reg(rsi),mem(-16,rbp)]),
    ins(mov,q,[reg(rdx),mem(-24,rbp)]),
    ins(mov,l,[mem(-8,rbp),reg(eax)]),
    ins(mov,q,[mem(-16,rbp),reg(rcx)]),
    ins(mov,q,[mem(-24,rbp),reg(rdx)])
], [
    ins(mov,q,[reg(rdi),reg(r10)]),
    ins(mov,q,[reg(rsi),reg(r11)]),
    ins(mov,q,[reg(rdx),mem(-24,rbp)]),
    ins(mov,l,[reg(r10d),reg(eax)]),
    ins(mov,q,[reg(r11),reg(rcx)]),
    ins(mov,q,[mem(-24,rbp),reg(rdx)]),
    ins(mov,q,[reg(r10),mem(-8,rbp)]),
    ins(mov,q,[reg(r11),mem(-16,rbp)])
], yes) :-
    Homes = [home(-8,[w,l,w]),home(-16,[l]),home(-24,[w])].

checker_case(ordinary_write_preserves_cache, [home(-8,[l])], [
    ins(mov,q,[reg(rax),mem(-8,rbp)]),
    ins(add,q,[imm(1),reg(rax)]),
    ins(mov,q,[mem(-8,rbp),reg(rdx)])
], [
    ins(mov,q,[reg(rax),reg(r10)]),
    ins(add,q,[imm(1),reg(rax)]),
    ins(mov,q,[reg(r10),reg(rdx)]),
    ins(mov,q,[reg(r10),mem(-8,rbp)])
], yes).

checker_case(refresh_after_arithmetic, [home(-8,[w])], [
    ins(mov,q,[reg(rax),mem(-8,rbp)]),
    ins(add,l,[imm(1),reg(eax)]),
    ins(mov,q,[reg(rax),mem(-8,rbp)]),
    ins(mov,l,[mem(-8,rbp),reg(edx)])
], [
    ins(mov,q,[reg(rax),reg(r11)]),
    ins(add,l,[imm(1),reg(eax)]),
    ins(mov,q,[reg(rax),reg(r11)]),
    ins(mov,l,[reg(r11d),reg(edx)]),
    ins(mov,q,[reg(r11),mem(-8,rbp)])
], yes).

% Explicit, implicit and partial writes must all break the old register
% equality. A cache containing the pre-instruction value is not its result.
checker_case(opaque_write(Name,Bank), Homes, Before, After, Expected) :-
    opaque_fixture(Name, Register, Instruction),
    member(Bank-Expected, [r11-yes,r10-no]),
    Homes = [home(-8,[l]),home(-16,[l])],
    Before = [ins(mov,q,[reg(Register),mem(-8,rbp)]), Instruction,
              ins(mov,q,[reg(Register),mem(-16,rbp)]),
              ins(mov,q,[mem(-16,rbp),reg(rdi)])],
    After = [ins(mov,q,[reg(Register),reg(r10)]), Instruction,
             ins(mov,q,[reg(Register),reg(r11)]),
             ins(mov,q,[reg(Bank),reg(rdi)]),
             ins(mov,q,[reg(r10),mem(-8,rbp)]),
             ins(mov,q,[reg(r11),mem(-16,rbp)])].

opaque_fixture(quotient, rax, ins(idiv,q,[reg(rcx)])).
opaque_fixture(remainder, rdx, ins(idiv,q,[reg(rcx)])).
opaque_fixture(sign_extension, rdx, ins(cqto,none,[])).
opaque_fixture(word_sign_extension, rdx, ins(cltd,none,[])).
opaque_fixture(low_byte, rax, ins(setne,none,[reg(al)])).
opaque_fixture(low_word, rax, ins(mov,w,[imm(7),reg(ax)])).
opaque_fixture(from_sse, rax, ins(movq,none,[reg(xmm0),reg(rax)])).

% This is intentionally unlike the allocator's no-eviction policy: the
% checker validates values, not its implementation's register decisions.
checker_case(reuse_after_spill, [home(-8,[l]),home(-16,[l])], [
    ins(mov,q,[reg(rax),mem(-8,rbp)]),
    ins(mov,q,[reg(rcx),mem(-16,rbp)]),
    ins(mov,q,[mem(-8,rbp),reg(rdx)])
], [
    ins(mov,q,[reg(rax),reg(r10)]),
    ins(mov,q,[reg(r10),mem(-8,rbp)]),
    ins(mov,q,[reg(rcx),reg(r10)]),
    ins(mov,q,[reg(r10),mem(-16,rbp)]),
    ins(mov,q,[mem(-8,rbp),reg(r10)]),
    ins(mov,q,[reg(r10),reg(rdx)])
], yes).

% Think of incoming rdi as 0x1234567800000001. The low-word load yields
% rax=1, but the original home (and r10) must retain 0x12345678 above it.
% Both cache registers have the SAME low symbol: only high-half tracking
% can distinguish them in these otherwise well-formed qword moves.
checker_case(high_bits(ReadBank,SpillBank), Homes, Before, After, Expected) :-
    member(choice(ReadBank,SpillBank,Expected),
           [choice(r10,r10,yes),choice(r11,r10,no),choice(r10,r11,no)]),
    Homes = [home(-8,[w,l]),home(-16,[w])],
    Before = [ins(mov,q,[reg(rdi),mem(-8,rbp)]),
              ins(mov,l,[mem(-8,rbp),reg(eax)]),
              ins(mov,q,[reg(rax),mem(-16,rbp)]),
              ins(mov,q,[mem(-8,rbp),reg(rcx)])],
    After = [ins(mov,q,[reg(rdi),reg(r10)]),
             ins(mov,l,[reg(r10d),reg(eax)]),
             ins(mov,q,[reg(rax),reg(r11)]),
             ins(mov,q,[reg(ReadBank),reg(rcx)]),
             ins(mov,q,[reg(SpillBank),mem(-8,rbp)]),
             ins(mov,q,[reg(r11),mem(-16,rbp)])].

checker_case(wrong_load_width, [home(-8,[l])], [
    ins(mov,q,[mem(-8,rbp),reg(rax)])
], [
    ins(mov,q,[mem(-8,rbp),reg(r10)]),
    ins(mov,l,[reg(r10d),reg(eax)])
], no).
checker_case(widened_word_load, [home(-8,[w])], [
    ins(mov,l,[mem(-8,rbp),reg(eax)])
], [
    ins(mov,q,[mem(-8,rbp),reg(r10)]),
    ins(mov,q,[reg(r10),reg(rax)])
], no).
checker_case(truncated_fill, [home(-8,[w])], [
    ins(mov,l,[mem(-8,rbp),reg(eax)])
], [
    ins(mov,l,[mem(-8,rbp),reg(r10d)]),
    ins(mov,l,[reg(r10d),reg(eax)])
], no).
checker_case(truncated_store, [home(-8,[w])], [
    ins(mov,q,[reg(rax),mem(-8,rbp)])
], [
    ins(mov,l,[reg(eax),reg(r10d)]),
    ins(mov,q,[reg(r10),mem(-8,rbp)])
], no).
checker_case(truncated_spill, [home(-8,[w])], [
    ins(mov,q,[reg(rax),mem(-8,rbp)])
], [
    ins(mov,q,[reg(rax),reg(r10)]),
    ins(mov,l,[reg(r10d),mem(-8,rbp)])
], no).

checker_case(stale_after_normal_overwrite(Tail), [home(-8,[l])], Before,
             After, no) :-
    member(Tail, [ins(mov,q,[reg(r10),mem(-8,rbp)]),
                  ins(mov,q,[reg(r10),reg(rdx)])]),
    Prefix = [ins(mov,q,[mem(-8,rbp),reg(rax)]),
              ins(mov,q,[reg(rcx),mem(-8,rbp)])],
    ( Tail = ins(mov,q,[_,reg(rdx)])
    -> append(Prefix,[ins(mov,q,[mem(-8,rbp),reg(rdx)])],Before)
    ; Before = Prefix ),
    After = [ins(mov,q,[mem(-8,rbp),reg(r10)]),
             ins(mov,q,[reg(r10),reg(rax)]),
             ins(mov,q,[reg(rcx),mem(-8,rbp)]), Tail].

checker_case(dirty_unchanged_load, [home(-8,[l])], [
    ins(mov,q,[reg(rax),mem(-8,rbp)]),
    ins(mov,q,[mem(-8,rbp),reg(rcx)])
], [
    ins(mov,q,[reg(rax),reg(r10)]),
    ins(mov,q,[mem(-8,rbp),reg(rcx)]),
    ins(mov,q,[reg(r10),mem(-8,rbp)])
], no).

% Flush must precede EACH boundary, never merely the end of the stream.
checker_case(boundary(Name,Placement), [home(-8,[l])], [Store,Line],
             After, Expected) :-
    boundary_fixture(Name, Line),
    Store = ins(mov,q,[reg(rax),mem(-8,rbp)]),
    Cached = ins(mov,q,[reg(rax),reg(r10)]),
    Spill = ins(mov,q,[reg(r10),mem(-8,rbp)]),
    member(placement(Placement,After,Expected),
           [placement(before,[Cached,Spill,Line],yes),
            placement(missing,[Cached,Line],no),
            placement(after,[Cached,Line,Spill],no)]).

boundary_fixture(branch, ins(jnz,none,[sym(failure)])).
boundary_fixture(jump, ins(jmp,none,[sym(next)])).
boundary_fixture(call, ins(call,none,[plt(filc_pollcheck_slow)])).
boundary_fixture(indirect_call, ins(call,q,[ind(reg(rax))])).
boundary_fixture(label, label(join)).
boundary_fixture(directive, p2align(4)).
boundary_fixture(read_memory, ins(mov,q,[mem(0,rdi),reg(rdx)])).
boundary_fixture(write_memory, ins(mov,q,[reg(rax),mem(0,rdi)])).
boundary_fixture(read_write_memory, ins(add,q,[imm(1),mem(0,rdi)])).
boundary_fixture(partial_home_write, ins(mov,l,[reg(eax),mem(-8,rbp)])).
boundary_fixture(noneligible_home, ins(mov,q,[mem(-16,rbp),reg(rax)])).
boundary_fixture(indexed_home, ins(mov,q,[mem(-8,rbp,rcx),reg(rax)])).
boundary_fixture(stack_write, ins(sub,q,[imm(16),reg(rsp)])).
boundary_fixture(frame_write, ins(mov,q,[reg(rax),reg(rbp)])).
boundary_fixture(word_frame_write, ins(mov,l,[reg(eax),reg(ebp)])).
boundary_fixture(home_to_frame, ins(mov,q,[mem(-8,rbp),reg(rbp)])).
boundary_fixture(push, ins(push,q,[reg(rbx)])).
boundary_fixture(pop, ins(pop,q,[reg(rbx)])).
boundary_fixture(leave, ins(leave,none,[])).
boundary_fixture(return, ins(ret,none,[])).
boundary_fixture(trap, ins(ud2,none,[])).

checker_case(stale_boundary(Name), [home(-8,[l])], [Load,Line,Load], [
    Fill, Read, Line, Read
], no) :-
    boundary_fixture(Name, Line),
    Load = ins(mov,q,[mem(-8,rbp),reg(rax)]),
    Fill = ins(mov,q,[mem(-8,rbp),reg(r11)]),
    Read = ins(mov,q,[reg(r11),reg(rax)]).

checker_case(fresh_after_boundary(Name), [home(-8,[l])], [Load,Line,Load],
             [Fill,Read,Line,Fill,Read], yes) :-
    member(Name, [call,label,branch,read_memory]),
    boundary_fixture(Name, Line),
    Load = ins(mov,q,[mem(-8,rbp),reg(rax)]),
    Fill = ins(mov,q,[mem(-8,rbp),reg(r11)]),
    Read = ins(mov,q,[reg(r11),reg(rax)]).

checker_case(fill_spill_after_leave, [home(-8,[l])], [Leave,Ret], [
    Leave, ins(mov,q,[mem(-8,rbp),reg(r10)]),
    ins(mov,q,[reg(r10),mem(-8,rbp)]), Ret
], no) :- Leave = ins(leave,none,[]), Ret = ins(ret,none,[]).

checker_case(flush_preserves_live_flags, [home(-8,[l])], [Store,Test,Jump],
             [Cached,Test,Spill,Jump], yes) :-
    Store = ins(mov,q,[reg(rax),mem(-8,rbp)]),
    Cached = ins(mov,q,[reg(rax),reg(r10)]),
    Spill = ins(mov,q,[reg(r10),mem(-8,rbp)]),
    Test = ins(test,q,[reg(rdx),reg(rdx)]),
    Jump = ins(jnz,none,[sym(exception)]).

checker_case(skeleton(Name), [], [Original], [Changed], no) :-
    skeleton_change(Name, Original, Changed).
skeleton_change(failure_register,
    ins(mov,q,[reg(rax),reg(rdi)]), ins(mov,q,[reg(rax),reg(rsi)])).
skeleton_change(flags,
    ins(test,q,[reg(rax),reg(rax)]), ins(cmp,q,[reg(rax),reg(rax)])).
skeleton_change(exception_branch,
    ins(jnz,none,[sym(exception)]), ins(jz,none,[sym(exception)])).
skeleton_change(exception_target,
    ins(jnz,none,[sym(exception)]), ins(jnz,none,[sym(success)])).
skeleton_change(call,
    ins(call,none,[plt(failure)]), ins(call,none,[plt(success)])).
skeleton_change(label, label(exception), label(success)).

checker_case(deleted_original, [home(-8,[l])], [
    ins(mov,q,[mem(-8,rbp),reg(rax)])
], [], no).
checker_case(arithmetic_rewrite, [home(-8,[l])], [
    ins(mov,q,[mem(-8,rbp),reg(rax)]),
    ins(add,q,[imm(1),reg(rax)])
], [
    ins(mov,q,[mem(-8,rbp),reg(r10)]),
    ins(add,q,[imm(1),reg(r10)]),
    ins(mov,q,[reg(r10),reg(rax)])
], no).
checker_case(extra_ordinary_move, [], [], [
    ins(mov,q,[reg(rax),reg(rcx)])
], no).
checker_case(unknown_candidate, [], [], [ins(unknown,q,[])], no).
checker_case(uninitialized_cache, [home(-8,[l])], [
    ins(mov,q,[mem(-8,rbp),reg(rax)])
], [ins(mov,q,[reg(r10),reg(rax)])], no).
checker_case(missing_final_writeback, [home(-8,[l])], [
    ins(mov,q,[reg(rax),mem(-8,rbp)])
], [ins(mov,q,[reg(rax),reg(r10)])], no).

checker_case(noneligible(Classes), [home(-8,Classes)], [Load], [Fill,Read],
             no) :-
    member(Classes, [[w,s],[s,w],[l,d],[p],[unknown],[w,unknown],[]]),
    Load = ins(mov,q,[mem(-8,rbp),reg(rax)]),
    Fill = ins(mov,q,[mem(-8,rbp),reg(r10)]),
    Read = ins(mov,q,[reg(r10),reg(rax)]).
checker_case(unlisted_home, [], [Load], [Fill,Read], no) :-
    Load = ins(mov,q,[mem(-8,rbp),reg(rax)]),
    Fill = ins(mov,q,[mem(-8,rbp),reg(r10)]),
    Read = ins(mov,q,[reg(r10),reg(rax)]).
checker_case(noneligible_extra, [home(-8,[l]),home(-16,[l,d])], [], [
    ins(mov,q,[mem(-16,rbp),reg(r11)])
], no).

fallback_cases :-
    forall(fallback_line(Name,Line), fallback_case(Name,Line)).

fallback_case(Name, Line) :-
    M = cache_metadata(false,[home(-8,[l])]),
    Store = ins(mov,q,[reg(rax),mem(-8,rbp)]),
    % Put the unsupported form in an unreachable tail: preflight is whole
    % function, not merely reachable code or the current region.
    framed([Store,ins(ud2,none,[]),label(dead),Line], Before),
    framed([ins(mov,q,[reg(rax),reg(r10)]),
            ins(mov,q,[reg(r10),mem(-8,rbp)]),
            ins(ud2,none,[]),label(dead),Line], After),
    ( check_cache(M,Before,Before), \+ check_cache(M,Before,After)
    -> true
    ; throw(error(cache_fallback(Name), cache_checker/0)) ).

fallback_line(unknown_opcode, ins(mystery,q,[reg(rax)])).
fallback_line(unknown_directive, cfi_unknown(foo)).
fallback_line(wrong_width_form, ins(mov,q,[reg(eax),reg(ecx)])).
fallback_line(wrong_arity, ins(add,q,[reg(rax)])).
fallback_line(two_memories, ins(mov,q,[mem(-8,rbp),mem(-16,rbp)])).
fallback_line(cache_source, ins(mov,q,[reg(r10),reg(rax)])).
fallback_line(cache_destination, ins(mov,q,[reg(rax),reg(r11)])).
fallback_line(cache_low32, ins(mov,l,[reg(r10d),reg(eax)])).
fallback_line(cache_low16, ins(mov,w,[reg(r11w),reg(ax)])).
fallback_line(cache_low8, ins(mov,b,[reg(r10b),reg(al)])).
fallback_line(cache_address, ins(mov,q,[mem(0,r10),reg(rax)])).
fallback_line(cache_index, ins(lea,q,[mem(0,rax,r11),reg(rdx)])).
fallback_line(cache_indirect, ins(call,none,[ind(mem(0,r10))])).

setjmp_case :-
    % Metadata includes unreachable setjmp sites even when no such call is
    % visible in this slice. The flag alone must disable transformation.
    M = cache_metadata(true,[home(-8,[l])]),
    framed([ins(mov,q,[mem(-8,rbp),reg(rax)])], Before),
    framed([ins(mov,q,[mem(-8,rbp),reg(r10)]),
            ins(mov,q,[reg(r10),reg(rax)])], After),
    check_cache(M,Before,Before),
    \+ check_cache(M,Before,After).

semidet_case :-
    M = cache_metadata(false,[home(-8,[l])]),
    framed([ins(mov,q,[mem(-8,rbp),reg(rax)])], Before),
    framed([ins(mov,q,[mem(-8,rbp),reg(r10)]),
            ins(mov,q,[reg(r10),reg(rax)])], After),
    findall(ok, check_cache(M,Before,After), Answers),
    Answers == [ok].

frame_cases :-
    M = cache_metadata(false,[home(-8,[l])]),
    Fill = ins(mov,q,[mem(-8,rbp),reg(r10)]),
    Spill = ins(mov,q,[reg(r10),mem(-8,rbp)]),
    framed([], Prologue),
    \+ check_cache(M, [], [Fill,Spill]),
    \+ check_cache(M, [label(f)], [label(f),Fill,Spill]),
    append([Fill,Spill], Prologue, TooEarly),
    \+ check_cache(M, Prologue, TooEarly),
    framed([Fill,Spill], Established),
    \+ check_cache(M, Prologue, Established),
    % Establishing rbp does not mean stack growth has been checked. An
    % unrelated fill here could fault instead of reporting stack overflow.
    Push = ins(push,q,[reg(rbp)]),
    Frame = ins(mov,q,[reg(rsp),reg(rbp)]),
    Tail = [ins(sub,q,[imm(8192),reg(rsp)]),
            ins(cmp,q,[reg(rsp),mem(0,rdi)]),
            ins(jae,none,[plt(filc_stack_overflow_failure)]),
            ins(mov,q,[mem(-8192,rbp),reg(rax)]),
            ins(leave,none,[]),ins(ret,none,[])],
    Deep = cache_metadata(false,[home(-8192,[l])]),
    Before = [Push,Frame|Tail],
    After = [Push,Frame,ins(mov,q,[mem(-8192,rbp),reg(r10)])|Tail],
    maplist(known_line, Before),
    check_cache(Deep, Before, Before),
    \+ check_cache(Deep, Before, After).
