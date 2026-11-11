/** <module> What each instruction does

The effect table the lifter is driven by. A row is the term the Prolog
SaRCAsm prototype gives (experiments/sarcasm-prolog/effects.pl):

    semantics(Action, effects(registers(Reads, Writes), memory(Accesses),
                              Flags, control(Control), may_trap(Traps)))

An instruction the prototype's table covers is looked up there, after
its mnemonic is given the width suffix that table expects. The rows
below add the forms memcmp.s uses and the prototype lacks: byte
registers, a memory source for `xor` and `cmp`, `dec`, `neg` and the
conditional move. The prototype is frozen and is not changed.
*/
:- module(lift_table, [semantics/2]).
:- use_module(library(lists)).
:- use_module('../../sarcasm-prolog/flags').
:- use_module('../../sarcasm-prolog/effects').

%! semantics(+Instruction, -Semantics) is det.
%
%  Semantics is the row for Instruction, an `instruction(Mnemonic,
%  Operands)` of lift_asm:parse_file/2. Registers are `register(Root,
%  Width)` with Width 8 or 64. Beyond the prototype's actions a row may
%  have:
%
%    | `binary(K, memory(Address, Bytes), R)` | a memory source |
%    | `compare(sub, memory(Address, 1), R)` | a byte compare with memory |
%    | `unary(dec, R)`, `unary(neg, R)` | |
%    | `conditional_move(Condition, Source, R)` | |
%
%  and a byte register is written as `write(R, integer, keep_upper)`:
%  the other 56 bits keep their value. `xor` of a register with itself
%  is the row of a move of 0 with the flags of `xor`, since it does not
%  read the register. Throws `error(Reason)` for an instruction outside
%  the table, as the prototype does.
semantics(Instruction, Semantics) :-
    canonical(Instruction, Canonical),
    (   added_action(Canonical, Action)
    ->  added_effects(Action, Effects),
        Semantics0 = semantics(Action, Effects)
    ;   sp_effects:instruction_effects(Canonical, Semantics0)
    ),
    zero_idiom(Semantics0, Semantics),
    (   sub_term(register(R, 32), Semantics)
    ->  throw(error(unsupported_width(register(R, 32))))
    ;   true
    ).

% canonical(+Instruction, -Canonical): the mnemonic with an alias
% resolved and the width suffix of its register operands.
canonical(instruction(M0, Operands), instruction(M, Operands)) :-
    ( alias(M0, M1) -> true ; M1 = M0 ),
    (   sized(M1)
    ->  findall(W, ( member(reg(Name), Operands), register(Name, _, W) ), Ws),
        (   sort(Ws, [W]), suffix(W, S)
        ->  atom_concat(M1, S, M)
        ;   throw(error(operand_widths(M0, Operands)))
        )
    ;   M = M1
    ).

alias(jnz, jne).
alias(jz, je).
alias(cmovnz, cmovne).
alias(cmovz, cmove).

sized(M) :- memberchk(M, [mov, lea, add, xor, or, and, cmp, test, shl, shr, dec, neg, cmovne, cmove]).
suffix(8, b).
suffix(32, l).
suffix(64, q).

register(Name, Root, 8) :- byte_register(Name, Root), !.
register(Name, Root, W) :- sp_effects:alias(Name, Root, W).

byte_register(al, rax).
byte_register(cl, rcx).
byte_register(dl, rdx).
byte_register(sil, rsi).
byte_register(dil, rdi).
byte_register(r8b, r8).
byte_register(r9b, r9).
byte_register(r10b, r10).
byte_register(r11b, r11).

% added_action(+Canonical, -Action): the forms the prototype lacks.
added_action(instruction(movb, [mem(D, B, I, S), reg(R)]), load(A, 1, register(Root, 8))) :-
    byte_register(R, Root), sp_effects:address(mem(D, B, I, S), A).
added_action(instruction(Op, [Source, reg(R)]), binary(K, V, register(Root, W))) :-
    added_binary(Op, K, W), register(R, Root, W), added_source(Source, W, V).
added_action(instruction(cmpb, [mem(D, B, I, S), reg(R)]), compare(sub, memory(A, 1), register(Root, 8))) :-
    byte_register(R, Root), sp_effects:address(mem(D, B, I, S), A).
added_action(instruction(Op, [reg(R)]), unary(K, register(Root, 64))) :-
    memberchk(Op-K, [decq-dec, negq-neg]), register(R, Root, 64).
added_action(instruction(Op, [reg(S), reg(R)]), conditional_move(C, register(Source, 64), register(Root, 64))) :-
    memberchk(Op-C, [cmovneq-ne, cmoveq-e]), register(S, Source, 64), register(R, Root, 64).

added_binary(xorb, xor, 8).
added_binary(orb, or, 8).
added_binary(Op, K, 64) :- sp_effects:binary_opcode(Op, K, 64).

% A byte source is a register or memory; a 64-bit source here is memory,
% since the prototype has the register and immediate ones.
added_source(reg(S), 8, register(Root, 8)) :- byte_register(S, Root).
added_source(mem(D, B, I, S), W, memory(A, Bytes)) :-
    Bytes is W // 8, sp_effects:address(mem(D, B, I, S), A).

added_effects(load(A, 1, R),
    effects(registers(Reads, [Write]),
            memory([access(read, A, 1, alignment(1), ordinary, integer)]),
            Flags, control(next), may_trap([address_overflow, invalid_read]))) :-
    sp_effects:address_reads(A, Reads), integer_write(R, Write),
    sp_effects:preserve_flags(Flags).
added_effects(binary(K, V, R),
    effects(registers([read(R, integer)|Reads], [Write]), memory(Accesses),
            Flags, control(next), may_trap(Traps))) :-
    source_effects(V, Reads, Accesses, Traps), integer_write(R, Write),
    sp_effects:binary_flags(K, Flags).
added_effects(compare(K, V, R),
    effects(registers([read(R, integer)|Reads], []), memory(Accesses),
            Flags, control(next), may_trap(Traps))) :-
    source_effects(V, Reads, Accesses, Traps), sp_effects:binary_flags(K, Flags).
added_effects(unary(K, R),
    effects(registers([read(R, integer)], [Write]), memory([]),
            Flags, control(next), may_trap([]))) :-
    integer_write(R, Write), unary_flags(K, Flags).
added_effects(conditional_move(C, S, R),
    effects(registers([read(R, integer), read(S, integer)], [Write]), memory([]),
            flags(reads(FlagReads), defined([]), cleared([]), undefined([]),
                  preserved([cf, pf, af, zf, sf, of])),
            control(next), may_trap([]))) :-
    integer_write(R, Write), sp_flags:condition_reads(C, FlagReads).

source_effects(register(S, W), [read(register(S, W), integer)], [], []).
source_effects(memory(A, Bytes), Reads,
               [access(read, A, Bytes, alignment(1), ordinary, integer)],
               [address_overflow, invalid_read]) :-
    sp_effects:address_reads(A, Reads).

integer_write(register(R, 8), write(register(R, 8), integer, keep_upper)).
integer_write(register(R, 64), write(register(R, 64), integer, replace)).

% dec leaves the carry flag alone; neg sets the flags of 0 - x.
unary_flags(dec, flags(reads([]), defined([pf, af, zf, sf, of]), cleared([]), undefined([]), preserved([cf]))).
unary_flags(neg, Flags) :- sp_effects:binary_flags(sub, Flags).

zero_idiom(semantics(binary(xor, R, R), effects(registers(_, Writes), M, F, C, T)),
           semantics(move(immediate(0), R), effects(registers([], Writes), M, F, C, T))) :-
    R = register(_, _), !.
zero_idiom(Semantics, Semantics).
