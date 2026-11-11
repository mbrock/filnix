(** In Fil-C, a pointer at run time is not a bare 64-bit integer
    address. Instead, every pointer carries an address together with an
    invisible [[capability]] that records which memory object, if any,
    the pointer is allowed to access. This module defines the run-time
    values that [[temporary|temporaries]] hold during execution:
    capabilities [cap], pointers [ptr], and run-time words [word].

    ![[capability]]

    ## Words

    Rather than indexing the type of run-time values by their IR
    [[class]], this module collects all run-time values into a single
    inductive type [word], and checks class compatibility separately.
    An integer word [WInt] holds an integer of class [W] or [L], or the
    bit pattern of a floating-point value.

    Pointer words preserve both an address and the authority to use
    it, including the [[proof]] values produced by successful checks.
    The constructor [WPtr] carries these pointers, while [WLimit]
    carries an opaque [[limit]] snapshot used for bounds comparisons.

    In C, a test harness or caller may occasionally pass a raw integer
    where a pointer parameter is declared. To match the Prolog
    [[interpreter]], [word_at_class] permits an integer word at the
    pointer class so the entry call can begin, and any instruction that
    dereferences or checks that integer as a pointer is then stuck. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope Z_scope.

(** ## Capabilities, pointers, and words

    At run time, every temporary holds a [word], and every pointer word
    pairs an integer address with a [cap]. This section defines those
    types and the functions that coerce a word to a target class or
    read its raw address. *)

(** A [cap] is the [[capability]] that a pointer carries beside its
    integer address to identify which memory object, if any, the pointer
    may access. An object capability records only the object's
    [[identity]]—the base address of its [[region]]—and leaves the
    object's current bounds in memory rather than in the pointer itself. *)
Inductive cap : Type :=
| CNone (* a null or forged pointer with no target object *)
| Obj (base : Z) (* a writable object identified by its base address *)
| Ro (base : Z) (* a read-only object identified by its base address *)
| Fn (f : name) (* a function defined in the current module *)
| External (n : name). (* a symbol defined outside the current module *)

(** The function [cap_eqb] tests whether two capabilities name the same
    object or symbol with the same access rights. *)
Definition cap_eqb (c c' : cap) : bool :=
  match c, c' with
  | CNone, CNone => true
  | Obj b, Obj b' | Ro b, Ro b' => Z.eqb b b'
  | Fn f, Fn f' | External f, External f' => name_eqb f f'
  | _, _ => false
  end.

(** A [ptr] pairs a 64-bit integer address with its [[capability]] as a
    single indivisible value, which is the pair that a [[flight]]
    instruction constructs. *)
Record ptr : Type := mkPtr { ptr_addr : Z; ptr_cap : cap }.

(** A [word] is the run-time value that a [[temporary]] holds during
    execution: an integer or floating-point bit pattern, a pointer or
    checked [[proof]], or an opaque [[limit]] snapshot. *)
Inductive word : Type :=
| WInt (n : Z) (* an integer, or the bit pattern of a floating-point value *)
| WPtr (p : ptr) (* a pointer of class P, or a checked proof of class A or F *)
| WLimit (c : cap) (size : Z). (* an opaque [[limit]] snapshot of a capability and access size *)

(** Given an IR [[class]] and a run-time [word], [word_at_class]
    truncates or checks the word to fit that class. Integer and
    floating-point bit patterns are reduced modulo the bit width of the
    class, pointers and proofs pass through unchanged at classes [P],
    [A], and [F], and a limit snapshot remains valid at class [L]. Any
    other combination is a run-time class mismatch and returns `None`. *)
Definition word_at_class (k : class) (x : word) : option word :=
  match k, x with
  | W, WInt n => Some (WInt (n mod 2 ^ 32))
  | L, WInt n => Some (WInt (n mod 2 ^ 64))
  | L, WLimit _ _ => Some x
  | Single, WInt n => Some (WInt (n mod 2 ^ 32))
  | Double, WInt n => Some (WInt (n mod 2 ^ 64))
  | Extended, WInt n => Some (WInt (n mod 2 ^ 80))
  | (P | A | F), _ => Some x
  | _, _ => None
  end.

(** Given a run-time [word], [pointer_address] extracts the integer
    address from a pointer word or returns a raw integer word directly,
    and returns `None` for a limit snapshot. *)
Definition pointer_address (x : word) : option Z :=
  match x with
  | WPtr p => Some (ptr_addr p)
  | WInt n => Some n
  | WLimit _ _ => None
  end.
