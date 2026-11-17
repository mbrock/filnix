(** Startup runs the deferred constructors through the runner that the
    model appends to the image, `c: zrun_deferred_global_ctors`
    ([StartCtors](../zsys/StartCtors.v)). The runner calls each pointer
    in its table with the saved argc, argv and environ. The image does
    not record the order of the table, so its contract must hold for
    every order. This module states that contract, and
    [StartCtorRunner](StartCtorRunner.v) proves it.

    ## Constructors as parameters

    The table's order is not known when the runner is proved, because the
    starting memory may list the constructors in any order. So the
    contract does not name them. For each name in the table it takes what
    the constructor needs, what it gives back, and the promise that a
    call to it turns the one into the other. The final assembly keeps that
    promise for each real constructor by using its own contract. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic Language.
From Glibc Require Import FileInv OsBlocks OsWorld StartCtors.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** This record holds the runner's flag and table, the saved arguments
    and the table's constructor names and pointers. *)
Record cr_in := {
  cr_fl : Z; cr_flreg : region;     (* the did-run flag *)
  cr_tb : Z; cr_treg : region;      (* the read-only table *)
  cr_dq : dfrac;                    (* the share of the table *)
  cr_argc : Z;
  cr_argv : ptr; cr_avreg : region;
  cr_env : ptr; cr_enreg : region;
  cr_adq : dfrac;                   (* the share of the two arrays' lives *)
  cr_order : list name;             (* the constructors in table order *)
  cr_ptrs : list ptr                (* their pointers in the table *)
}.

Section spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The runner passes the same three arguments to every constructor:
    argc as an integer word and the two arrays as pointers. *)
Definition ctor_args : list arg :=
  [Arg W (Tmp (TAtom "argc")); Arg P (Tmp (TAtom "argv")); Arg P (Tmp (TAtom "environ"))].

(** The runner needs to know what each constructor does when it is called.
    This promise says that calling g through a checked pointer, with the
    runner's arguments evaluating to xs, turns P into Q and then returns
    to the caller. *)
Definition ctor_call_ok (g : name) (xs : list word) (P Q : iProp Σ) : Prop :=
  forall f e ls lab callee rest j p Ψ,
    let args := ctor_args in
    value_x ge e F callee = Some (WPtr p) -> ptr_cap p = Fn g -> function_check_res ge p = Some ok ->
    map_option (arg_x ge e) args = Some xs ->
    ⊢ P -∗ ▷ (Q -∗ WP (ERun (mkFrame f e ls None (Exec lab rest j)) : sexpr) {{ Ψ }}) -∗
      WP (ERun (mkFrame f e ls None (Exec lab (RawCall CVoid callee args :: rest) j)) : sexpr) {{ Ψ }}.

(** The program names the flag and the table, the table holds three
    constructors, each pointer is a checked pointer to its constructor,
    and argc fits a signed 32-bit int. *)
Definition cr_ok (c : cr_in) : Prop :=
  lookup ctor_flag_name (ge_globals ge) = Some (mkPtr (cr_fl c) (Obj (cr_fl c))) /\
  lookup ctor_table_name (ge_globals ge) = Some (mkPtr (cr_tb c) (Ro (cr_tb c))) /\
  cr_fl c + 1 <= r_end (cr_flreg c) /\ cr_tb c mod 8 = 0 /\ cr_tb c + ctor_table_size 3 <= r_end (cr_treg c) /\
  length (cr_order c) = 3%nat /\ 0 <= cr_argc c < 2 ^ 31 /\
  0 <= ptr_addr (cr_argv c) < 2 ^ 64 /\ 0 <= ptr_addr (cr_env c) < 2 ^ 64 /\
  Forall2 (fun g p => ptr_cap p = Fn g /\ function_check_res ge p = Some ok /\ 0 <= ptr_addr p < 2 ^ 64)
    (cr_order c) (cr_ptrs c).

(** Every constructor receives argc, argv and environ, in this order. *)
Definition cr_args (c : cr_in) : list word := [WInt (cr_argc c); WPtr (cr_argv c); WPtr (cr_env c)].

(** The runner only reads its table, so it needs only a share of it. The
    share covers argc in the first four bytes, the pointers to the
    argument and environment arrays, and one pointer per constructor. It
    also covers shares of the two arrays' lives, so that the pointers the
    runner loads still point at live memory. *)
Definition cr_table (c : cr_in) : iProp Σ :=
  liveq (cr_dq c) (cr_tb c) (cr_treg c) ∗ bytesq (cr_dq c) (cr_tb c) 0 (le_bytes (cr_argc c) 4) ∗
  pcellq (cr_dq c) (cr_tb c) 8 (cr_argv c) ∗ pcellq (cr_dq c) (cr_tb c) 16 (cr_env c) ∗
  ([∗ list] i ↦ p ∈ cr_ptrs c, pcellq (cr_dq c) (cr_tb c) (24 + 8 * Z.of_nat i) p) ∗
  live_capq (cr_adq c) (ptr_cap (cr_argv c)) (cr_avreg c) ∗ live_capq (cr_adq c) (ptr_cap (cr_env c)) (cr_enreg c).

(** A call of the runner with a clear flag sets the flag and runs every
    constructor of the table once, in table order. Each constructor
    turns its own precondition cP g into its postcondition cQ g. *)
Definition ctor_runner_spec : fspec Σ :=
  FSpec (cr_in * (name -> iProp Σ) * (name -> iProp Σ)) (fun _ => [])
    (fun '(c, cP, cQ) =>
       ⌜cr_ok c /\ Forall (fun g => ctor_call_ok g (cr_args c) (cP g) (cQ g)) (cr_order c)⌝ ∗
       live (cr_fl c) (cr_flreg c) ∗ ibyte (cr_fl c) 0 0 ∗ cr_table c ∗ [∗ list] g ∈ cr_order c, cP g)%I
    (fun '(c, cP, cQ) r =>
       ⌜r = RetVoid⌝ ∗ live (cr_fl c) (cr_flreg c) ∗ ibyte (cr_fl c) 0 1 ∗ cr_table c ∗
       [∗ list] g ∈ cr_order c, cQ g)%I.

End spec.
