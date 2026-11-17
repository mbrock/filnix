(** Startup runs the deferred constructors through the runner that the
    model appends to the image, `c: zrun_deferred_global_ctors`
    ([StartCtors](../zsys/StartCtors.v)). The runner calls each pointer
    in its table with the saved argc, argv and environ. The image does
    not record the order of the table, so its contract must hold for
    every order. This module states that contract, and
    [StartCtorRunner](StartCtorRunner.v) proves it.

    ## Constructors as parameters

    Nobody knows in advance the order in which the constructors run,
    because the starting memory may list them in any order. So the
    contract does not name them. Two constructors may also need the same
    memory: both `c: _IO_stdfiles_init` and `c: check_stdfiles_vtables`
    need the lives of the standard streams. So the contract follows one
    assertion K through all the calls, and K is told which constructors
    have already run. Each call must turn K before it into K after it.
    The final assembly shows this for each real constructor from its own
    contract. *)

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

(** The runner calls the constructors one after another, so each call
    must leave memory as the next call expects it. The call of the i-th
    constructor starts from K applied to the first i names and ends in K
    applied to the first i + 1 names. *)
Definition ctor_chain_ok (xs : list word) (K : list name -> iProp Σ) (order : list name) : Prop :=
  forall i g, nth_error order i = Some g -> ctor_call_ok g xs (K (firstn i order)) (K (firstn (S i) order)).

(** A call of the runner with a clear flag sets the flag and runs every
    constructor of the table once, in table order. The assertion K goes
    from no constructor run to all of them run. *)
Definition ctor_runner_spec : fspec Σ :=
  FSpec (cr_in * (list name -> iProp Σ)) (fun _ => [])
    (fun '(c, K) =>
       ⌜cr_ok c /\ ctor_chain_ok (cr_args c) K (cr_order c)⌝ ∗
       live (cr_fl c) (cr_flreg c) ∗ ibyte (cr_fl c) 0 0 ∗ cr_table c ∗ K [])%I
    (fun '(c, K) r =>
       ⌜r = RetVoid⌝ ∗ live (cr_fl c) (cr_flreg c) ∗ ibyte (cr_fl c) 0 1 ∗ cr_table c ∗ K (cr_order c))%I.

End spec.
