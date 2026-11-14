From Glibc Require Import GlibcProgram.
(** A program parses long options by calling glibc's getopt_long with
    the argument count, the argument vector, the short-option string,
    the table of long options and a cell for the matched index. The
    function does nothing itself. It calls the wrapper _getopt_internal
    with those five arguments and two zero flags, one that turns off the
    long-only mode and one that turns off the strict POSIX order, and it
    returns what the wrapper returns. This file proves that call on top
    of the wrapper's rule, so the parser's own behaviour stays a premise. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptWrapper.
From Glibc Require FileInv GetoptInitialize GetoptState GetoptWrapper LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Transparent glibc_getopt_long glibc_getopt_internal.

(** ## The function's single call

    A proof about getopt_long is useful only if it follows the code that
    the program runs. The function has one block, which calls the
    wrapper and returns the result. The facts below pin that block down,
    including the order of the arguments and the two zero flags. *)

(** The function has no stack objects, takes five arguments and returns a 32-bit integer. *)
Lemma getopt_long_shape : local_objects glibc_getopt_long = [] /\ fn_ret glibc_getopt_long = RClass W /\
  List.length (fn_params glibc_getopt_long) = 5%nat.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** The function's only block is its first block. *)
Definition getopt_long_blk : block := Eval vm_compute in
  match find_block (TAtom "start") (fn_blocks glibc_getopt_long) with
  | Some b => b | None => mkBlock (TAtom "start") [] [] JUnreachable end.

(** The block passes its five parameters in order, then 0 for the
    long-only flag and 0 for the strict-order flag, and returns the
    wrapper's result. *)
Lemma getopt_long_call :
  b_insts getopt_long_blk = [Call (CResult (TAtom "v15") W) (Global (TAtom "_getopt_internal"))
    [Arg W (Tmp (TAtom "v0")); Arg P (Tmp (TAtom "v2")); Arg P (Tmp (TAtom "v4")); Arg P (Tmp (TAtom "v6"));
     Arg P (Tmp (TAtom "v8")); Arg W (Const 0); Arg W (Const 0)]] /\
  b_jump getopt_long_blk = JRet (Tmp (TAtom "v15")).
Proof. vm_compute. split; reflexivity. Qed.

(** These controls use five different values, so a call that swapped two
    pointers or passed a nonzero flag would produce a different list. With
    three arguments and pointers at 16, 24, 32 and 40, the call passes
    them in that order and then two zeros. *)
Lemma getopt_long_ctl_args ge :
  map_option (arg_x ge [(TAtom "v0", WInt 3); (TAtom "v2", WPtr (mkPtr 16 (Obj 16)));
      (TAtom "v4", WPtr (mkPtr 24 (Ro 24))); (TAtom "v6", WPtr (mkPtr 32 (Ro 32)));
      (TAtom "v8", WPtr (mkPtr 40 (Obj 40)))])
    [Arg W (Tmp (TAtom "v0")); Arg P (Tmp (TAtom "v2")); Arg P (Tmp (TAtom "v4")); Arg P (Tmp (TAtom "v6"));
     Arg P (Tmp (TAtom "v8")); Arg W (Const 0); Arg W (Const 0)] =
  Some [WInt 3; WPtr (mkPtr 16 (Obj 16)); WPtr (mkPtr 24 (Ro 24)); WPtr (mkPtr 32 (Ro 32));
        WPtr (mkPtr 40 (Obj 40)); WInt 0; WInt 0].
Proof. reflexivity. Qed.

(** The long-option table and the index cell are both pointers, so only
    their distinct values show whether they arrive in the right order. *)
Lemma getopt_long_ctl_order :
  [WPtr (mkPtr 32 (Ro 32)); WPtr (mkPtr 40 (Obj 40))] <> [WPtr (mkPtr 40 (Obj 40)); WPtr (mkPtr 32 (Ro 32))].
Proof. discriminate. Qed.

(** The public index decides whether the parser starts over. An index of
    0, copied into the private object, makes the parser start over, and
    an index of 2 in a set-up object does not. *)
Lemma getopt_long_ctl_index :
  needs_init (mkGetoptState 0 1 0 null 1 null 0 0 0) /\ ~ needs_init (mkGetoptState 2 1 0 null 1 null 0 1 1).
Proof. unfold needs_init. cbn. split; [left; reflexivity | lia]. Qed.


(** The wrapper module proves the copies around the reentrant parser. *)
Import GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic.

Import ProgramAbbreviations.
Section long_wrapper.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the call's safepoints. *)
Local Instance lw_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## How getopt_long reaches the parser

    A program sees only getopt_long, so the safety of its option loop
    depends on what this one call does with the public cells. The caller
    of getopt_long holds the same resources as the caller of the
    wrapper, and the lemma below passes them through the call. *)

(** After each call of getopt_long, a program reads optind, optarg and
    optopt, so each must hold the value that the parser left. The caller
    describes the reentrant parser on the frame that the wrapper builds,
    in which both flags are 0. The function then returns the parser's
    32-bit result. The private index is in optind, the argument is in
    optarg with its capability, and the option character is in optopt.
    The value of opterr does not change, and the caller's own resources
    come back with the parser. *)
Lemma wp_getopt_long e n av p lo li b r oi roi oe roe oa roa oo roo i err a0 c0 i0 e0
    (Ψ : Z -> Z -> Z -> ptr -> iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr av) ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> 0 <= n < 2 ^ 32 ->
  find_fn ge (TAtom "_getopt_internal") = Some (Defined glibc_getopt_internal) ->
  find_fn ge (TAtom "_getopt_internal_r") = Some (Defined glibc_getopt_internal_r) ->
  lookup (TAtom "glibc_getopt#getopt_data") (ge_globals ge) = Some (mkPtr b (Obj b)) ->
  lookup (TAtom "optind") (ge_globals ge) = Some (mkPtr oi (Obj oi)) ->
  lookup (TAtom "opterr") (ge_globals ge) = Some (mkPtr oe (Obj oe)) ->
  lookup (TAtom "optarg") (ge_globals ge) = Some (mkPtr oa (Obj oa)) ->
  lookup (TAtom "optopt") (ge_globals ge) = Some (mkPtr oo (Obj oo)) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < oi -> oi + 4 <= r_end roi -> r_end roi <= 2 ^ 48 ->
  0 < oe -> oe + 4 <= r_end roe -> r_end roe <= 2 ^ 48 ->
  0 < oa -> oa mod 8 = 0 -> oa + 8 <= r_end roa -> r_end roa <= 2 ^ 48 ->
  0 < oo -> oo + 4 <= r_end roo -> r_end roo <= 2 ^ 48 ->
  live oi roi -∗ int_cell oi 0 i -∗ live oe roe -∗ int_cell oe 0 err -∗
  live oa roa -∗ pcell oa 0 a0 -∗ live oo roo -∗ int_cell oo 0 c0 -∗
  live b r -∗ int_cell b 0 i0 -∗ int_cell b 4 e0 -∗
  (∀ cf, ⌜call_frame glibc_getopt_internal_r
            [WInt n; WPtr av; WPtr p; WPtr lo; WPtr li; WInt 0; WPtr (mkPtr b (Obj b)); WInt 0] = Some cf⌝ -∗
     live b r -∗ int_cell b 0 i -∗ int_cell b 4 err -∗
     WP (ERun cf : gexpr) {{ o, ∃ x i' c' a' ra, ⌜o = Ret (WInt x) /\ 0 <= x < 2 ^ 32 /\ 0 <= ptr_addr a' < 2 ^ 64⌝ ∗
       live b r ∗ int_cell b 0 i' ∗ int_cell b 8 c' ∗ pcell b 16 a' ∗ live_capq DfracDiscarded (ptr_cap a') ra ∗
       Ψ x i' c' a' }}) -∗
  (∀ x i' c' a', ⌜0 <= x < 2 ^ 32⌝ -∗ Ψ x i' c' a' -∗ live b r -∗ int_cell b 0 i' -∗ int_cell b 8 c' -∗
     pcell b 16 a' -∗ live oi roi -∗ int_cell oi 0 i' -∗ live oe roe -∗ int_cell oe 0 err -∗
     live oa roa -∗ pcell oa 0 a' -∗ live oo roo -∗ int_cell oo 0 c' -∗ Φ (Ret (WInt x))) -∗
  WP (ERun (mkFrame glibc_getopt_long e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros H0 H2 H4 H6 H8 Hn Hfi Hfr Hgd Hgi Hge Hga Hgo
    Hb Hal Hend Hr Hoi Hoie Hoir Hoe Hoee Hoer Hoa Hoaa Hoae Hoar Hoo Hooe Hoor.
  iIntros "Hli Hi Hle He Hla Hab Hlo Hc Hl Hb0 Hb4 HR HK".
  iApply wp_enter; [reflexivity | reflexivity | iNext]; cbn [b_insts b_jump].
  iApply (wp_call_bind registry (os_wi w0) ge _ _ _ _ _ _ _ _ _
            [WInt n; WPtr av; WPtr p; WPtr lo; WPtr li; WInt 0; WInt 0] glibc_getopt_internal
            (mkFrame glibc_getopt_internal [(TAtom "v12", WInt 0); (TAtom "v10", WInt 0); (TAtom "v8", WPtr li);
               (TAtom "v6", WPtr lo); (TAtom "v4", WPtr p); (TAtom "v2", WPtr av); (TAtom "v0", WInt n)] [] None
               (Enter (TAtom "start") None)));
    [ cbn; rewrite H0 H2 H4 H6 H8; cbn; unwrap; reflexivity | exact Hfi | reflexivity |].
  iNext.
  iApply (GetoptWrapper.wp_getopt_internal _ n av p lo li 0 0 b r oi roi oe roe oa roa oo roo i err a0 c0 i0 e0
            (fun x i' c' a' => ⌜0 <= x < 2 ^ 32⌝ ∗ Ψ x i' c' a')%I
            with "Hli Hi Hle He Hla Hab Hlo Hc Hl Hb0 Hb4 [HR] [HK]");
    try (reflexivity || assumption || lia).
  - iIntros (cf Hcf) "Hl Hi He".
    iApply (wp_wand with "[HR Hl Hi He]"); [iApply ("HR" with "[%] Hl Hi He"); exact Hcf|].
    iIntros (o) "(%x & %i' & %c' & %a' & %ra & (%Ho & %Hx & %Ha) & Hl & Hi & Hc & Hp & Hcap & HΨ)".
    iExists x, i', c', a', ra. iSplit; [iPureIntro; tauto|]. iFrame. iPureIntro. exact Hx.
  - iIntros (x i' c' a') "[%Hx HΨ] Hl Hb0 Hb8 Hb16 Hli Hi Hle He Hla Hab Hlo Hc".
    iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
    iApply (wp_ret registry (os_wi w0) ge _ _ _ _ _ (WInt x)); [reflexivity | cbn; unwrap; reflexivity |].
    iNext. iApply ("HK" with "[%] HΨ Hl Hb0 Hb8 Hb16 Hli Hi Hle He Hla Hab Hlo Hc"). exact Hx.
Qed.

End long_wrapper.
