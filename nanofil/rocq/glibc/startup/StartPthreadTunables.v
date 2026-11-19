(** This module proves the contract of `c: __pthread_tunables_init`,
    stated in [StartPthreadTunablesSpec](StartPthreadTunablesSpec.v), over
    the function's compiled body. The function allocates a four-byte
    variable, reads tunable 27 into it through `c: __tunable_get_val` and
    reads the variable back.

    ## How the callee enters

    The proof uses the contract of `c: __tunable_get_val` as a premise
    rather than importing its proof. So a change to that proof rebuilds
    only that file and the final startup assembly, not this one. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics OsTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps StartCode
  StartTunableGetValSpec StartPthreadTunablesSpec.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

(** ## The proof

    Reading the spin count needs a place to put it, so the function
    first makes room for a four-byte local. It then asks for tunable 27
    to be copied there and reads the local back. All the proof needs to
    know about the copy is that it fills those four bytes and leaves the
    table alone. *)

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context `{Hget : !HasSpec registry (os_wi w0) ge (TAtom "__tunable_get_val") tunable_int_spec}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The function satisfies its contract, given the callback's address in
    the program. *)
#[global] Instance pthread_tunables_init_has_spec cb
    `{!Defines ge "__pthread_tunables_init" start_pthread_tunables_init_fn} :
  lookup (TAtom "glibc_pthread_mutex_conf#_dl_tunable_set_mutex_spin_count") (ge_globals ge) = Some cb ->
  HasSpec registry (os_wi w0) ge (TAtom "__pthread_tunables_init") pthread_tunables_init_spec.
Proof using Type*.
  intros Hcb [[tl tlreg] v]. exists start_pthread_tunables_init_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr. injection Hfr as <-.
  cbn [fs_pre fs_post fs_args pthread_tunables_init_spec].
  iIntros "(%Hok & Hl & Hent) HK". step.
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  change (4 mod 2 ^ 64) with 4.
  iNext. iIntros (b (Hb & Hbal & Hbend)) "Ho".
  change (req_extent (heap_req 4 4)) with 16 in Hbend.
  rewrite obj_zero_block; [|vm_compute; congruence].
  change (req_extent (heap_req 4 4)) with 16. change (req_kind (heap_req 4 4)) with Heap.
  change (replicate (Z.to_nat 16) 0) with ([0; 0; 0; 0] ++ replicate 12 0)%list.
  rewrite bytes_app. iDestruct "Ho" as "(Hlb & [Hx _] & _)".
  remember (mkRegion b (b + 16) Heap Live) as breg eqn:Ebreg.
  assert (Hbr : r_end breg = b + 16) by (rewrite Ebreg; reflexivity).
  step_global Hcb.
  iApply (wp_call_spec registry (os_wi w0) ge _ tunable_int_spec
            (27, cb, tl, tlreg, v, b, breg, [0; 0; 0; 0]) with "[Hl Hent Hlb Hx]");
    [reflexivity | iFrame; iPureIntro; split_and!; [exact Hok | lia | reflexivity] |].
  iIntros (o) "(-> & Hl & Hent & Hlb & Hx)". iExists _. iSplit; [done|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply (wp_live_fit1 with "Hlb"). iIntros ([B0 B48]) "Hlb".
  check "Hlb".
  iApply (wp_raw_load_sub_bytes_dq with "Hlb Hx"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Hlb Hx". iApply wp_ret_void. iNext. iApply "HK". iFrame. done.
Qed.

End rules.
