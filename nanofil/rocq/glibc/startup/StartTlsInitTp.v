(** This module proves the contract of `c: __tls_init_tp`, stated in
    [StartTlsInitTpSpec](StartTlsInitTpSpec.v), over the function's
    compiled body. The function asks the runtime for the cookie, the
    kernel thread id and the runtime's thread handle, and stores them
    and a few self pointers in the thread object.

    ## Why no errno handler is needed

    A runtime call that fails would set errno, which panics before the
    errno handler is registered. None of the three calls here can fail,
    so the proof runs in any world whose cookie is the thread object. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsStartCalls FileInv LibioLogic LibioCloseSteps OsStart StartCode StartLogic
  StartTlsInitTpSpec.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The body fills in the object's fields when the cookie already names
    it. *)
Lemma wp_tls_init_tp fr tb treg re rereg x se sereg sp spreg Φ :
  call_frame start_tls_init_tp_fn [] = Some fr ->
  registry (TAtom "zthread_self_cookie") = Some os_self_contract ->
  registry (TAtom "zthread_self_id") = Some os_self_id_contract ->
  registry (TAtom "zthread_self") = Some os_thread_self_contract ->
  os_ext ge "zthread_self_cookie" -> os_ext ge "zthread_self_id" -> os_ext ge "zthread_self" ->
  lookup (TAtom "__nptl_initial_report_events") (ge_globals ge) = Some (mkPtr re (Obj re)) ->
  lookup (TAtom "__libc_stack_end") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  re + 1 <= r_end rereg -> se mod 8 = 0 -> se + 8 <= r_end sereg -> 0 <= x < 256 -> 0 <= ptr_addr sp < 2 ^ 64 ->
  ow_self w0 = mkPtr tb (Obj tb) -> 0 < tb -> tb mod 16 = 0 -> tb + 2496 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  live tb treg -∗ tp_zero tb -∗
  live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
  ▷ (∀ t a, ⌜0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ -∗ live tb treg -∗ tp_fields tb t a x sp -∗
       live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
       Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hr1 Hr2 Hr3 [Hf1 Hg1] [Hf2 Hg2] [Hf3 Hg3] Hre Hse Hreend Hseal Hseend Hx Hsp Hself Htb Hal Hend Hreg.
  injection Hfr as <-. assert (Hal8 : tb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iIntros "Hl (H720 & H728 & H736 & H744 & H752 & H760 & H1312 & H1569 & H1572 & H1592 & H1720)
    Hlre Hre Hlse Hse Hcap HK".
  step.
  iApply wp_zthread_self_cookie; [exact Hr1 | exact Hf1 | exact Hg1 | rewrite Hself; cbn; lia |]. iNext.
  rewrite Hself. step.
  iApply wp_zthread_self_id; [exact Hr2 | exact Hf2 | exact Hg2 |]. iNext. iIntros (t Ht).
  norm. check "Hl". store_int "Hl" "H720". step. norm.
  iApply wp_zthread_self; [exact Hr3 | exact Hf3 | exact Hg3 |]. iNext. iIntros (a Ha).
  check "Hl". store "Hl" "H728".
  step. norm. check "Hl". store_int "Hl" "H736".
  step. step. norm. check "Hl". store "Hl" "H1312".
  step. norm. check "Hl". store_int "Hl" "H1572".
  step. norm. check "Hl". store_int "Hl" "H1592".
  step. step_global Hre. norm.
  iApply (wp_live_fit1 with "Hlre"). iIntros ([Hre0 Hre48]) "Hlre". check "Hlre".
  iApply (wp_raw_load_byte with "Hlre Hre"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Hlre Hre". check "Hl".
  iApply (wp_raw_store_byte with "Hl H1569"); [vx | vx | reflexivity | a2 | wi_store |]. iNext.
  iIntros "Hl H1569".
  step. step. norm. check "Hl". store "Hl" "H744".
  check "Hl". store "Hl" "H752".
  step. norm. check "Hl". store_long "Hl" "H760".
  step. step_global Hse. iApply (wp_live_fit1 with "Hlse"). iIntros ([Hse0 Hse48]) "Hlse".
  check "Hlse". load "Hlse" "Hse" "Hcap". step. norm. check "Hl". store_long "Hl" "H1720".
  iApply wp_ret_void. iNext.
  replace (((extension Ub x mod 2 ^ 32) mod 2 ^ 32) mod 256) with x
    by (cbn [extension]; rewrite !(Z.mod_small x); lia).
  rewrite (Z.mod_small (ptr_addr sp)); [|lia].
  iApply ("HK" $! t a with "[%] Hl [H720 H728 H736 H744 H752 H760 H1312 H1569 H1572 H1592 H1720] Hlre Hre Hlse Hse Hcap");
    [lia | rewrite /tp_fields; iFrame "H720 H728 H736 H744 H752 H760 H1312 H1569 H1572 H1592 H1720"].
Qed.

(** A program whose image defines `c: __tls_init_tp` with this body meets
    the contract for the object that its cookie names. *)
Lemma tls_init_tp_has_spec tb
    `{!Defines ge "__tls_init_tp" start_tls_init_tp_fn} :
  registry (TAtom "zthread_self_cookie") = Some os_self_contract ->
  registry (TAtom "zthread_self_id") = Some os_self_id_contract ->
  registry (TAtom "zthread_self") = Some os_thread_self_contract ->
  os_ext ge "zthread_self_cookie" -> os_ext ge "zthread_self_id" -> os_ext ge "zthread_self" ->
  ow_self w0 = mkPtr tb (Obj tb) ->
  HasSpec registry (os_wi w0) ge (TAtom "__tls_init_tp") (tls_init_tp_spec ge tb).
Proof using Type.
  intros Hr1 Hr2 Hr3 He1 He2 He3 Hself [[[[[[[treg re] rereg] x] se] sereg] sp] spreg].
  exists start_tls_init_tp_fn. split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fs_args tls_init_tp_spec].
  iIntros "(%H & Hl & Hz & Hlre & Hre & Hlse & Hse & Hcap) HK".
  destruct H as (Hre_g & Hse_g & Hreend & Hseal & Hseend & Hx & Hsp & Htb & Hal & Hend & Hreg).
  iApply (wp_tls_init_tp with "Hl Hz Hlre Hre Hlse Hse Hcap"); try eassumption.
  iNext. iIntros (t a Hta) "Hl Hf Hlre Hre Hlse Hse Hcap". iApply "HK". iSplit; [done|].
  iExists t, a. iSplit; [done|]. iFrame.
Qed.

End rules.
