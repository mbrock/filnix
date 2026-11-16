(** This module proves the contract of `c: __tunable_get_val`, stated in
    [StartTunableGetValSpec](StartTunableGetValSpec.v), over the
    function's compiled body. The function branches on a tunable's type
    code, copies the value at the width that type gives, and runs a
    callback only when the tunable's initialized byte is set.

    ## How the proof is arranged

    Startup reads only size tunables and int tunables, so the proof
    follows the body down those two branches and no others. Each branch
    becomes a contract that a caller can use without this file. Only the
    final assembly of startup imports the proof itself. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic LibioCloseSteps GlibcSpec StartCode StartLogic StartTunableGetValSpec.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## Reading one tunable

    `c: __tunable_get_val` branches on the type code and copies the value
    at the width that the type gives. A size tunable is copied as an
    eight-byte value and an int tunable as four bytes. The two rules
    below cover those two cases, which are all that startup reads. *)

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Reading a size tunable, whose type code is 2, copies its eight-byte
    value to the destination. *)
Lemma wp_tunable_get_val_size fr id cb tl tlreg v dst dreg w Φ :
  call_frame start_tunable_get_val_fn [WInt id; WPtr (mkPtr dst (Obj dst)); WPtr cb] = Some fr ->
  lookup (TAtom "glibc_dl_tunables#tunable_list") (ge_globals ge) = Some (mkPtr tl (Obj tl)) ->
  0 <= id < 2 ^ 32 -> tl mod 8 = 0 -> tl + id * 136 + 136 <= r_end tlreg ->
  dst mod 8 = 0 -> dst + 8 <= r_end dreg ->
  live tl tlreg -∗ bytes tl (id * 136 + 48) (le_bytes 2 4) -∗ icell tl (id * 136 + 88) v -∗
  ibyte tl (id * 136 + 104) 0 -∗ live dst dreg -∗ icell dst 0 w -∗
  ▷ (live tl tlreg -∗ bytes tl (id * 136 + 48) (le_bytes 2 4) -∗ icell tl (id * 136 + 88) v -∗
     ibyte tl (id * 136 + 104) 0 -∗ live dst dreg -∗ icell dst 0 (v mod 2 ^ 64) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Htl Hid Hal Hend Hdal Hdend. injection Hfr as <-.
  iIntros "Hl Hty Hv Hin Hld Hd HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([H0 H48]) "Hl".
  iApply (wp_live_fit1 with "Hld"). iIntros ([D0 D48]) "Hld".
  step. step_global Htl. step. step. step. step. norm. check "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hty"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Hl Hty". step. branch. step. step. branch. step. step. branch.
  step. step. norm. check "Hl". iApply (wp_raw_load with "Hl Hv"); [reflexivity | vx | reflexivity | a2 |].
  iNext. iIntros "Hl Hv". check "Hld". store_long "Hld" "Hd".
  step. step. step. norm. check "Hl".
  iApply (wp_raw_load_byte with "Hl Hin"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Hl Hin". branch. step. branch. step. iApply wp_ret_void. iNext.
  rewrite Zmod_mod. iApply ("HK" with "Hl Hty Hv Hin Hld Hd").
Qed.

(** Reading an int tunable, whose type code is 0, copies the low four
    bytes of its value to the destination. *)
Lemma wp_tunable_get_val_int fr id cb tl tlreg v dst dreg xs Φ :
  call_frame start_tunable_get_val_fn [WInt id; WPtr (mkPtr dst (Obj dst)); WPtr cb] = Some fr ->
  lookup (TAtom "glibc_dl_tunables#tunable_list") (ge_globals ge) = Some (mkPtr tl (Obj tl)) ->
  0 <= id < 2 ^ 32 -> tl mod 8 = 0 -> tl + id * 136 + 136 <= r_end tlreg ->
  dst + 4 <= r_end dreg -> length xs = 4%nat ->
  live tl tlreg -∗ bytes tl (id * 136 + 48) (le_bytes 0 4) -∗ icell tl (id * 136 + 88) v -∗
  ibyte tl (id * 136 + 104) 0 -∗ live dst dreg -∗ bytes dst 0 xs -∗
  ▷ (live tl tlreg -∗ bytes tl (id * 136 + 48) (le_bytes 0 4) -∗ icell tl (id * 136 + 88) v -∗
     ibyte tl (id * 136 + 104) 0 -∗ live dst dreg -∗ bytes dst 0 (le_bytes ((v mod 2 ^ 64) mod 2 ^ 32) 4) -∗
     Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Htl Hid Hal Hend Hdend Hlen. injection Hfr as <-.
  iIntros "Hl Hty Hv Hin Hld Hd HK".
  iApply (wp_live_fit1 with "Hl"). iIntros ([H0 H48]) "Hl".
  iApply (wp_live_fit1 with "Hld"). iIntros ([D0 D48]) "Hld".
  step. step_global Htl. step. step. step. step. norm. check "Hl".
  iApply (wp_raw_load_sub_bytes_dq with "Hl Hty"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Hl Hty". step. branch. step. step. branch.
  step. step. norm. check "Hl". iApply (wp_raw_load with "Hl Hv"); [reflexivity | vx | reflexivity | a2 |].
  iNext. iIntros "Hl Hv". check "Hld". store_word "Hld Hd" by (a2) preserving (wi_store). iNext. iIntros "Hld Hd".
  step. step. step. norm. check "Hl".
  iApply (wp_raw_load_byte with "Hl Hin"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Hl Hin". branch. step. branch. step. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hl Hty Hv Hin Hld Hd").
Qed.

(** ## The contracts

    The two lemmas above take the entry's fields one by one. The
    instances below repackage them as the contracts that callers import,
    for any program in which the name runs the image's body. *)

(** A size tunable read satisfies [tunable_size_spec]. *)
#[global] Instance tunable_size_has_spec `{!Defines ge "__tunable_get_val" start_tunable_get_val_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "__tunable_get_val") tunable_size_spec.
Proof.
  intros [[[[[[[id cb] tl] tlreg] v] dst] dreg] w]. exists start_tunable_get_val_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fs_args tunable_size_spec].
  iIntros "(%H & Hl & (Hty & Hv & Hin) & Hld & Hd) HK". destruct H as ((Hg & Hid & Hal & Hend) & Hdal & Hdend).
  iApply (wp_tunable_get_val_size with "Hl Hty Hv Hin Hld Hd"); [exact Hfr | exact Hg | exact Hid | exact Hal
    | exact Hend | exact Hdal | exact Hdend |].
  iNext. iIntros "Hl Hty Hv Hin Hld Hd". iApply "HK". iFrame. done.
Qed.

(** An int tunable read satisfies [tunable_int_spec]. *)
#[global] Instance tunable_int_has_spec `{!Defines ge "__tunable_get_val" start_tunable_get_val_fn} :
  HasSpec registry (os_wi w0) ge (TAtom "__tunable_get_val") tunable_int_spec.
Proof.
  intros [[[[[[[id cb] tl] tlreg] v] dst] dreg] xs]. exists start_tunable_get_val_fn.
  split; [apply defines|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fs_args tunable_int_spec].
  iIntros "(%H & Hl & (Hty & Hv & Hin) & Hld & Hd) HK". destruct H as ((Hg & Hid & Hal & Hend) & Hdend & Hlen).
  iApply (wp_tunable_get_val_int with "Hl Hty Hv Hin Hld Hd"); [exact Hfr | exact Hg | exact Hid | exact Hal
    | exact Hend | exact Hdend | exact Hlen |].
  iNext. iIntros "Hl Hty Hv Hin Hld Hd". iApply "HK". iFrame. done.
Qed.

End rules.
