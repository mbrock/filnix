(** This module proves the contract of `c: __libc_setup_tls`, stated in
    [StartSetupTlsSpec](StartSetupTlsSpec.v), over the function's
    compiled body. The function allocates the thread object, points its
    two self fields at it, makes it the cookie and then calls
    `c: __tls_init_tp`.

    ## How the callee enters

    The function calls `c: __tls_init_tp` only after it has made the new
    object the cookie. The allocator picks that object's address, so no
    one knows it before the call starts. The proof therefore asks for
    the callee's contract at every address the object could have. *)

From Glibc Require Import GlibcProgram.
From Glibc Require Import GlibcTactics LibioTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsStartCalls FileInv LibioLogic LibioCloseSteps OsStart StartCode StartLogic
  StartTlsInitTpSpec StartSetupTlsSpec.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## The proof

    Editing one function's proof should rebuild as little as possible.
    So this file assumes what `c: __tls_init_tp` promises and never
    imports how that promise was proved. The world is read through the
    ghost key k throughout. *)

Section setup.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract os_world)) (ge : genv) (w0 : os_world) (k : Z).
Context (Hinit : forall tb, HasSpec registry (os_wi (start_world w0 (mkPtr tb (Obj tb)) false false)) ge
  (TAtom "__tls_init_tp") (tls_init_tp_spec ge tb)).

(** In this section the program reads the OS world through the key k,
    over the base world w0. *)
Local Instance setup_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi_start w0 k) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Garbage collection keeps the startup interpretation. *)
Local Instance setup_stable : LG0.SafepointStable (os_wi_start w0 k) := os_wi_start_stable w0 k.

(** The body ends with the new thread object as the cookie. *)
Lemma wp_setup_tls fr c re rereg x se sereg sp spreg Φ :
  call_frame start_setup_tls_fn [] = Some fr ->
  registry (TAtom "zthread_set_self_cookie") = Some os_set_cookie_contract ->
  os_ext ge "zthread_set_self_cookie" ->
  lookup (TAtom "__nptl_initial_report_events") (ge_globals ge) = Some (mkPtr re (Obj re)) ->
  lookup (TAtom "__libc_stack_end") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  re + 1 <= r_end rereg -> se mod 8 = 0 -> se + 8 <= r_end sereg -> 0 <= x < 256 -> 0 <= ptr_addr sp < 2 ^ 64 ->
  pointsto (PName k) (DfracOwn 1) (start_ghost c false false) -∗
  live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
  ▷ (∀ tb t a, ⌜0 < tb /\ tb mod 16 = 0 /\ tb + 2496 <= 2 ^ 48 /\ 0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ -∗
       pointsto (PName k) (DfracOwn 1) (start_ghost (mkPtr tb (Obj tb)) false false) -∗
       live tb (mkRegion tb (tb + 2496) Heap Live) -∗
       pcell tb 0 (mkPtr tb (Obj tb)) -∗ pcell tb 16 (mkPtr tb (Obj tb)) -∗ tp_fields tb t a x sp -∗
       pcell tb 776 null -∗ pcell tb 784 null -∗ bytes tb 792 [0; 0; 0; 0] -∗
       live re rereg -∗ ibyte re 0 x -∗ live se sereg -∗ pcell se 0 sp -∗ live_cap (ptr_cap sp) spreg -∗
       Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hrs [Hfs Hgs] Hre Hse Hreend Hseal Hseend Hx Hsp. injection Hfr as <-.
  iIntros "Hkey Hlre Hre Hlse Hse Hcap HK". step.
  iApply wp_alloc; [reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_start_alloc _ _ _ _ _ _ _ Hf Hw) |].
  change (2496 mod 2 ^ 64) with 2496.
  iNext. iIntros (tb (Htb & Hal & Hend)) "Ho".
  change (req_extent (heap_req 16 2496)) with 2496 in Hend. change (req_align (heap_req 16 2496)) with 16 in Hal.
  assert (Hal8 : tb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  iDestruct (tcb_fresh with "Ho") as "(Hl & H0 & H16 & Htp & H776 & H784 & H792)".
  remember (mkRegion tb (tb + 2496) Heap Live) as treg eqn:Etreg.
  assert (Htr : r_end treg = tb + 2496) by (rewrite Etreg; reflexivity).
  check "Hl". iApply (wp_raw_store_pointer with "Hl H0"); [vx | vx | reflexivity | a2 | a2 | wi_store_start |].
  iNext. iIntros "Hl H0". step. norm. check "Hl".
  iApply (wp_raw_store_pointer with "Hl H16"); [vx | vx | reflexivity | a2 | a2 | wi_store_start |].
  iNext. iIntros "Hl H16".
  iApply (wp_zthread_set_self_cookie_start _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (live tb _) with "Hkey Hl");
    [exact Hrs | exact Hfs | exact Hgs | reflexivity | |].
  { iIntros (h m) "Hh Hl". rewrite /live pts_ptsq. iApply (self_registered_liveq with "Hh Hl"). }
  iNext. iIntros "Hkey Hl".
  destruct (Hinit tb (treg, re, rereg, x, se, sereg, sp, spreg)) as (gf & Hgf & [fr0 Hfr0] & Hwp).
  eapply step_wand; [eapply wp_call_bind; inst; [reflexivity | exact Hgf | exact Hfr0] |].
  iApply (wp_wand with "[Hkey Hl Htp Hlre Hre Hlse Hse Hcap]").
  { iApply (wp_start_of_os registry ge w0 k (mkPtr tb (Obj tb)) false false (DfracOwn 1) with "Hkey").
    iApply (Hwp with "[Hl Htp Hlre Hre Hlse Hse Hcap]"); [exact Hfr0 | |].
    { cbn [fs_pre tls_init_tp_spec]. iFrame. iPureIntro. repeat split; try eassumption; lia. }
    cbn [fs_post tls_init_tp_spec]. iIntros (o) "H". iExact "H". }
  iIntros (o) "[Hkey (-> & %t & %a & %Hta & Hl & Hf & Hlre & Hre & Hlse & Hse & Hcap)]".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply wp_ret_void. iNext. subst treg.
  iApply ("HK" with "[%] Hkey Hl H0 H16 Hf H776 H784 H792 Hlre Hre Hlse Hse Hcap"). lia.
Qed.

(** Any program whose image defines `c: __libc_setup_tls` with this body
    meets the contract. *)
Lemma setup_tls_has_spec :
  find_fn ge (TAtom "__libc_setup_tls") = Some (Defined start_setup_tls_fn) ->
  registry (TAtom "zthread_set_self_cookie") = Some os_set_cookie_contract ->
  os_ext ge "zthread_set_self_cookie" ->
  HasSpec registry (os_wi_start w0 k) ge (TAtom "__libc_setup_tls") (setup_tls_spec ge k).
Proof.
  intros Hf Hrs Hes [[[[[[[c re] rereg] x] se] sereg] sp] spreg].
  exists start_setup_tls_fn. split; [exact Hf|]. split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post fs_args setup_tls_spec].
  iIntros "(%H & Hkey & Hlre & Hre & Hlse & Hse & Hcap) HK".
  destruct H as (Hre_g & Hse_g & Hreend & Hseal & Hseend & Hx & Hsp).
  iApply (wp_setup_tls with "Hkey Hlre Hre Hlse Hse Hcap"); try eassumption.
  iNext. iIntros (tb t a Hta) "Hkey Hl H0 H16 Hf H776 H784 H792 Hlre Hre Hlse Hse Hcap". iApply "HK".
  iSplit; [done|]. iExists tb, t, a. iSplit; [done|]. iFrame.
Qed.

End setup.
