(** The locked middle of `c: _IO_un_link` (LibioUnlinkCode.v), from
    block `c: L22`, with `c: list_all_lock` taken and the cleanup
    buffer pushed: `c: run_fp` is the stream, the stream's lock, free,
    is taken by the single thread (`c: L96` to `c: L101`), and
    `c: L91` reads the list's head, the stream itself or the first of
    the streams before it; then LibioUnlinkMid.v's [unlink_split] and
    [wp_unlink_L185]. LibioUnlink.v proves the whole function. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsThread OsRegistry SysCode LibioUnlinkCode FileInv LibioLogic
  SysWrappers SysCleanup LibioCloseSteps LibioUnlinkTail LibioUnlinkMid.
From Glibc Require FileInv LibioCloseSteps LibioLogic LibioUnlinkMid LibioUnlinkTail OsThread OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioUnlinkMid LibioUnlinkTail SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hpop : find_fn ge (TAtom "__GI___libc_cleanup_pop_restore") =
                Some (Defined glibc___libc_cleanup_pop_restore)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance unlink_lock_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The premises of `c: zthread_self_cookie`'s rule. *)
Ltac self_side := first [apply (reg_of registry Hreg); reflexivity | apply (ext_fn ge Hext); cbn; tauto
                        | apply (ext_data ge Hext); cbn; tauto].

(** A call of `c: zthread_self_cookie`, whose result is the thread's
    cookie, not null (H). *)
Ltac self H := iApply (OsThread.wp_zthread_self_cookie w0 registry ge); try self_side; [exact H|]; iNext.

(** Block `c: L22` of `c: _IO_un_link` to its return, `c: list_all_lock`
    held once by the thread and the cleanup buffer cb pushed: the
    stream fb of the list pre ++ fb :: post, whose lock is free, leaves
    the list, as [wp_glibc__IO_un_link] says. *)
Lemma wp_unlink_L22 e from pre post fb freg fl lb lbreg la lareg lk lkreg rf rfreg cb creg sb sreg x Φ :
  lookup (TAtom "__GI__IO_list_all") (ge_globals ge) = Some (mkPtr la (Obj la)) ->
  lookup (TAtom "glibc_genops#list_all_lock") (ge_globals ge) = Some (mkPtr lk (Obj lk)) ->
  lookup (TAtom "glibc_genops#run_fp") (ge_globals ge) = Some (mkPtr rf (Obj rf)) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v10") e = Some (WPtr (mkPtr cb (Obj cb))) ->
  ptr_addr (ow_self w0) <> 0 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 <= fl < 2 ^ 32 -> Z.land fl 32768 = 0 ->
  la mod 8 = 0 -> la + 8 <= r_end lareg -> rf mod 8 = 0 -> rf + 8 <= r_end rfreg ->
  0 < cb -> cb mod 8 = 0 -> cb + 32 <= r_end creg -> r_end creg <= 2 ^ 63 ->
  single_ro ge sb sreg -∗ tcb_pushed (ow_self w0) (mkPtr cb (Obj cb)) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
  lock_state lb lbreg 0 0 null -∗
  live la lareg -∗ pcell la 0 (head_ptr (pre ++ mkPtr fb (Obj fb) :: post)) -∗
  chain_links (mkPtr la (Obj la)) (pre ++ mkPtr fb (Obj fb) :: post) -∗
  lock_state lk lkreg 1 0 (ow_self w0) -∗ live rf rfreg -∗ pcell rf 0 x -∗
  ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  live cb creg -∗ pcell cb 24 null -∗ int_cell cb 16 0 -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ live fb freg -∗ int_cell fb off_flags (unlinked_flags fl) -∗
     pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
     live la lareg -∗ pcell la 0 (head_ptr (pre ++ post)) -∗ chain_links (mkPtr la (Obj la)) (pre ++ post) -∗
     lock_state lk lkreg 0 0 null -∗ live rf rfreg -∗ pcell rf 0 null -∗
     ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     (∃ c p, pcell fb off_chain c ∗ pcell fb off_prevchain p) -∗ Φ RetVoid) -∗
  WP (ERun (mkFrame glibc__IO_un_link e [] None (Enter (TAtom "L22") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hgla Hglk Hgrf Hv0 Hc0 Hv10 Hsz Hfb Hfal Hfend Hfreg Hfl Hul Hlaal Hlaend Hral Hrend Hcb Hcal8 Hcend
    Hcreg.
  unfold file_size in Hfend. assert (0 <= Z.land fl 32768 < 2 ^ 32) by (rewrite Hul; lia).
  iIntros "#Hs Htcb Hl [_ Hfl] Hlp Hlb Hla Hlah Hch Hlk Hrl Hrc Hlives Hcl Hc24 Hc16 HK".
  iPoseProof "Hs" as "(%Hs' & Hsl & Hsb)". destruct Hs' as (Hgs & Hsend).
  iDestruct "Hlb" as "(%Hb & Hbl & [%Hb0r Hb0] & [%Hb4r Hb4] & Hbo)". destruct Hb as (Hbal & Hbend & Hbreg).
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hla"). iIntros ([Hla0 Hla48]) "Hla".
  iApply (wp_live_fit1 w0 registry ge with "Hbl"). iIntros ([Hlb0 Hlb48]) "Hbl".
  iApply (wp_live_fit1 w0 registry ge with "Hrl"). iIntros ([Hrf0 Hrf48]) "Hrl".
  iApply (wp_live_fit w0 registry ge with "Hsl"). iIntros ([Hsb0 Hsb48]) "_".
  (* L22: `c: run_fp`; L96 to L101: take the stream's lock. *)
  step. step. check "Hrl". store "Hrl" "Hrc". check "Hl". load_s32 "Hl" "Hfl". step. step. branch_as false.
  step. self Hsz. step. check_persistent "Hsl". load_byte_persistent "Hsl Hsb". step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". step. check "Hbl". load_null "Hbl" "Hbo". step. step. step. step. step. branch.
  step. step. check "Hl". load "Hl" "Hlp" "Hbl". check "Hbl". store_int "Hbl" "Hb0". load "Hl" "Hlp" "Hbl". step.
  check "Hbl". store "Hbl" "Hbo". step.
  (* L91: the list's head, fp or the first of pre. *)
  step. step. check "Hla".
  iAssert (∃ hb hreg, ⌜head_ptr (pre ++ mkPtr fb (Obj fb) :: post) = mkPtr hb (Obj hb) /\ 0 < hb /\
                                hb + 8 <= r_end hreg⌝ ∗ live hb hreg ∗
             (live hb hreg -∗ live fb freg ∗ [∗ list] g ∈ pre ++ post, stream_life g))%I
    with "[Hl Hlives]" as (hb hreg (Hhd & Hhb & Hhend)) "[Hhl Hback]".
  { destruct pre as [|g pre].
    - iExists fb, freg. iFrame "Hl". iSplit; [iPureIntro; split_and!; [reflexivity | lia | lia]|].
      iIntros "$". done.
    - cbn [app head_ptr big_opL]. iDestruct "Hlives" as "[(%gb & %greg & %Hg & Hgl) Hlives]".
      pose proof Hg as (-> & Hgb & _ & Hgend & _). unfold file_size in Hgend. iExists gb, greg. iFrame "Hgl".
      iSplit; [iPureIntro; split_and!; [reflexivity | lia | lia]|]. iIntros "Hgl". iFrame "Hl Hlives".
      iExists gb, greg. iFrame. done. }
  iApply (wp_live_fit1 w0 registry ge with "Hhl"). iIntros ([Hh0 Hh48]) "Hhl".
  iEval (rewrite Hhd) in "Hlah". load "Hla" "Hlah" "Hhl". iEval (rewrite -Hhd) in "Hlah".
  iDestruct ("Hback" with "Hhl") as "[Hl Hlives]". step. step. step. branch_as true.
  (* L185 to the return. *)
  iDestruct (unlink_split la lareg pre fb post Hlaal Hlaend with "Hla Hlah Hch Hlives")
    as (qb qo qreg Hq) "(Hql & Hqc & Hfp & Hfc & Hnx & HW)".
  destruct Hq as (Hqo & Hqal & Hqend).
  iAssert (lock_state lb lbreg 1 0 (ow_self w0)) with "[Hbl Hb0 Hb4 Hbo]" as "Hlb".
  { iFrame. iPureIntro. unfold int_bytes. split_and!; try lia. }
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done|]; iExact "Hfl"|].
  iApply (wp_unlink_L185 w0 registry ge Hreg Hext Hpop
            with "Hs Hl Hfl Hlp Hlb Hfp Hfc Hql Hqc Hnx Hrl Hrc Hlk Htcb Hcl Hc24 Hc16"); try close_side.
  iNext. iIntros "Hl Hfl Hlp Hlb Hfp Hfc Hql Hqc Hnx Hrl Hrc Hlk Htcb Hcl".
  iDestruct ("HW" with "Hql Hqc Hnx") as "(Hla & Hlah & Hch & Hlives)".
  iApply ("HK" with "Htcb Hl Hfl Hlp Hlb Hla Hlah Hch Hlk Hrl Hrc Hlives [Hfp Hfc]"). iExists _, _. iFrame.
Qed.

End rules.
