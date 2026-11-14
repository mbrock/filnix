(** The small fill of `c: _IO_default_xsputn`'s loop
    (LibioGenCode.v), block `c: L50`, when at most 20 bytes go into the
    buffer: none, or one at a time by LibioDefaultXsputnBytes.v's
    [wp_dx_bytes]; then the round ends at `c: L22`
    (LibioDefaultXsputnTail.v's [wp_dx_L22]).
    LibioDefaultXsputnRoom.v's [wp_dx_L44] takes the other way. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioDoWriteCode LibioDefaultXsputnCopy LibioDefaultXsputnBuf
  LibioDefaultXsputnBytes LibioDefaultXsputnTail.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputnBuf LibioDefaultXsputnBytes LibioDefaultXsputnCopy LibioDefaultXsputnTail LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioDefaultXsputnTail LibioDefaultXsputnBytes LibioDefaultXsputnBuf LibioDefaultXsputnCopy SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance dx_small_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Block `c: L51` on, from any of its three predecessors, to
    [wp_dx_L22]: enter it, subtract the count, enter `c: L22`. *)
Ltac to_L22 := step; step; step; step.

(** A lookup premise of [wp_dx_L22], through the environment's puts. *)
Ltac lk_fin := lookups; first [reflexivity | do 2 f_equal; unwrap2; lia | do 3 f_equal; cbn [ptr_addr]; unwrap2; lia].
(** Block `c: L50` on, entered from `c: L44`: cnt bytes, at most 20,
    the t left and the room between the write pointer wa and end ea of
    the buffer b, copied from s one at a time, and the round finished
    at `c: L22`. *)
Lemma wp_dx_L50 os fb freg vb vreg b sz reg xs cs wa ea dq b' reg' so c' ys t cnt e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge os -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  room_ok b sz reg xs cs (mkPtr wa (Obj b)) (mkPtr ea (Obj b)) ->
  c' = Obj b' \/ c' = Ro b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= t <= n -> 0 <= cnt <= t -> cnt <= 20 -> wa + cnt <= ea ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.7") e = Some (WInt t) ->
  lookup (TAtom "pr.9") e = Some (WInt cnt) ->
  lookup (TAtom "pr.2") e = Some (WPtr (mkPtr (b' + (so + (n - t))) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wcells fb (Some (b, sz)) -∗ pcell fb off_write_ptr (mkPtr wa (Obj b)) -∗
  pcell fb off_write_end (mkPtr ea (Obj b)) -∗ live b reg -∗ bytes b 0 xs -∗ auxes b 0 cs -∗
  os fb (Some (b, sz)) -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ dx_loop w0 registry ge os fb freg vb vreg dq b' reg' so c' ys Φ -∗
  ▷ dx_post registry ge os fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_default_xsputn e [] None (Enter (TAtom "L50") (Some (TAtom "L44")))) : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Hfb Hfal Hfend Hfreg Hok Hc' Hb8' Hso Hyend Hyreg Hy Ht Hcnt Hsmall Hroom Hv0 Hc0 Hv4 Hp7 Hp9 Hp2.
  unfold file_size in Hfend.
  destruct Hok as (Hb0 & Hb8 & Hsz & Hbend & Hbreg & Hlx & Hlc & Hx & [_ Hwa] & [_ Hea] & Hheap). cbn in Hwa, Hea.
  iIntros "#Hvt Hl Hvtp Hwc Hwp Hwe Hbl Hxs Hcs Hos Hl' Hys IH HK".
  iApply (wp_live_fit w0 registry ge with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  step. step.
  destruct (Z.eq_dec cnt 0) as [-> | Hcn0].
  + (* None: L51 at once. *)
    branch_as true. to_L22.
    iAssert (wbuf fb (Some (b, sz)) (mkPtr wa (Obj b)) (mkPtr ea (Obj b))) with "[Hwc Hwp Hwe Hbl Hxs Hcs]" as "Hwb".
    { iFrame. iPureIntro. unfold room_ok, in_buf. cbn. split_and!; first [reflexivity | assumption | lia]. }
    iApply (wp_dx_L22 w0 registry ge os fb freg vb vreg (Some (b, sz)) (mkPtr wa (Obj b)) (mkPtr ea (Obj b))
              dq b' reg' so c' ys t with "Hvt Hl Hvtp Hwb Hos Hl' Hys IH HK"); try close_side.
    all: unfold n in *; first [intros _; discriminate | lk_fin].
  + (* L65: the byte loop. *)
    branch_as false. step. step. norm. load "Hl" "Hwp" "Hbl". step. step.
    iApply (wp_dx_bytes w0 registry ge fb freg b reg sz (wa - b) cnt dq b' reg' so c' ys (n - t)
              (mkPtr wa (Obj b)) with "[%] Hl Hwp Hbl Hxs Hl' Hys"); try close_side.
    { unfold n in *. split_and!; try (lookups; reflexivity); try lia.
      all: first [assumption | lia | lookups; do 3 f_equal; cbn [ptr_addr]; unfold raw_address; unwrap2; lia]. }
    iNext. iIntros (e' xs' (Hsame & Hp6 & Hlx' & Hx')) "Hl Hwp Hbl Hxs Hl' Hys".
    assert (Hv0' : lookup (TAtom "v0") e' = Some (WPtr (mkPtr fb (Obj fb)))) by (rewrite Hsame; [|reflexivity]; lookups; reflexivity).
    assert (Hc0' : lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb)))) by (rewrite Hsame; [|reflexivity]; lookups; reflexivity).
    assert (Hv4' : lookup (TAtom "v4") e' = Some (WInt n)) by (rewrite Hsame; [|reflexivity]; lookups; reflexivity).
    assert (Hp7' : lookup (TAtom "pr.7") e' = Some (WInt t)) by (rewrite Hsame; [|reflexivity]; lookups; reflexivity).
    assert (Hp9' : lookup (TAtom "pr.9") e' = Some (WInt cnt)) by (rewrite Hsame; [|reflexivity]; lookups; reflexivity).
    clear Hsame. to_L22.
    iAssert (wbuf fb (Some (b, sz)) (mkPtr (wa + cnt) (Obj b)) (mkPtr ea (Obj b)))
      with "[Hwc Hwp Hwe Hbl Hxs Hcs]" as "Hwb".
    { replace (b + (wa - b + cnt)) with (wa + cnt) by lia. iFrame. iPureIntro. unfold room_ok, in_buf. cbn.
      split_and!; first [reflexivity | assumption | lia]. }
    iApply (wp_dx_L22 w0 registry ge os fb freg vb vreg (Some (b, sz)) (mkPtr (wa + cnt) (Obj b))
              (mkPtr ea (Obj b)) dq b' reg' so c' ys (t - cnt) with "Hvt Hl Hvtp Hwb Hos Hl' Hys IH HK"); try close_side.
    all: unfold n in *; first [intros _; discriminate | lk_fin].
Qed.

End rules.
