From Glibc Require Import GlibcProgram.
(** The default stream writer fills available buffer space before trying
    to flush it. This module verifies the following part of its loop:

    ```
    size_t count = f->_IO_write_end - f->_IO_write_ptr;
    if (count > more)
      count = more;
    if (count > 20)
      { f->_IO_write_ptr = __mempcpy (f->_IO_write_ptr, s, count); s += count; }
    else if (count)
      ... the byte loop ...
    more -= count;
    ```

    The writer copies no more bytes than the available space permits.
    It calls mempcpy for copies larger than 20 bytes and uses a byte
    loop for smaller copies. Both paths update the write pointer and
    return to the main output loop with the remaining byte count. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioDoWriteCode LibioDefaultXsputnCopy LibioDefaultXsputnBuf
  LibioDefaultXsputnBytes LibioDefaultXsputnTail LibioDefaultXsputnSmall.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputnBuf LibioDefaultXsputnBytes LibioDefaultXsputnCopy LibioDefaultXsputnSmall LibioDefaultXsputnTail LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
From Glibc Require Import GlibcSpec.
From Glibc Require StringSpecs.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** This block begins the copy after the writer has chosen its byte count. *)
Definition dx_L44 : block := Eval vm_compute in
  match find_block (TAtom "L44") (fn_blocks glibc__IO_default_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L44") [] [] JRetVoid end.


Import LibioDefaultXsputnSmall LibioDefaultXsputnTail LibioDefaultXsputnBytes LibioDefaultXsputnBuf LibioDefaultXsputnCopy SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The registry holds `c: zmemmove`'s contract, and the genv's
    `c: __GI_memcpy` and `c: __GI_mempcpy` are glibc's. *)
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  `{Hcpy : !Defines ge "__GI_memcpy" glibc_memcpy}
  `{Hpcpy : !Defines ge "__GI_mempcpy" glibc_mempcpy}.


(** This abbreviation selects expressions in the caller's linked program. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** After either copy path, these steps subtract the copied count and reenter the output loop. *)
Ltac to_L22 := step; step; step; step.

(** This tactic checks that the updated environment records the remaining bytes and source pointer. *)
Ltac lk_fin := lookups; first [reflexivity | do 2 f_equal; unwrap2; lia | do 3 f_equal; cbn [ptr_addr]; unwrap2; lia].

(** The writer copies the chosen count into its buffer and completes one loop iteration.
    The count fits both the source and the available destination space. *)
Lemma wp_dx_L44 os fb freg vb vreg b sz reg xs cs wa ea dq b' reg' so c' ys t cnt e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge os -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  room_ok b sz reg xs cs (mkPtr wa (Obj b)) (mkPtr ea (Obj b)) ->
  c' = Obj b' \/ c' = Ro b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= t <= n -> 0 <= cnt <= t -> wa + cnt <= ea ->
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
  WP (ERun (mkFrame glibc__IO_default_xsputn e [] None (Exec (TAtom "L44") (b_insts dx_L44) (b_jump dx_L44)))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Hfb Hfal Hfend Hfreg Hok Hc' Hb8' Hso Hyend Hyreg Hy Ht Hcnt Hroom Hv0 Hc0 Hv4 Hp7 Hp9 Hp2.
  unfold file_size in Hfend.
  destruct Hok as (Hb0 & Hb8 & Hsz & Hbend & Hbreg & Hlx & Hlc & Hx & [_ Hwa] & [_ Hea] & Hheap). cbn in Hwa, Hea.
  iIntros "#Hvt Hl Hvtp Hwc Hwp Hwe Hbl Hxs Hcs Hos Hl' Hys IH HK".
  iApply (wp_live_fit with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  cbn [dx_L44 b_insts b_jump]. step.
  destruct (Z_le_gt_dec cnt 20) as [Hsmall | Hbig].
  - (* L50: at most 20 bytes. *)
    branch_as true.
    iApply (wp_dx_L50 os fb freg vb vreg b sz reg xs cs wa ea dq b' reg' so c' ys t cnt
              with "Hvt Hl Hvtp Hwc Hwp Hwe Hbl Hxs Hcs Hos Hl' Hys IH HK"); try close_side.
    unfold room_ok, in_buf. cbn. split_and!; first [reflexivity | assumption | lia].
  - (* L49: past 20 bytes, `c: __mempcpy`. *)
    assert (Hbig' : 20 < cnt) by lia. branch_as false. step. step. norm. load "Hl" "Hwp" "Hbl".
    set (ysub := take (Z.to_nat cnt) (drop (Z.to_nat (n - t)) ys)).
    assert (Hls : Z.of_nat (length ysub) = cnt).
    { unfold ysub. rewrite length_take_le; [lia|]. rewrite length_drop. lia. }
    iDestruct (bytesq_sub _ _ _ _ (Z.to_nat (n - t)) (Z.to_nat cnt) with "Hys") as "[Hsub Hysb]"; [lia|].
    call_spec with (inr (b, reg, wa - b, xs, cs, dq, b', reg', so + Z.of_nat (Z.to_nat (n - t)), c', ysub)).
    { cbn -[put]. lookups. rewrite Hls. unfold n in *. do 2 f_equal; [do 2 f_equal; lia|]. f_equal.
      - do 2 f_equal. cbn [ptr_addr]. lia.
      - f_equal. f_equal. f_equal. unwrap2. reflexivity. }
    { repeat split; try assumption; try lia. unfold ysub. apply Forall_take, Forall_drop. exact Hy. }
    iDestruct "Hpost" as "(-> & Hbl & Hbuf & Hl' & Hsub)".
    iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
    iDestruct ("Hysb" with "Hsub") as "Hys".
    iDestruct "Hbuf" as (xs' cs') "(%Hl3 & Hxs & Hcs)". cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
    check "Hl". store "Hl" "Hwp". step. step. to_L22.
    iAssert (wbuf fb (Some (b, sz)) (mkPtr (wa + cnt) (Obj b)) (mkPtr ea (Obj b)))
      with "[Hwc Hwp Hwe Hbl Hxs Hcs]" as "Hwb".
    { rewrite Hls. replace (b + (wa - b) + cnt) with (wa + cnt) by lia. iFrame. iPureIntro.
      unfold room_ok, in_buf. cbn. destruct Hl3 as (H1 & H2 & H3).
      split_and!; first [reflexivity | assumption | lia]. }
    iApply (wp_dx_L22 os fb freg vb vreg (Some (b, sz)) (mkPtr (wa + cnt) (Obj b))
              (mkPtr ea (Obj b)) dq b' reg' so c' ys (t - cnt) with "Hvt Hl Hvtp Hwb Hos Hl' Hys IH HK"); try close_side.
    all: unfold n in *; first [intros _; discriminate | lk_fin].
Qed.

End rules.
