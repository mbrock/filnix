From Glibc Require Import GlibcProgram.
(** Generic string output fills the stream buffer and sends remaining bytes through its overflow function.
    The file-specific output function uses this loop after filling and flushing its own buffer.

    ```
    more = n;
    for (;;)
      {
        if (f->_IO_write_ptr < f->_IO_write_end)
          { fill the room, at most more bytes; more -= count; }
        if (more == 0 || _IO_OVERFLOW (f, (unsigned char) *s++) == EOF)
          break;
        more--;
      }
    return n - more;
    ```

    The caller lends an [[separation-logic|ownership share]] of the source and receives it back unchanged.
    The stream owns its write buffer, jump table pointer and fields needed by overflow.
    Output returns the number of bytes written, which may be short when an overflow fails.

    The loop proof joins the existing buffer-fill and end-of-round proofs.
    The named contract exposes the resulting stream state without its internal execution frames. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioDoWriteCode LibioDefaultXsputnCopy LibioDefaultXsputnBuf
  LibioDefaultXsputnBytes LibioDefaultXsputnTail LibioDefaultXsputnRoom.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputnBuf LibioDefaultXsputnBytes LibioDefaultXsputnCopy LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
From Glibc Require Import GlibcSpec LibioStreamSpecs.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioDefaultXsputnBytes LibioDefaultXsputnBuf LibioDefaultXsputnCopy SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

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


(** The expression type uses this caller's linked program and registry. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Environment lookups recover the values preserved across the loop's local assignments. *)
Ltac lk_fin := lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_ptr; unwrap2; lia].

(** Each loop iteration fills available room and then handles any remaining byte through overflow.
    [[later-modality|Löb induction]] supplies the continuation for the next iteration. *)
Lemma wp_dx_loop os fb freg vb vreg dq b' reg' so c' ys Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge os -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys ->
  vtables_ro ge vb vreg ⊢ dx_loop w0 registry ge os fb freg vb vreg dq b' reg' so c' ys Φ.
Proof using Type*.
  intros n Hov Hfo Hfb Hfal Hfend Hfreg Hc' Hb8' Hso Hyend Hyreg Hy. unfold file_size in Hfend.
  iIntros "#Hvt". iLöb as "IH". iEval (unfold dx_loop; cbv zeta).
  iIntros (e t nb wp we (Hv0 & Hv4 & Hp7 & Hp2 & Ht & Hprogress)) "Hl Hvtp Hwb Hos Hl' Hys HK".
  iDestruct "Hwb" as "(Hwc & Hwp & Hwe & Hroom)".
  iApply (wp_live_fit with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  cbn [dx_L16 b_insts b_jump]. step. check "Hl".
  destruct nb as [[b sz] |].
  - iDestruct "Hroom" as (reg xs cs Hok) "(Hbl & Hxs & Hcs)".
    pose proof Hok as (Hb0 & Hb8 & Hsz & Hbend & Hbreg & Hlx & Hlc & Hx & [Hwc' Hwa] & [Hec Hea] & Hheap).
    destruct wp as [wa wc], we as [ea ec]. cbn in Hwc', Hwa, Hec, Hea. subst wc ec.
    load "Hl" "Hwp" "Hbl". step. check "Hl". load "Hl" "Hwe" "Hbl". step. step. step.
    destruct (Z_lt_le_dec wa ea) as [Hlt | Hge].
    + (* L20: room for ea - wa bytes; the count is the smaller of it and t. *)
      branch_as false. step. step. norm. load "Hl" "Hwe" "Hbl". step. load "Hl" "Hwp" "Hbl". step. step. step. step.
      destruct (Z_lt_le_dec t (ea - wa)) as [Htl | Htg].
      * branch_as false. step.
        iApply (wp_dx_L44 Hmove Hmove_fn Hmove_sym os fb freg vb vreg b sz reg xs cs wa ea
                  dq b' reg' so c' ys t t with "Hvt Hl Hvtp Hwc Hwp Hwe Hbl Hxs Hcs Hos Hl' Hys IH HK"); try close_side.
        all: try lia. all: lk_fin.
      * branch_as true. step. step. step.
        iApply (wp_dx_L44 Hmove Hmove_fn Hmove_sym os fb freg vb vreg b sz reg xs cs wa ea
                  dq b' reg' so c' ys t (ea - wa) with "Hvt Hl Hvtp Hwc Hwp Hwe Hbl Hxs Hcs Hos Hl' Hys IH HK");
          try close_side.
        all: try lia. all: lk_fin.
    + (* No room: L22. *)
      branch_as true. step.
      iAssert (wbuf fb (Some (b, sz)) (mkPtr wa (Obj b)) (mkPtr ea (Obj b))) with "[Hwc Hwp Hwe Hbl Hxs Hcs]" as "Hwb".
      { iFrame "Hwc Hwp Hwe Hbl Hxs Hcs". iPureIntro. exact Hok. }
      iApply (wp_dx_L22 os fb freg vb vreg (Some (b, sz)) (mkPtr wa (Obj b)) (mkPtr ea (Obj b))
                dq b' reg' so c' ys t with "Hvt Hl Hvtp Hwb Hos Hl' Hys IH HK"); try close_side.
      all: first [intros _; discriminate | lk_fin].
  - (* No buffer yet: both pointers null, no room; L22. *)
    iDestruct "Hroom" as %[-> ->].
    load_null "Hl" "Hwp". step. check "Hl". load_null "Hl" "Hwe". step. step. step. branch_as true. step.
    iApply (wp_dx_L22 os fb freg vb vreg None null null dq b' reg' so c' ys t
              with "Hvt Hl Hvtp [$Hwc $Hwp $Hwe //] Hos Hl' Hys IH HK"); try close_side.
    all: lk_fin.
Qed.

(** Generic string output writes at most the requested number of bytes.
    Its result returns the updated stream together with the borrowed source memory. *)
Lemma wp_glibc__IO_default_xsputn fr os fb freg vb vreg nb wp we dq b' reg' so c' ys Φ :
  let n := Z.of_nat (length ys) in
  call_frame glibc__IO_default_xsputn [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b' + so) c'); WInt n] = Some fr ->
  overflow_spec w0 registry ge os -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ os fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ dx_post registry ge os fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type*.
  intros n Hfr Hov Hfo Hfb Hfal Hfend Hfreg Hc' Hb8' Hso Hyend Hyreg Hy. injection Hfr as <-.
  iIntros "#Hvt Hl Hvtp Hwb Hos Hl' Hys HK".
  iApply (wp_live_fit with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  step. step.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  - (* Nothing to write: L10 returns 0. *)
    branch_as false. step. iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' Hys"). rewrite Zmod_0_l. split; lia.
  - branch_as true. step.
    iPoseProof (wp_dx_loop os fb freg vb vreg dq b' reg' so c' ys Φ with "Hvt") as "Hloop"; try assumption.
    iEval (unfold dx_loop; cbv zeta) in "Hloop".
    iApply ("Hloop" $! _ n with "[%] Hl Hvtp Hwb Hos Hl' Hys HK").
    unfold n in *. split_and!; try lia. all: lk_fin.
Qed.

(** A linked generic output function provides the stream-and-source contract. *)
#[global] Instance default_xsputn_has_spec g `{!Defines ge g glibc__IO_default_xsputn} :
  HasSpec registry (os_wi w0) ge (TAtom g) default_xsputn_spec.
Proof using Type*.
  intros [[[[[[[[[[[[[os fb] freg] vb] vreg] nb] wp] we] dq] b] reg] so] c] ys].
  exists glibc__IO_default_xsputn. split; [apply defines|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  cbn [fs_pre fs_post default_xsputn_spec].
  iIntros "(%Hpre & #Hvt & Hl & Hvtp & Hwb & Hos & Hl' & Hys) HK".
  destruct Hpre as (Hov & Hfo & Hfb & Hal & Hend & Hfreg & Hcap & Hb8 & Hso & Hysend & Hreg & Hys).
  iApply (wp_glibc__IO_default_xsputn with "Hvt Hl Hvtp Hwb Hos Hl' Hys"); try eassumption.
  { cbn [fs_args default_xsputn_spec] in Hfr. exact Hfr. }
  iNext. iIntros (k nb' wp' we' Hk) "Hl Hvtp Hwb Hos Hl' Hys".
  iApply "HK". iExists k, nb', wp', we'. iFrame "Hl Hvtp Hwb Hos Hl' Hys". iPureIntro. tauto.
Qed.

End rules.
