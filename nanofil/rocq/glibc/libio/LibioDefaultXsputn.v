(** The triple of `c: _IO_default_xsputn(f, s, n)` (LibioGenCode.v),
    the generic string output of libio, which `c: _IO_new_file_xsputn`
    hands the bytes that are left once it has filled and flushed the
    buffer:

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

    The source is n bytes ys of an object b' owned at any share dq,
    such as a [word_string]'s, and is handed back. The stream is its
    life, its jump table pointer, its write side ([wbuf]) and a rest os
    that only the overflow reads; the overflow is
    `c: _IO_new_file_overflow` through the jump table, taken as the
    premise [overflow_spec]. The result is the count k of bytes the
    function wrote, at most n ([dx_post]): n when every overflow
    succeeded, fewer when one returned `c: EOF`.

    | Lemma | Part |
    |---|---|
    | [wp_dx_loop] | the loop's head, block `c: L16`, by Löb induction |
    | [wp_glibc__IO_default_xsputn] | the whole function |

    The fill is LibioDefaultXsputnRoom.v's, the end of a round
    LibioDefaultXsputnTail.v's. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioDoWriteCode LibioDefaultXsputnCopy LibioDefaultXsputnBuf
  LibioDefaultXsputnBytes LibioDefaultXsputnTail LibioDefaultXsputnRoom.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDefaultXsputnOn (R : Runtime) (LG0 : LogicSig R).
Module RM := LibioDefaultXsputnRoomOn R LG0.
Import RM RM.SM.TL RM.SM.TL.BY RM.SM.TL.BY.BF RM.SM.TL.BY.BF.CP RM.SM.TL.BY.BF.CP.CS RM.SM.TL.BY.BF.CP.SW
  RM.SM.TL.BY.BF.CP.SW.FI.ML RM.SM.TL.BY.BF.CP.SW.FI.LG RM.SM.TL.BY.BF.CP.SW.FI.L RM.SM.TL.BY.BF.CP.SW.OW
  RM.SM.TL.BY.BF.CP.SW.FI RM.SM.TL.BY.BF.CP.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The registry holds `c: zmemmove`'s contract, and the genv's
    `c: __GI_memcpy` and `c: __GI_mempcpy` are glibc's. *)
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None) (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  (Hcpy : find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy))
  (Hpcpy : find_fn ge (TAtom "__GI_mempcpy") = Some (Defined glibc_mempcpy)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance dx_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise of a block lemma, through the environment's puts. *)
Ltac lk_fin := lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_ptr; unwrap2; lia].

(** The loop's head, block `c: L16`, for every count left, by Löb
    induction: with no room, the round ends at once
    ([wp_dx_L22]); with room, it is filled ([wp_dx_L44]). *)
Lemma wp_dx_loop os fb freg vb vreg dq b' reg' so c' ys Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge os -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys ->
  vtables_ro ge vb vreg ⊢ dx_loop w0 registry ge os fb freg vb vreg dq b' reg' so c' ys Φ.
Proof.
  intros n Hov Hfo Hfb Hfal Hfend Hfreg Hc' Hb8' Hso Hyend Hyreg Hy. unfold file_size in Hfend.
  iIntros "#Hvt". iLöb as "IH". iEval (unfold dx_loop; cbv zeta).
  iIntros (e t nb wp we (Hv0 & Hv4 & Hp7 & Hp2 & Ht)) "Hl Hvtp Hwb Hos Hl' Hys HK".
  iDestruct "Hwb" as "(Hwc & Hwp & Hwe & Hroom)".
  iApply (wp_live_fit w0 registry ge with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  cbn [dx_L16 b_insts b_jump]. fs. fchk "Hl".
  destruct nb as [[b sz] |].
  - iDestruct "Hroom" as (reg xs cs Hok) "(Hbl & Hxs & Hcs)".
    pose proof Hok as (Hb0 & Hb8 & Hsz & Hbend & Hbreg & Hlx & Hlc & Hx & [Hwc' Hwa] & [Hec Hea] & Hheap).
    destruct wp as [wa wc], we as [ea ec]. cbn in Hwc', Hwa, Hec, Hea. subst wc ec.
    fldp "Hl" "Hwp" "Hbl". fs. fchk "Hl". fldp "Hl" "Hwe" "Hbl". fs. fs. fs.
    destruct (Z_lt_le_dec wa ea) as [Hlt | Hge].
    + (* L20: room for ea - wa bytes; the count is the smaller of it and t. *)
      fbrv false. fs. fs. norm. fldp "Hl" "Hwe" "Hbl". fs. fldp "Hl" "Hwp" "Hbl". fs. fs. fs. fs.
      destruct (Z_lt_le_dec t (ea - wa)) as [Htl | Htg].
      * fbrv false. fs.
        iApply (wp_dx_L44 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy os fb freg vb vreg b sz reg xs cs wa ea
                  dq b' reg' so c' ys t t with "Hvt Hl Hvtp Hwc Hwp Hwe Hbl Hxs Hcs Hos Hl' Hys IH HK"); try side.
        all: try lia. all: lk_fin.
      * fbrv true. fs. fs. fs.
        iApply (wp_dx_L44 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy os fb freg vb vreg b sz reg xs cs wa ea
                  dq b' reg' so c' ys t (ea - wa) with "Hvt Hl Hvtp Hwc Hwp Hwe Hbl Hxs Hcs Hos Hl' Hys IH HK");
          try side.
        all: try lia. all: lk_fin.
    + (* No room: L22. *)
      fbrv true. fs.
      iAssert (wbuf fb (Some (b, sz)) (mkPtr wa (Obj b)) (mkPtr ea (Obj b))) with "[Hwc Hwp Hwe Hbl Hxs Hcs]" as "Hwb".
      { iFrame. iPureIntro. exact Hok. }
      iApply (wp_dx_L22 w0 registry ge os fb freg vb vreg (Some (b, sz)) (mkPtr wa (Obj b)) (mkPtr ea (Obj b))
                dq b' reg' so c' ys t with "Hvt Hl Hvtp Hwb Hos Hl' Hys IH HK"); try side.
      all: lk_fin.
  - (* No buffer yet: both pointers null, no room; L22. *)
    iDestruct "Hroom" as %[-> ->].
    fldn "Hl" "Hwp". fs. fchk "Hl". fldn "Hl" "Hwe". fs. fs. fs. fbrv true. fs.
    iApply (wp_dx_L22 w0 registry ge os fb freg vb vreg None null null dq b' reg' so c' ys t
              with "Hvt Hl Hvtp [$Hwc $Hwp $Hwe //] Hos Hl' Hys IH HK"); try side.
    all: lk_fin.
Qed.

(** `c: _IO_default_xsputn(f, s, n)` of the n bytes ys from offset so
    of the object b', owned at the share dq: it writes k of them, at
    most n, into the stream's buffer or through the jump table's
    overflow, and hands the stream and the source back ([dx_post]). *)
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
Proof.
  intros n Hfr Hov Hfo Hfb Hfal Hfend Hfreg Hc' Hb8' Hso Hyend Hyreg Hy. injection Hfr as <-.
  iIntros "#Hvt Hl Hvtp Hwb Hos Hl' Hys HK".
  iApply (wp_live_fit w0 registry ge with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  fs. fs.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  - (* Nothing to write: L10 returns 0. *)
    fbrv false. fs. iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' Hys"). rewrite Zmod_0_l. lia.
  - fbrv true. fs.
    iPoseProof (wp_dx_loop os fb freg vb vreg dq b' reg' so c' ys Φ with "Hvt") as "Hloop"; try assumption.
    iEval (unfold dx_loop; cbv zeta) in "Hloop".
    iApply ("Hloop" $! _ n with "[%] Hl Hvtp Hwb Hos Hl' Hys HK").
    unfold n in *. split_and!; try lia. all: lk_fin.
Qed.

End rules.
End LibioDefaultXsputnOn.
