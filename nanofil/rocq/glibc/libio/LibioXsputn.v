(** The triple of `c: _IO_new_file_xsputn(f, s, n)`
    (LibioXsputnCode.v), the jump table's string output of a narrow
    stream; LibioXsputnBase.v gives its C, its stream ([wbuf], [xos])
    and its premises: the overflow ([overflow_spec]) and the write of
    bytes at a share ([fwq_spec]).

    [wp_glibc__IO_new_file_xsputn] returns 0 for no bytes, reads the
    flags, and takes the line-buffered count (LibioXsputnEnter.v's
    [wp_xs_L18]) when `c: _IO_LINE_BUF` and `c: _IO_CURRENTLY_PUTTING`
    are both set, else the count up to the write end ([wp_xs_L19]).

    | File | Blocks |
    |---|---|
    | LibioXsputnEnter.v | `c: L18` to `c: L73`, the count |
    | LibioXsputnFill.v | `c: L20` to `c: L101`, the copy |
    | LibioXsputnFlush.v | `c: L96` to `c: L146`, the overflow |
    | LibioXsputnWrite.v, LibioXsputnDo.v | `c: L132` to `c: L168`, the direct write's count |
    | LibioXsputnCall.v, LibioXsputnReset.v, LibioXsputnFlags.v, LibioXsputnSetp.v | `c: new_do_write` inlined |
    | LibioXsputnBase.v | the scan and `c: L178`, the rest to `c: _IO_default_xsputn` | *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioReadCode LibioDoWriteCode LibioXsputnCode LibioDefaultXsputnCopy
  LibioDefaultXsputnBuf LibioDefaultXsputnTail LibioDefaultXsputn LibioXsputnBase
  LibioXsputnSetp LibioXsputnFlags
  LibioXsputnReset LibioXsputnCall LibioXsputnDo
  LibioXsputnWrite LibioXsputnFlush
  LibioXsputnFill LibioXsputnEnter.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioXsputnOn (R : Runtime) (LG0 : LogicSig R).
Module XE := LibioXsputnEnterOn R LG0.
Import XE XE.XL XE.XL.XU XE.XL.XU.XW XE.XL.XU.XW.XD XE.XL.XU.XW.XD.XC XE.XL.XU.XW.XD.XC.XR XE.XL.XU.XW.XD.XC.XR.XF XE.XL.XU.XW.XD.XC.XR.XF.XS XE.XL.XU.XW.XD.XC.XR.XF.XS.XB XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY
  XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.CS
  XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.ML XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.LG
  XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.L XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.OW XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI
  XE.XL.XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The genv's copies and `c: __GI__IO_default_xsputn` are glibc's, as
    LibioXsputnBase.v asks. *)
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None) (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  (Hcpy : find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy))
  (Hpcpy : find_fn ge (TAtom "__GI_mempcpy") = Some (Defined glibc_mempcpy))
  (Hdxf : find_fn ge (TAtom "__GI__IO_default_xsputn") = Some (Defined glibc__IO_default_xsputn)).
(** The jump table's write is glibc's `c: _IO_new_file_write`, which
    writes bytes at a share ([fwq_spec]). *)
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write) (Hfwq : fwq_spec w0 registry ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance xs_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise, through the environment's puts. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** Rebuild the stream's rest [xos] from its flags Hfl and the other fields. *)
Ltac repack fl f2 fd tw off m eb X fb nb :=
  iAssert (xos w0 eb X fb nb) with "[Hfl Hrest HX]" as "Hos";
  [iFrame "HX"; iExists fl, f2, fd, tw, off, m; iFrame "Hrest"; iSplit; [done | iFrame "Hfl"; done] |].

(** `c: _IO_new_file_xsputn(f, s, n)` of the n bytes ys from offset so
    of b', at the share dq: the result r is `c: EOF` as a `c: size_t`
    or the count written, at most n, as [xs_post] says. *)
Lemma wp_glibc__IO_new_file_xsputn fr eb X fb freg vb vreg nb wp we dq b' reg' so c' ys Φ :
  let n := Z.of_nat (length ys) in
  call_frame glibc__IO_new_file_xsputn [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b' + so) c'); WInt n] = Some fr ->
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros n Hfr Hov Hfo Heb Hfb Hfal Hfend Hfreg Hc' Hb'0 Hb8' Hso Hyend Hyreg Hy. injection Hfr as <-.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp Hwb (Hxf & HX) Hl' Hys HK".
  fs. fs.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  { (* No bytes: L12 returns 0. *)
    fbrv false. fs. iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hvtp Hwb [$Hxf $HX] Hl' Hys"). right. rewrite Zmod_0_l. unfold n. lia. }
  fbrv true. fs.
  iDestruct "Hxf" as (fl f2 fd tw off m Hfs) "(Hfl & Hrest)". iDestruct "Hfl" as "[%Hfl32 Hfl]".
  assert (H512 : 0 <= Z.land fl 512 < 2 ^ 32) by (apply land_lt32; lia).
  assert (H2048 : 0 <= Z.land fl 2048 < 2 ^ 32) by (apply land_lt32; lia).
  fchk "Hl". fldi "Hl" "Hfl". fs.
  destruct (Z.land fl 512 =? 0) eqn:E512; [apply Z.eqb_eq in E512 | apply Z.eqb_neq in E512].
  - (* Not line-buffered: L25, then L19. *)
    fbrv true. fs. fbrv true. repack fl f2 fd tw off m eb X fb nb.
    iApply (wp_xs_L19 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf Hfw Hfwq eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK"); try side.
    all: unfold n in *; try lia. all: lk_fin.
  - (* L24: currently putting? *)
    fbrv false. fs. fldi "Hl" "Hfl". fs. fs. fs. fs.
    destruct (Z.land fl 2048 =? 0) eqn:E2048; [apply Z.eqb_eq in E2048 | apply Z.eqb_neq in E2048].
    + fbrv true. repack fl f2 fd tw off m eb X fb nb.
      iApply (wp_xs_L19 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf Hfw Hfwq eb X fb freg vb vreg nb wp we
                dq b' reg' so c' ys with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK"); try side.
      all: unfold n in *; try lia. all: lk_fin.
    + fbrv false. repack fl f2 fd tw off m eb X fb nb.
      iApply (wp_xs_L18 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf Hfw Hfwq eb X fb freg vb vreg nb wp we
                dq b' reg' so c' ys with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK"); try side.
      all: unfold n in *; try lia. all: lk_fin.
Qed.

End rules.
End LibioXsputnOn.
