(** The direct write of `c: _IO_new_file_xsputn` (LibioXsputnBase.v
    describes the function), from block `c: L168`, with do_write the
    count LibioXsputnWrite.v's [wp_xs_L132] computes:

    ```
    if (do_write)
      { count = new_do_write (f, s, do_write);
        to_do -= count;
        if (count < do_write) return n - to_do; }
    if (to_do) to_do -= _IO_default_xsputn (f, s + do_write, to_do);
    ```

    `c: new_do_write` is inlined (blocks `c: iw_2.*`). The stream is
    not appending, so `c: _offset` is not reset; its read end is its
    write base, as a flush leaves them, so no seek is made; the write
    goes through the jump table to `c: _IO_new_file_write` on the
    caller's bytes at their share ([fwq_spec]); `c: _cur_column` is 0,
    so `c: _IO_adjust_column` is not called; and LibioXsputnReset.v's
    [wp_xs_L70] resets the pointers. With nothing to write directly,
    LibioXsputnBase.v's [wp_xs_L178] hands the rest on. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioReadCode LibioDoWriteCode LibioXsputnCode LibioDefaultXsputnCopy
  LibioDefaultXsputnBuf LibioDefaultXsputnTail LibioDefaultXsputn LibioXsputnBase
  LibioXsputnSetp LibioXsputnFlags LibioXsputnReset LibioXsputnCall.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L168`, after its phi: the direct write's count. *)
Definition xs_L168 : block := Eval vm_compute in
  match find_block (TAtom "L168") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L168") [] [] JRetVoid end.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioXsputnDoOn (R : Runtime) (LG0 : LogicSig R).
Module XC := LibioXsputnCallOn R LG0.
Import XC XC.XR XC.XR.XF XC.XR.XF.XS XC.XR.XF.XS.XB XC.XR.XF.XS.XB.DX XC.XR.XF.XS.XB.DX.RM XC.XR.XF.XS.XB.DX.RM.SM.TL XC.XR.XF.XS.XB.DX.RM.SM.TL.BY
  XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.CS
  XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.ML XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.LG
  XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.L XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.OW XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI
  XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.ST.

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
Local Instance xs_do_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise, through the environment's puts. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** Block `c: L168` on, the overflow done, T of the n bytes left
    from s, d of them to write directly: the write of the d bytes
    through the jump table, then the rest. *)
Lemma wp_xs_L168 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys T d e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= d <= T -> T <= n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk11") e = Some (WPtr (mkPtr (fb + off_vtable) (Obj fb))) ->
  lookup (TAtom "chk14") e = Some (WPtr (mkPtr (fb + off_buf_end) (Obj fb))) ->
  lookup (TAtom "chk15") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.5") e = Some (WInt T) ->
  lookup (TAtom "v174") e = Some (WInt (T - d)) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b' + so + (n - T)) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Exec (TAtom "L168") (b_insts xs_L168) (b_jump xs_L168)))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Heb Hfb Hfal Hfend Hfreg Hc' Hb'0 Hb8' Hso Hyend Hyreg Hy Hd HT
    Hv0 Hc0 Hc11 Hc14 Hc15 Hv4 Hp5 Hv174 Hp1.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp Hwbf Hos Hl' Hys HK".
  cbn [xs_L168 b_insts b_jump]. fs. fs.
  destruct (Z.eq_dec d 0) as [-> | Hd0].
  { (* Nothing to write directly: L178 on the T left. *)
    fbrv true. fs.
    iApply (wp_xs_L178 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys T 0 with "Hvt Hl Hvtp Hwbf Hos Hl' Hys HK"); try side.
    all: unfold n in *; try lia. all: lk_fin. }
  fbrv false. fs.
  iDestruct "Hwbf" as "((Hrp & Hre & Hrb & Hwb & Hbb & Hbe) & Hwp & Hwe & Hroom)".
  iDestruct (wroom_cap with "Hroom") as (reg (Hb1 & Hb2 & Hcap)) "[Hbl Hroom]".
  iDestruct "Hos" as "(Hxf & HX)".
  iDestruct "Hxf" as (fl f2 fd tw off m (Happ & Hf2 & Hfd & Hm & Hflags & Hfd31 & Hf2160)) "(Hfl & Hfl2 & Hfdc & Htw & Hoff & Hcol & Hmode & Herr)".
  iDestruct "Hfl" as "[%Hfl32 Hfl]". iDestruct "Hfl2" as "[%Hf2r Hfl2]".
  (* iw_2.start: not appending. *)
  fchk "Hl". fldi "Hl" "Hfl". fs. unfold io_is_appending in Happ. fbrv true.
  (* iw_2.L8: the read end is the write base. *)
  fs. fs. fldp "Hl" "Hre" "Hbl". fs. fldp "Hl" "Hwb" "Hbl". fs. fs. fs. fbrv true.
  iDestruct ("Hroom" with "Hbl") as "Hroom".
  iApply (wp_xs_L9 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf Hfw Hfwq eb X fb freg vb vreg nb wp we
            dq b' reg' so c' ys T d fl f2 fd tw off m with "Hvt Hl Hvtp [$Hrp $Hre $Hrb $Hwb $Hbb $Hbe $Hwp $Hwe $Hroom]
            [$Hfl //] [$Hfl2 //] Hfdc Htw Hoff Hcol Hmode Herr HX Hl' Hys HK"); try side.
  all: unfold n in *; try lia. all: lk_fin.
Qed.

End rules.
End LibioXsputnDoOn.
