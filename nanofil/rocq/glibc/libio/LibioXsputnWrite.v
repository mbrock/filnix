(** The direct write of `c: _IO_new_file_xsputn` (LibioXsputnBase.v
    describes the function), from block `c: L132`, once the overflow
    has flushed the buffer:

    ```
    block = f->_IO_buf_end - f->_IO_buf_base;
    do_write = to_do - (block >= 128 ? to_do % block : 0);
    if (do_write)
      { count = new_do_write (f, s, do_write); ... }
    ```

    `c: new_do_write` is inlined: the stream is not appending, and its
    read end is its write base, so it neither resets `c: _offset` nor
    seeks; it hands the do_write bytes from s, the caller's bytes at
    their share, to the jump table's write ([fwq_spec]), finds
    `c: _cur_column` 0 and goes on at LibioXsputnReset.v's
    [wp_xs_L70]. With nothing to write directly, the rest goes to
    LibioXsputnBase.v's [wp_xs_L178]. *)

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
  LibioXsputnReset LibioXsputnCall LibioXsputnDo.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The size of the buffer nb, 0 when there is none. *)
Definition nb_size (nb : option (Z * Z)) : Z := match nb with Some (_, sz) => sz | None => 0 end.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioXsputnWriteOn (R : Runtime) (LG0 : LogicSig R).
Module XD := LibioXsputnDoOn R LG0.
Import XD XD.XC XD.XC.XR XD.XC.XR.XF XD.XC.XR.XF.XS XD.XC.XR.XF.XS.XB XD.XC.XR.XF.XS.XB.DX XD.XC.XR.XF.XS.XB.DX.RM XD.XC.XR.XF.XS.XB.DX.RM.SM.TL XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY
  XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.CS
  XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.ML XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.LG
  XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.L XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.OW XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI
  XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.ST.

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
Local Instance xs_write_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise, through the environment's puts. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** Block `c: L132` on, the overflow done, T of the n bytes left from
    s: the direct write of T less T modulo the buffer's size when that
    is at least 128, else of T, then the rest ([wp_xs_L168]). *)
Lemma wp_xs_L132 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys T e from Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> nb <> None ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= T <= n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk11") e = Some (WPtr (mkPtr (fb + off_vtable) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.5") e = Some (WInt T) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b' + so + (n - T)) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Enter (TAtom "L132") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Heb Hfb Hfal Hfend Hfreg Hnb Hc' Hb'0 Hb8' Hso Hyend Hyreg Hy HT Hv0 Hc0 Hc11 Hv4 Hp5 Hp1.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp ((Hrp & Hre & Hrb & Hwb & Hbb & Hbe) & Hwp & Hwe & Hroom) Hos Hl' Hys HK".
  iDestruct (wroom_cap with "Hroom") as (reg (Hb1 & Hb2 & Hcap)) "[Hbl Hroom]".
  iAssert (⌜ptr_addr (nb_end nb) - ptr_addr (nb_base nb) = nb_size nb /\ 0 <= nb_size nb < 2 ^ 63⌝)%I as %[Hsz Hszr].
  { destruct nb as [[b sz] |]; [|iPureIntro; cbn; lia].
    iDestruct ("Hroom" with "Hbl") as "(%reg0 & %xs & %cs & %Hok & _)". iPureIntro. cbn.
    destruct Hok as (H1 & H2 & H3 & H4 & H5 & _). lia. }
  fs. fs. fchk "Hl". iEval (rewrite -Hcap) in "Hbl". fldp "Hl" "Hbe" "Hbl". iEval (rewrite Hcap) in "Hbl".
  fs. fchk "Hl". fldp "Hl" "Hbb" "Hbl". fs. fs. fs. fs.
  replace ((ptr_addr (nb_end nb) mod 2 ^ 64 - ptr_addr (nb_base nb) mod 2 ^ 64) mod 2 ^ 64) with (nb_size nb)
    by (unwrap2; lia).
  iDestruct ("Hroom" with "Hbl") as "Hroom".
  pose proof (Z.mod_pos_bound T (nb_size nb)) as Hmb.
  destruct (Z_le_gt_dec 128 (nb_size nb)) as [Hbig | Hsmall].
  - (* L166: whole blocks. *)
    fbrv false. fs. fs. fs. fs.
    iApply (wp_xs_L168 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf Hfw Hfwq eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys T (T - T mod nb_size nb)
              with "Hvt Hl Hvtp [$Hrp $Hre $Hrb $Hwb $Hbb $Hbe $Hwp $Hwe $Hroom] Hos Hl' Hys HK"); try side.
    assert (Hml : T mod nb_size nb <= T) by (apply Z.mod_le; lia). specialize (Hmb ltac:(lia)).
    all: unfold n, off_buf_end, off_buf_base in *; try lia.
    all: lookups; try reflexivity. all: try (do 3 f_equal; unwrap2; lia).
    all: do 2 f_equal; unwrap2.
    all: unfold unsigned_division; destruct (nb_size nb =? 0) eqn:E; [apply Z.eqb_eq in E; lia|]; unwrap2; set (q := T mod nb_size nb) in *; lia.
  - (* L168 at once: everything. *)
    assert (Hs128 : nb_size nb < 128) by lia. clear Hsmall. fbrv true. fs.
    iApply (wp_xs_L168 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf Hfw Hfwq eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys T T
              with "Hvt Hl Hvtp [$Hrp $Hre $Hrb $Hwb $Hbb $Hbe $Hwp $Hwe $Hroom] Hos Hl' Hys HK"); try side.
    all: unfold n, off_buf_end, off_buf_base in *; try lia.
    all: lookups; try reflexivity. all: try (do 3 f_equal; unwrap2; lia). all: do 2 f_equal; lia.
Qed.

End rules.
End LibioXsputnWriteOn.
