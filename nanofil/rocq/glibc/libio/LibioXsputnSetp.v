(** The end of `c: new_do_write` inlined in `c: _IO_new_file_xsputn`
    (LibioXsputnBase.v describes the function), from block
    `c: iw_2.L70`, once the jump table's write returned r of the
    do_write bytes asked:

    ```
    _IO_setg (fp, fp->_IO_buf_base, fp->_IO_buf_base, fp->_IO_buf_base);
    fp->_IO_write_base = fp->_IO_write_ptr = fp->_IO_buf_base;
    fp->_IO_write_end = (fp->_mode <= 0 && (fp->_flags & (_IO_LINE_BUF | _IO_UNBUFFERED))
                         ? fp->_IO_buf_base : fp->_IO_buf_end);
    ...
    to_do -= count;
    if (count < do_write) return n - to_do;
    ```

    LibioXsputnReset.v's [wp_xs_L70] stores the six pointers, every
    read and write pointer the buffer's base and the write end its base
    or end, which keeps [wbuf] ([wroom_reset]); here [wp_xs_L117]
    stores the write end and returns, or goes on at `c: L178`
    (LibioXsputnBase.v's [wp_xs_L178]) when all do_write bytes
    went. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioReadCode LibioDoWriteCode LibioXsputnCode LibioDefaultXsputnCopy
  LibioDefaultXsputnBuf LibioDefaultXsputnTail LibioDefaultXsputn LibioXsputnBase.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: iw_2.L117`, after its phi: the new write end. *)
Definition xs_L117 : block := Eval vm_compute in
  match find_block (TAtom "iw_2.L117") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "iw_2.L117") [] [] JRetVoid end.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioXsputnSetpOn (R : Runtime) (LG0 : LogicSig R).
Module XB := LibioXsputnBaseOn R LG0.
Import XB XB.DX XB.DX.RM XB.DX.RM.SM.TL XB.DX.RM.SM.TL.BY XB.DX.RM.SM.TL.BY.BF XB.DX.RM.SM.TL.BY.BF.CP
  XB.DX.RM.SM.TL.BY.BF.CP.CS XB.DX.RM.SM.TL.BY.BF.CP.SW XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.ML
  XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.LG XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.L XB.DX.RM.SM.TL.BY.BF.CP.SW.OW
  XB.DX.RM.SM.TL.BY.BF.CP.SW.FI XB.DX.RM.SM.TL.BY.BF.CP.SW.ST.

(** A buffer whose write pointer becomes its base and write end its
    base or end is still [wroom]'s. *)
Lemma wroom_reset `{!gen_heapGS piece pval Σ} nb wp we we' :
  we' = nb_base nb \/ we' = nb_end nb -> wroom nb wp we ⊢ wroom nb (nb_base nb) we'.
Proof.
  intros Hwe. destruct nb as [[b sz] |]; cbn.
  - iIntros "(%reg & %xs & %cs & %Hok & H)". iExists reg, xs, cs. iFrame. iPureIntro.
    unfold room_ok, in_buf in *. cbn in Hwe. destruct Hok as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _ & _ & Hheap).
    destruct Hwe as [-> | ->]; cbn; split_and!; first [assumption | reflexivity | lia].
  - iIntros "_". cbn in Hwe. iPureIntro. destruct Hwe as [-> | ->]; split; reflexivity.
Qed.

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

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance xs_setp_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise, through the environment's puts. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** Block `c: iw_2.L117` on, after its phi we': the write end stored,
    and r of the d bytes written of the T left: the return of
    n - (T - r) when r < d, else `c: L178` on the T - d left. *)
Lemma wp_xs_L117 eb X fb freg vb vreg nb we we' dq b' reg' so c' ys T d r e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= r <= d -> 0 < d <= T -> T <= n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "iw_2.v114") e = Some (WPtr (mkPtr (fb + off_write_end) (Obj fb))) ->
  lookup (TAtom "iw_2.v136") e = Some (WPtr we') ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.5") e = Some (WInt T) ->
  lookup (TAtom "iw_2.v67") e = Some (WInt r) -> lookup (TAtom "v175") e = Some (WInt d) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b' + so + (n - T)) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wcells fb nb -∗ pcell fb off_write_ptr (nb_base nb) -∗ pcell fb off_write_end we -∗
  wroom nb (nb_base nb) we' -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Exec (TAtom "iw_2.L117") (b_insts xs_L117) (b_jump xs_L117)))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Hfb Hfal Hfend Hfreg Hc' Hb8' Hso Hyend Hyreg Hy Hr Hd HT Hv0 Hc0 Hv114 Hv136 Hv4 Hp5 Hv67 Hv175 Hp1.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp Hwc Hwp Hwe Hroom Hos Hl' Hys HK".
  iApply (wp_live_fit w0 registry ge with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  cbn [xs_L117 b_insts b_jump]. fchk "Hl". fstp "Hl" "Hwe". fs. fs. fs. fs.
  iAssert (wbuf fb nb (nb_base nb) we') with "[Hwc Hwp Hwe Hroom]" as "Hwb"; [iFrame|].
  destruct (Z.eq_dec r d) as [-> | Hrd].
  - (* All went: L178 on the T - d left. *)
    fbrv true. fs.
    iApply (wp_xs_L178 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf eb X fb freg vb vreg nb (nb_base nb) we'
              dq b' reg' so c' ys (T - d) d with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK"); try side.
    all: unfold n in *; try lia. all: lk_fin.
  - (* Fewer: L188 returns n - (T - r). *)
    fbrv false. fs. fs. iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' Hys"). unwrap2. lia.
Qed.

End rules.
End LibioXsputnSetpOn.
