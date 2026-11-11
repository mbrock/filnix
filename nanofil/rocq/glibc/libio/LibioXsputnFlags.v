(** The flags' test of `c: new_do_write` inlined in
    `c: _IO_new_file_xsputn` (LibioXsputnBase.v describes the
    function), block `c: iw_2.L122`: once the mode is narrow, the
    write end is the buffer's base when `c: _flags` has
    `c: _IO_LINE_BUF` or `c: _IO_UNBUFFERED` (514), else its end
    ([wp_xs_L122]), and LibioXsputnSetp.v's [wp_xs_L117] stores it.
    The proof is one for every buffer, none or a heap object, through
    the life its base's capability names ([wroom_cap]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioReadCode LibioDoWriteCode LibioXsputnCode LibioDefaultXsputnCopy
  LibioDefaultXsputnBuf LibioDefaultXsputnTail LibioDefaultXsputn LibioXsputnBase
  LibioXsputnSetp.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: iw_2.L122`: the flags' test. *)
Definition xs_L122 : block := Eval vm_compute in
  match find_block (TAtom "iw_2.L122") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "iw_2.L122") [] [] JRetVoid end.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioXsputnFlagsOn (R : Runtime) (LG0 : LogicSig R).
Module XS := LibioXsputnSetpOn R LG0.
Import XS XS.XB XS.XB.DX XS.XB.DX.RM XS.XB.DX.RM.SM.TL XS.XB.DX.RM.SM.TL.BY XS.XB.DX.RM.SM.TL.BY.BF
  XS.XB.DX.RM.SM.TL.BY.BF.CP XS.XB.DX.RM.SM.TL.BY.BF.CP.CS XS.XB.DX.RM.SM.TL.BY.BF.CP.SW
  XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.ML XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.LG XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.L
  XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.OW XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.ST.

(** The life of a stream's buffer, as the capability of its base
    names it: the heap object's, or nothing when there is no buffer;
    its base and end are addresses and share that capability. *)
Lemma wroom_cap `{!gen_heapGS piece pval Σ} nb wp we :
  wroom nb wp we ⊢ ∃ reg, ⌜0 <= ptr_addr (nb_base nb) < 2 ^ 64 /\ 0 <= ptr_addr (nb_end nb) < 2 ^ 64 /\
    ptr_cap (nb_end nb) = ptr_cap (nb_base nb)⌝ ∗ live_cap (ptr_cap (nb_base nb)) reg ∗
    (live_cap (ptr_cap (nb_base nb)) reg -∗ wroom nb wp we).
Proof.
  destruct nb as [[b sz] |]; cbn.
  - iIntros "(%reg & %xs & %cs & %Hok & Hl & H)". iExists reg. iFrame "Hl".
    pose proof Hok as (H1 & H2 & H3 & H4 & H5 & _). iSplit; [iPureIntro; split_and!; first [reflexivity | lia]|].
    iIntros "Hl". iExists reg, xs, cs. iFrame. iPureIntro. exact Hok.
  - iIntros "H". iExists (mkRegion 0 0 Heap Live). iSplit; [iPureIntro; split_and!; first [reflexivity | lia]|].
    iSplit; [done|]. iIntros "_". iExact "H".
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
Local Instance xs_flags_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise, through the environment's puts. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** [wp_xs_L117] after the write end's load, its resources named. *)
Ltac to117 fb nb :=
  iAssert (wcells fb nb) with "[Hrp Hre Hrb Hwb Hbb Hbe]" as "Hwc"; [iFrame |];
  iApply (wp_xs_L117 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf with "Hvt Hl Hvtp Hwc Hwp Hwe Hroom Hos Hl' Hys HK"); try side; lk_fin.

(** Block `c: iw_2.L122` on, the narrow mode passed, the read and
    write pointers the buffer's base: the flags' test of
    `c: _IO_LINE_BUF | _IO_UNBUFFERED` takes the write end, the base
    or the end ([wroom_reset]), and [wp_xs_L117] goes on. *)
Lemma wp_xs_L122 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys T d r fl f2 fd tw off m e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= r <= d -> 0 < d <= T -> T <= n ->
  Z.land fl io_is_appending = 0 -> Z.land f2 2 = 0 -> In fd (ow_fds w0) -> m = 0 \/ m = 2 ^ 32 - 1 ->
  xs_flags nb fl -> 0 <= fd < 2 ^ 31 -> Z.land f2 160 = 0 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk14") e = Some (WPtr (mkPtr (fb + off_buf_end) (Obj fb))) ->
  lookup (TAtom "chk15") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  lookup (TAtom "iw_2.v114") e = Some (WPtr (mkPtr (fb + off_write_end) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.5") e = Some (WInt T) ->
  lookup (TAtom "iw_2.v67") e = Some (WInt r) -> lookup (TAtom "v175") e = Some (WInt d) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b' + so + (n - T)) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb off_read_ptr (nb_base nb) -∗ pcell fb 16 (nb_base nb) -∗ pcell fb 24 (nb_base nb) -∗
  pcell fb off_write_base (nb_base nb) -∗ pcell fb off_buf_base (nb_base nb) -∗ pcell fb off_buf_end (nb_end nb) -∗
  pcell fb off_write_ptr (nb_base nb) -∗ pcell fb off_write_end we -∗ wroom nb wp we -∗
  int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ bytes fb off_column [0; 0] -∗
  int_cell fb off_mode m -∗ errno_any eb -∗ X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Enter (TAtom "iw_2.L122") (Some (TAtom "iw_2.L70"))))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Hfb Hfal Hfend Hfreg Hc' Hb8' Hso Hyend Hyreg Hy Hr Hd HT Happ Hf2 Hfd Hm Hflags Hfd31 Hf2160
    Hv0 Hc0 Hc14 Hc15 Hv114 Hv4 Hp5 Hv67 Hv175 Hp1.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp Hrp Hre Hrb Hwb Hbb Hbe Hwp Hwe Hroom Hfl Hfl2 Hfdc Htw Hoff Hcol Hmode Herr HX Hl' Hys HK".
  iDestruct (wroom_cap with "Hroom") as (reg (Hb1 & Hb2 & Hcap)) "[Hbl Hroom]".
  iDestruct "Hfl" as "[%Hfl32 Hfl]".
  fs. fchk "Hl". fldi "Hl" "Hfl". fs. fs. fs. fs.
  iAssert (xos w0 eb X fb nb) with "[Hfl Hfl2 Hfdc Htw Hoff Hcol Hmode Herr HX]" as "Hos".
  { iFrame "HX". iExists fl, f2, fd, tw, off, m. iFrame. iPureIntro. split_and!; first [assumption | lia]. }
  assert (Hm514 : 0 <= Z.land fl 514 < 2 ^ 32) by (apply land_lt32; lia).
  destruct (Z.land fl 514 =? 0) eqn:E514; [apply Z.eqb_eq in E514 | apply Z.eqb_neq in E514].
  - (* L116: the buffer's end. *)
    fbrv true. clear E514 Hm514. fs. fs. fchk "Hl".
    iEval (rewrite -Hcap) in "Hbl". fldp "Hl" "Hbe" "Hbl". iEval (rewrite Hcap) in "Hbl". fs. fs.
    iDestruct ("Hroom" with "Hbl") as "Hroom".
    iDestruct (wroom_reset nb wp we (nb_end nb) with "Hroom") as "Hroom"; [right; reflexivity|].
    to117 fb nb.
  - (* L115: the buffer's base. *)
    fbrv false. clear E514 Hm514. fs. fs. fchk "Hl". fldp "Hl" "Hbb" "Hbl". fs. fs.
    iDestruct ("Hroom" with "Hbl") as "Hroom".
    iDestruct (wroom_reset nb wp we (nb_base nb) with "Hroom") as "Hroom"; [left; reflexivity|].
    to117 fb nb.
Qed.

End rules.
End LibioXsputnFlagsOn.
