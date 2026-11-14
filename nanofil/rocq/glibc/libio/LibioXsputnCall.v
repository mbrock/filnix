From Glibc Require Import GlibcProgram.
(** The jump table's write in the `c: new_do_write` inlined in
    `c: _IO_new_file_xsputn` (LibioXsputnDo.v describes it), from
    block `c: iw_2.L9`:

    ```
    count = _IO_SYSWRITE (fp, data, to_do);
    if (fp->_cur_column && count)
      fp->_cur_column = _IO_adjust_column (fp->_cur_column - 1, data, count) + 1;
    ```

    The jump table is checked against `c: __io_vtables`, its write
    slot is `c: _IO_new_file_write`, which takes the d bytes from s at
    their share ([fwq_spec]), and `c: _cur_column` is 0; then
    LibioXsputnReset.v's [wp_xs_L70] goes on. *)

From Glibc Require Import GlibcTactics LibioTactics.
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
  LibioXsputnReset.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputn LibioDefaultXsputnBuf LibioDefaultXsputnBytes LibioDefaultXsputnCopy LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioLogic LibioXsputnBase LibioXsputnFlags LibioXsputnReset LibioXsputnSetp OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Setting `c: _IO_ERR_SEEN` keeps `c: _IO_IS_APPENDING` clear. *)
Lemma land_err_seen fl : Z.land fl io_is_appending = 0 -> Z.land (Z.lor fl io_err_seen) io_is_appending = 0.
Proof. intros H. rewrite Z.land_lor_distr_l H. reflexivity. Qed.


Import LibioXsputnReset LibioXsputnFlags LibioXsputnSetp LibioXsputnBase LibioDefaultXsputn LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioDefaultXsputnBytes LibioDefaultXsputnBuf LibioDefaultXsputnCopy SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The genv's copies and `c: __GI__IO_default_xsputn` are glibc's, as
    LibioXsputnBase.v asks. *)
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  `{Hcpy : !Defines ge "__GI_memcpy" glibc_memcpy}
  `{Hpcpy : !Defines ge "__GI_mempcpy" glibc_mempcpy}
  `{Hdxf : !Defines ge "__GI__IO_default_xsputn" glibc__IO_default_xsputn}.
(** The jump table's write is glibc's `c: _IO_new_file_write`, which
    writes bytes at a share ([fwq_spec]). *)
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hfwq : fwq_spec w0 registry ge).


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise, through the environment's puts. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** Block `c: iw_2.L9` on, the stream's fields apart: the write of
    the d bytes from s, of the T left, through the jump table. *)
Lemma wp_xs_L9 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys T d fl f2 fd tw off m e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> nb <> None ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 < d <= T -> T <= n ->
  Z.land fl io_is_appending = 0 -> Z.land f2 2 = 0 -> In fd (ow_fds w0) -> m = 0 \/ m = 2 ^ 32 - 1 ->
  xs_flags nb fl -> 0 <= fd < 2 ^ 31 -> Z.land f2 160 = 0 ->
  0 <= fl < 2 ^ 32 -> 0 <= f2 < 2 ^ 32 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk11") e = Some (WPtr (mkPtr (fb + off_vtable) (Obj fb))) ->
  lookup (TAtom "chk14") e = Some (WPtr (mkPtr (fb + off_buf_end) (Obj fb))) ->
  lookup (TAtom "chk15") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.5") e = Some (WInt T) ->
  lookup (TAtom "v175") e = Some (WInt d) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b' + so + (n - T)) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ bytes fb off_column [0; 0] -∗
  int_cell fb off_mode m -∗ errno_any eb -∗ X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Enter (TAtom "iw_2.L9") (Some (TAtom "iw_2.L8"))))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Heb Hfb Hfal Hfend Hfreg Hnb Hc' Hb'0 Hb8' Hso Hyend Hyreg Hy Hd HT Happ Hf2 Hfd Hm Hflags Hfd31 Hf2160 Hfl32 Hf2r
    Hv0 Hc0 Hc11 Hc14 Hc15 Hv4 Hp5 Hv175 Hp1.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp Hwbf Hfl Hfl2 Hfdc Htw Hoff Hcol Hmode Herr HX Hl' Hys HK".
  (* iw_2.L9: the jump table, checked against `c: __io_vtables`. *)
  iPoseProof (vtables_slot ge vb vreg slot_write "_IO_new_file_write" with "Hvt") as "#Hsw"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_write")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfw). done. }
  iPoseProof "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)".
  unfold io_vtables_size in Hvend.
  step. step. norm. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true.
  (* iw_2.iw_2.join: the write slot and the call. *)
  step. step. norm.
  check_read_dq "Hvl'" by ar.
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsw Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hfw) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfw) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfw) | apply (ge_fn_check _ _ _ Hfw) | vx |
    apply (ge_fn_find _ _ _ Hfw) | reflexivity | reflexivity |].
  iNext.
  set (j := Z.to_nat (n - T)).
  iDestruct (bytesq_sub _ _ _ _ j (Z.to_nat d) with "Hys") as "[Hsub Hysb]"; [lia|].
  set (zs := take (Z.to_nat d) (drop j ys)).
  assert (Hlz : Z.of_nat (length zs) = d) by (unfold zs; rewrite length_take_le; [lia | rewrite length_drop; lia]).
  iApply (Hfwq _ fb freg fl f2 fd tw off dq b' reg' (so + Z.of_nat j) c' zs eb
            with "Hl Hfl Hfl2 Hfdc Htw Hoff Hl' Hsub Herr").
  1: { rewrite Hlz. rewrite (Z.mod_small d (2 ^ 64)); [|lia].
        replace (b' + so + (n - T)) with (b' + (so + Z.of_nat j)) by (unfold j; lia). reflexivity. }
  all: try (unfold zs; apply Forall_take, Forall_drop; exact Hy).
  all: try (unfold j in *; lia).
  all: try assumption.
  iNext. iIntros (r fl' tw' off' [Hpost Hfl']) "Hl Hfl Hfl2 Hfdc Htw Hoff Hl' Hsub Herr".
  rewrite Hlz in Hpost. iDestruct ("Hysb" with "Hsub") as "Hys".
  assert (Hr : 0 <= r <= d) by (destruct Hpost as [[-> _] | [? _]]; lia).
  resume. rewrite (Z.mod_small r (2 ^ 64)); [|lia].
  (* `c: _cur_column` is 0: no adjustment; iw_2.L70. *)
  step. check "Hl".
  load_bytes_dq "Hl Hcol" decode (reflexivity) by ar.
  iNext. iIntros "Hl Hcol". branch. step. branch.
  iAssert (xos w0 eb X fb nb) with "[Hfl Hfl2 Hfdc Htw Hoff Hcol Hmode Herr HX]" as "Hos".
  { assert (Happ' : Z.land fl' io_is_appending = 0).
    { destruct Hpost as [[_ ->] | [_ ->]]; [exact Happ | apply land_err_seen; exact Happ]. }
    assert (Hflags' : xs_flags nb fl').
    { destruct Hpost as [[_ ->] | [_ ->]]; [exact Hflags | apply xs_flags_error; exact Hflags]. }
    iFrame "HX". iExists fl', f2, fd, tw', off', m. iFrame. iPureIntro.
    tauto. }
  iApply (wp_xs_L70 Hmove Hmove_fn Hmove_sym eb X fb freg vb vreg nb wp we
            dq b' reg' so c' ys T d r with "Hvt Hl Hvtp Hwbf Hos Hl' Hys HK");
    try close_side.
  all: unfold n in *; try lia. all: lk_fin.
Qed.

End rules.
