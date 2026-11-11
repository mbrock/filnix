(** `c: _IO_file_close_maybe_unlink(fp, 0)` (LibioCloseItCode.v;
    glibc 2.44's `c: _IO_file_close_it`, libio/fileops.c), which
    `c: fclose` calls, on a narrow stream with pending output in its
    heap buffer (`c: _IO_CURRENTLY_PUTTING` set, as `c: puts` leaves
    stdout): the pending bytes go to `c: _IO_new_do_write` (Lane 4A's
    LibioDoWrite.v, whose triple is [do_write_spec]), then
    LibioCloseItMid.v's [wp_close_it_L18] closes the descriptor, gives
    up the buffer and leaves the stream closed
    ([wp_glibc__IO_file_close_maybe_unlink]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode LibioCloseItCode
  FileInv LibioLogic SysWrappers LibioSetb LibioCloseSteps LibioCloseItEnd LibioCloseItMid.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioCloseItOn (R : Runtime) (LG0 : LogicSig R).
Module CM := LibioCloseItMidOn R LG0.
Import CM CM.CE CM.CE.CS CM.CE.CS.SW CM.CE.CS.SW.FI.ML CM.CE.CS.SW.FI.LG CM.CE.CS.SW.FI.L CM.CE.CS.SW.OW
  CM.CE.CS.SW.FI CM.CE.CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hfc : ge_fn ge "__GI__IO_file_close" glibc__IO_file_close).
Context (Hsetb : find_fn ge (TAtom "__GI__IO_setb") = Some (Defined glibc__IO_setb)).
Context (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance close_it_top_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_new_do_write`'s triple, as LibioDoWrite.v's
    [wp_glibc__IO_new_do_write] states it. *)
Definition do_write_spec : Prop := forall fr fb freg fl f2 fd tw off bb breg i xs rp rb wp we be eb vb vreg Φ,
  let n := Z.of_nat (length xs) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  call_frame glibc__IO_new_do_write [WPtr (mkPtr fb (Obj fb)); WPtr wb; WInt n] = Some fr -> 0 < n ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode 0 -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post n fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end (if Z.land fl' 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode 0 -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

(** The callees' triples: [do_write_spec], and LibioCloseItMid.v's
    `c: _IO_file_close`, `c: _IO_setb` and `c: _IO_unsave_markers`. *)
Context (Hdw : do_write_spec).
Context (Hclose : CM.close_spec w0 registry ge).
Context (Hsetb_spec : setb_spec w0 registry ge).
Context (fum : func) (Hfum : find_fn ge (TAtom "__GI__IO_unsave_markers") = Some (Defined fum)).
Context (Hum : CM.unsave_spec w0 registry ge fum).

(** `c: _IO_file_close_maybe_unlink(fp, 0)` of an open narrow stream
    (mode 0) whose n pending bytes xs sit at offset i of its heap
    buffer bb: `c: _IO_new_do_write` writes r of them ([fw_post]); the
    descriptor is closed, k the result; the buffer is given up; every
    buffer pointer is null; the flags are [closed_flags], the
    descriptor and offset -1; the result is k if not 0, else
    `c: _IO_new_do_write`'s. *)
Lemma wp_glibc__IO_file_close_maybe_unlink fr fb freg fl f2 fd tw off bb breg i xs rp rb we be eb vb vreg Φ :
  let n := Z.of_nat (length xs) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  call_frame glibc__IO_file_close_maybe_unlink [WPtr (mkPtr fb (Obj fb)); WInt 0] = Some fr -> 0 < n ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> Z.land f2 32 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 -> Z.land fl io_no_writes = 0 ->
  Z.land fl io_currently_putting <> 0 -> Z.land fl io_user_buf = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> r_kind breg = Heap ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr (mkPtr (bb + i + n) (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode 0 -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 80 null -∗ pcell fb 96 null -∗
  ▷ (∀ r fl' k tw', ⌜fw_post n fl r fl' /\ (k = 0 \/ k = 2 ^ 32 - 1)⌝ -∗
     live fb freg -∗ int_cell fb off_flags (closed_flags fl') -∗ int_cell fb off_flags2 f2 -∗
     int_cell fb off_fileno (2 ^ 32 - 1) -∗ icell fb off_total_written tw' -∗ icell fb off_offset (2 ^ 64 - 1) -∗
     errno_any eb -∗
     pcell fb 8 null -∗ pcell fb 16 null -∗ pcell fb 24 null -∗ pcell fb 32 null -∗ pcell fb 40 null -∗
     pcell fb 48 null -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end null -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode 0 -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     pcell fb 80 null -∗ pcell fb 96 null -∗
     Φ (Ret (WInt (if k =? 0 then (if r =? n then 0 else 2 ^ 32 - 1) else k)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros n wb base Hfr. injection Hfr as <-. intros Hn0 Hfb Hfal Hfend Hfreg Hf22 Hf232 Hf2r Hfd Hfdr Hfl Happ Hnw
    Hcp Hub He Hbk Hb Hi Hbend Hbreg Hy Hbe Hbec.
  iIntros "#Hvt Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp H80 H96 HK".
  unfold file_size in Hfend. pose proof Hnw as Hnw'. pose proof Hcp as Hcp'.
  unfold io_no_writes in Hnw'. unfold io_currently_putting in Hcp'.
  iApply (wp_live_fit1 w0 registry ge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 registry ge with "Hbl"). iIntros ([Hb0 Hb48]) "Hbl".
  assert (0 <= fd < 2 ^ 32) by lia. assert (0 <= 0 < 2 ^ 32) by lia.
  assert (0 <= Z.land fl 8 < 2 ^ 32) by (rewrite Hnw'; lia).
  assert (0 <= Z.land fl 2048 < 2 ^ 32) by (apply land_lt32; lia).
  iDestruct "Hfd" as "[_ Hfd]". iDestruct "Hfl" as "[_ Hfl]". iDestruct "Hmode" as "[_ Hmode]".
  (* start, L7, L23, L24, L16: open, writable, putting, narrow. *)
  fs. fs. fchk "Hl". fldi "Hl" "Hfd". fs. fbrv true.
  fs. fchk "Hl". fldi "Hl" "Hfl". fs. fs. fbrv false.
  fs. fldi "Hl" "Hfl". fs. fs. fs. fs. fbrv false.
  fs. fs. fchk "Hl". fldi "Hl" "Hmode". fs. fbr.
  (* L31: `c: _IO_do_write(fp, write_base, write_ptr - write_base)`. *)
  fs. fs. fchk "Hl". fldp "Hl" "Hwb" "Hbl". fs. fldp "Hl" "Hwp" "Hbl". fldp "Hl" "Hwb" "Hbl". fs. fs. fs.
  assert (E50 : ((bb + i + n) mod 2 ^ 64 - (bb + i) mod 2 ^ 64) mod 2 ^ 64 = n).
  { rewrite (Z.mod_small (bb + i + n) (2 ^ 64)); [|lia]. rewrite (Z.mod_small (bb + i) (2 ^ 64)); [|lia].
    rewrite Z.mod_small; lia. }
  rewrite E50. clear E50.
  iAssert (int_cell fb off_flags fl) with "[Hfl]" as "Hfl"; [iSplit; [done | iExact "Hfl"]|].
  iAssert (int_cell fb off_fileno fd) with "[Hfd]" as "Hfd"; [iSplit; [done | iExact "Hfd"]|].
  iAssert (int_cell fb off_mode 0) with "[Hmode]" as "Hmode"; [iSplit; [done | iExact "Hmode"]|].
  iApply wp_call_bind; [vx | exact Hdwf | reflexivity |]. iNext. rewrite (Z.mod_small n (2 ^ 64)); [|lia].
  iApply (Hdw with "Hvt Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp");
    try side.
  iNext. iIntros (r fl' tw' off' [Hpost Hfl']) "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase
    Hbend Hcol Hmode Hvtp". resume. fs.
  (* L18 to the return. *)
  assert (Ep3 : (if r =? Z.of_nat (length xs) then 0 else 2 ^ 32 - 1) mod 2 ^ 32 =
                (if r =? Z.of_nat (length xs) then 0 else 2 ^ 32 - 1))
    by (destruct (r =? Z.of_nat (length xs)); reflexivity).
  rewrite Ep3. try rewrite Ep3.
  iApply (CM.wp_close_it_L18 w0 registry ge Hfc Hsetb Hclose Hsetb_spec fum Hfum Hum
            with "Hvt Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend [Hbl] H80 H96");
    first [intros blk Hblk; vm_compute in Hblk; injection Hblk as <-; reflexivity | try side].
  { iRight. iExists bb, breg. iFrame "Hbl". iPureIntro. split_and!; try done; try lia.
    destruct Hpost as [(_ & ->) | (_ & ->)]; [exact Hub|].
    rewrite Z.land_lor_distr_l. rewrite Hub. reflexivity. }
  iNext. iIntros (k Hk) "Hl Hfl Hfl2 Hfd Hoff Hmode Hvtp Herr H8 H16 H24 H32 H40 H48 Hbb Hbe H80 H96".
  try rewrite Ep3. try rewrite Ep3.
  iApply ("HK" $! r fl' k tw' with "[%] Hl Hfl Hfl2 Hfd Htw Hoff Herr H8 H16 H24 H32 H40 H48 Hbb Hbe Hcol Hmode Hvtp
            H80 H96").
  split; [exact Hpost | exact Hk].
Qed.

End rules.
End LibioCloseItOn.
