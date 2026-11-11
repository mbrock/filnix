(** The fill of `c: _IO_new_file_xsputn` (LibioXsputnBase.v describes
    the function), from block `c: L20`, with the count of bytes that
    fit and the flush flag the line-buffer test chose:

    ```
    if (count > 0)
      { if (count > to_do) count = to_do;
        f->_IO_write_ptr = __mempcpy (f->_IO_write_ptr, s, count);
        s += count; to_do -= count; }
    ```

    [wp_xs_L101] copies the count into the buffer at the write pointer
    by LibioDefaultXsputnCopy.v's [wp_call_mempcpy_in], from the
    caller's bytes at their share, and [wp_xs_L20] takes the smaller of
    the count and n; both go on at LibioXsputnFlush.v's [wp_xs_L96]. *)

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
  LibioXsputnWrite LibioXsputnFlush.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L20` of `c: _IO_new_file_xsputn`, after its phis. *)
Definition xs_L20b : block := Eval vm_compute in
  match find_block (TAtom "L20") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L20") [] [] JRetVoid end.

(** Block `c: L101`, after its phi: the copy. *)
Definition xs_L101 : block := Eval vm_compute in
  match find_block (TAtom "L101") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L101") [] [] JRetVoid end.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioXsputnFillOn (R : Runtime) (LG0 : LogicSig R).
Module XU := LibioXsputnFlushOn R LG0.
Import XU XU.XW XU.XW.XD XU.XW.XD.XC XU.XW.XD.XC.XR XU.XW.XD.XC.XR.XF XU.XW.XD.XC.XR.XF.XS XU.XW.XD.XC.XR.XF.XS.XB XU.XW.XD.XC.XR.XF.XS.XB.DX XU.XW.XD.XC.XR.XF.XS.XB.DX.RM XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY
  XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.CS
  XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.ML XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.LG
  XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI.L XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.OW XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.FI
  XU.XW.XD.XC.XR.XF.XS.XB.DX.RM.SM.TL.BY.BF.CP.SW.ST.

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
Local Instance xs_fill_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise, through the environment's puts. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** Block `c: L101` on: the c bytes from s, at most n and the room
    from the write pointer to the buffer's end, copied there. *)
Lemma wp_xs_L101 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys mf c e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 < c <= Z.of_nat (length ys) ->
  ptr_addr wp + c <= ptr_addr (nb_end nb) -> mf = 0 \/ mf = 1 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr (b' + so) c')) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.6") e = Some (WInt mf) ->
  lookup (TAtom "pr.9") e = Some (WInt c) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Exec (TAtom "L101") (b_insts xs_L101) (b_jump xs_L101)))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Heb Hfb Hfal Hfend Hfreg Hc' Hb'0 Hb8' Hso Hyend Hyreg Hy Hc Hroom Hmf Hv0 Hc0 Hv2 Hv4 Hp6 Hp9.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp (Hwc & Hwp & Hwe & Hroom) Hos Hl' Hys HK".
  destruct nb as [[b sz] |]; [| iDestruct "Hroom" as %[-> ->]; cbn in Hroom; lia].
  iDestruct "Hroom" as (reg xs cs Hok) "(Hbl & Hxs & Hcs)".
  pose proof Hok as (Hb0 & Hb8 & Hsz & Hbend & Hbreg & Hlx & Hlc & Hx & [Hwc' Hwa] & [Hec Hea] & Hheap).
  destruct wp as [wa wc]. cbn in Hwc', Hwa, Hroom. subst wc.
  cbn [xs_L101 b_insts b_jump]. fs. fchk "Hl". fldp "Hl" "Hwp" "Hbl".
  set (ysub := take (Z.to_nat c) ys).
  assert (Hls : Z.of_nat (length ysub) = c) by (unfold ysub; rewrite length_take_le; lia).
  iDestruct (bytesq_sub _ _ _ _ 0 (Z.to_nat c) with "Hys") as "[Hsub Hysb]"; [lia|].
  iApply (wp_call_mempcpy_in w0 registry ge Hmove Hmove_fn Hmove_sym _ _ _ _ _ _ _ _ _ b reg xs cs (wa - b) dq b'
            reg' (so + Z.of_nat 0) c' ysub with "Hbl Hxs Hcs Hl' Hsub");
    [exact Hcpy | | exact Hpcpy | reflexivity | exact Hc' | lia | lia | exact Hb8 | exact Hb8' | lia | lia | lia
    | lia | lia | lia | exact Hx | |].
  { cbn -[put]. lookups. rewrite Hls. repeat f_equal; first [lia | unwrap2; reflexivity]. }
  { unfold ysub. apply Forall_take. exact Hy. }
  iNext. iIntros "Hbl Hbuf Hl' Hsub". iDestruct ("Hysb" with "Hsub") as "Hys".
  iDestruct "Hbuf" as (xs' cs') "(%Hl3 & Hxs & Hcs)". cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  fchk "Hl". fstp "Hl" "Hwp". fs. fs. fs. fs.
  iAssert (wbuf fb (Some (b, sz)) (mkPtr (wa + c) (Obj b)) we) with "[Hwc Hwp Hwe Hbl Hxs Hcs]" as "Hwb".
  { rewrite Hls. replace (b + (wa - b) + c) with (wa + c) by lia. iFrame. iPureIntro.
    unfold room_ok, in_buf. cbn. destruct Hl3 as (H1 & H2 & H3). cbn in Hroom.
    split_and!; first [reflexivity | assumption | lia]. }
  iApply (wp_xs_L96 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf Hfw Hfwq eb X fb freg vb vreg
            (Some (b, sz)) (mkPtr (wa + c) (Obj b)) we dq b' reg' so c' ys (n - c) mf
            with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK"); try side.
  all: unfold n in *; try lia; try (intros _; discriminate). all: lk_fin.
Qed.

(** Block `c: L20` on, cnt bytes of room from the write pointer and
    the flush flag mf: the copy of the smaller of cnt and n when cnt is
    not 0 ([wp_xs_L101]), then [wp_xs_L96]. *)
Lemma wp_xs_L20 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys mf cnt e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 < n -> 0 <= cnt ->
  ptr_addr wp + cnt <= ptr_addr (nb_end nb) -> ptr_addr (nb_end nb) <= 2 ^ 63 -> mf = 0 \/ mf = 1 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr (b' + so) c')) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.6") e = Some (WInt mf) ->
  lookup (TAtom "pr.10") e = Some (WInt cnt) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Exec (TAtom "L20") (b_insts xs_L20b) (b_jump xs_L20b)))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Heb Hfb Hfal Hfend Hfreg Hc' Hb'0 Hb8' Hso Hyend Hyreg Hy Hn0 Hcnt Hroom Hend Hmf Hv0 Hc0 Hv2 Hv4 Hp6 Hp10.
  iIntros "#Hvt Hl Hvtp Hwb Hos Hl' Hys HK".
  iAssert (⌜0 <= ptr_addr wp⌝)%I as %Hwp0.
  { iDestruct "Hwb" as "(_ & _ & _ & Hr)". destruct nb as [[b sz] |].
    - iDestruct "Hr" as (reg xs cs Hok) "_". iPureIntro. destruct Hok as (H1 & _ & _ & _ & _ & _ & _ & _ & [_ H2] & _). lia.
    - iDestruct "Hr" as %[-> _]. done. }
  cbn [xs_L20b b_insts b_jump]. fs.
  destruct (Z.eq_dec cnt 0) as [-> | Hc0'].
  - (* Nothing fits: L96 with all n left. *)
    fbrv true. fs.
    iApply (wp_xs_L96 w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf Hfw Hfwq eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys n mf with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK"); try side.
    all: unfold n in *; try lia; try (intros Hlt; lia). all: lk_fin.
  - fbrv false. fs. fs.
    destruct (Z_lt_le_dec (Z.of_nat (length ys)) cnt) as [Hlt | Hle].
    + (* More room than bytes: all n. *)
      fbrv false. fs.
      iApply (wp_xs_L101 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys mf n with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK");
        try side.
      all: unfold n in *; try lia. all: lk_fin.
    + fbrv true. fs. fs. fs.
      iApply (wp_xs_L101 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys mf cnt with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK");
        try side.
      all: unfold n in *; try lia. all: lk_fin.
Qed.

End rules.
End LibioXsputnFillOn.
