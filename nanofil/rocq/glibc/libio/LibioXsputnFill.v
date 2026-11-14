From Glibc Require Import GlibcProgram.
(** The file stream writer copies bytes into its buffer before handling
    any pending flush. This module verifies that copy and its byte count:

    ```
    if (count > 0)
      { if (count > to_do) count = to_do;
        f->_IO_write_ptr = __mempcpy (f->_IO_write_ptr, s, count);
        s += count; to_do -= count; }
    ```

    The writer caps the count at the number of source bytes remaining.
    It preserves the caller's source ownership while copying into the
    stream buffer, then continues to the flush decision. *)

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
  LibioXsputnReset LibioXsputnCall LibioXsputnDo
  LibioXsputnWrite LibioXsputnFlush.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputn LibioDefaultXsputnBuf LibioDefaultXsputnBytes LibioDefaultXsputnCopy LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioLogic LibioXsputnBase LibioXsputnCall LibioXsputnDo LibioXsputnFlags LibioXsputnFlush LibioXsputnReset LibioXsputnSetp LibioXsputnWrite OsWorld SysWrappers.
From Glibc Require Import Fix.
From Glibc Require Import GlibcSpec.
From Glibc Require StringSpecs.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** This block begins the fill after the writer has measured the available space. *)
Definition xs_L20b : block := Eval vm_compute in
  match find_block (TAtom "L20") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L20") [] [] JRetVoid end.

(** This block copies the chosen count and advances the write pointer. *)
Definition xs_L101 : block := Eval vm_compute in
  match find_block (TAtom "L101") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L101") [] [] JRetVoid end.


Import LibioXsputnFlush LibioXsputnWrite LibioXsputnDo LibioXsputnCall LibioXsputnReset LibioXsputnFlags LibioXsputnSetp LibioXsputnBase LibioDefaultXsputn LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioDefaultXsputnBytes LibioDefaultXsputnBuf LibioDefaultXsputnCopy SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The linked program provides glibc's copy functions and default stream writer. *)
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


(** This abbreviation selects expressions in the caller's linked program. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic checks the source pointer and byte counts after updates to the environment. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** The writer copies c source bytes into available buffer space and advances its write pointer. *)
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
  cbn [xs_L101 b_insts b_jump]. step. check "Hl". load "Hl" "Hwp" "Hbl".
  set (ysub := take (Z.to_nat c) ys).
  assert (Hls : Z.of_nat (length ysub) = c) by (unfold ysub; rewrite length_take_le; lia).
  iDestruct (bytesq_sub _ _ _ _ 0 (Z.to_nat c) with "Hys") as "[Hsub Hysb]"; [lia|].
  call_spec with (inr (b, reg, wa - b, xs, cs, dq, b', reg', so + Z.of_nat 0, c', ysub)).
  { cbn -[put]. lookups. rewrite Hls. repeat f_equal; first [lia | unwrap2; reflexivity]. }
  { repeat split; try assumption; try lia. unfold ysub. apply Forall_take. exact Hy. }
  iDestruct "Hpost" as "(-> & Hbl & Hbuf & Hl' & Hsub)".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iDestruct ("Hysb" with "Hsub") as "Hys".
  iDestruct "Hbuf" as (xs' cs') "(%Hl3 & Hxs & Hcs)". cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  check "Hl". store "Hl" "Hwp". step. step. step. step.
  iAssert (wbuf fb (Some (b, sz)) (mkPtr (wa + c) (Obj b)) we) with "[Hwc Hwp Hwe Hbl Hxs Hcs]" as "Hwb".
  { rewrite Hls. replace (b + (wa - b) + c) with (wa + c) by lia. iFrame. iPureIntro.
    unfold room_ok, in_buf. cbn. destruct Hl3 as (H1 & H2 & H3). cbn in Hroom.
    split_and!; first [reflexivity | assumption | lia]. }
  iApply (wp_xs_L96 Hmove Hmove_fn Hmove_sym Hfw Hfwq eb X fb freg vb vreg
            (Some (b, sz)) (mkPtr (wa + c) (Obj b)) we dq b' reg' so c' ys (n - c) mf
            with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK"); try close_side.
  all: unfold n in *; try lia; try (intros _; discriminate). all: lk_fin.
Qed.

(** The writer fills available space with at most n bytes before deciding whether to flush.
    If the buffer is full, it proceeds directly to the flush decision. *)
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
  cbn [xs_L20b b_insts b_jump]. step.
  destruct (Z.eq_dec cnt 0) as [-> | Hc0'].
  - (* Nothing fits: L96 with all n left. *)
    branch_as true. step.
    iApply (wp_xs_L96 Hmove Hmove_fn Hmove_sym Hfw Hfwq eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys n mf with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK"); try close_side.
    all: unfold n in *; try lia; try (intros Hlt; lia). all: lk_fin.
  - branch_as false. step. step.
    destruct (Z_lt_le_dec (Z.of_nat (length ys)) cnt) as [Hlt | Hle].
    + (* More room than bytes: all n. *)
      branch_as false. step.
      iApply (wp_xs_L101 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys mf n with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK");
        try close_side.
      all: unfold n in *; try lia. all: lk_fin.
    + branch_as true. step. step. step.
      iApply (wp_xs_L101 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys mf cnt with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK");
        try close_side.
      all: unfold n in *; try lia. all: lk_fin.
Qed.

End rules.
