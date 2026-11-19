(** Hello prints through a wide stream, and every byte that reaches
    stdout passes through glibc's narrow write function on the way out.
    The wide flush first turns its characters into bytes, then asks the
    narrow `c: _IO_new_do_write` to send those bytes and reset the narrow
    buffer. The narrow proofs in [LibioDoWrite](LibioDoWrite.v) do not
    cover this call, for two reasons. A wide stream has mode 1, so after
    the write glibc sets the write end to the buffer's end even when the
    stream is line-buffered or unbuffered. And the bytes may come from a
    small array on the caller's stack rather than from the narrow buffer,
    because the wide flush converts into that array when the buffer has
    fewer than 16 bytes free. This file proves the call for both kinds of
    narrow buffer that a wide stream can have. *)

From Glibc Require Import Unit_io_write_os Unit_libio_fileops_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics GlibcSymFunc.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry FileInv LibioLogic
  LibioPutsInv LibioWriteDq LibioOverflowBase LibioOverflowShortWrite LibioWIdle SysWrappers.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write).

(** ## A heap buffer

    Most streams keep their bytes in a buffer on the heap. Between two
    writes such a stream keeps its read pointers and its write base at the
    start of that buffer, so the write never has to seek first. The bytes
    to send may sit in the buffer itself or in a separate array. The
    statement covers both cases at once: when the bytes are in the buffer,
    the buffer's own life also serves for the write.
*)

(** This rule sends n bytes through the wide jump table, whose write slot
    holds the same narrow write function as the narrow table. The post
    says how many bytes reached the descriptor, as [fw_post] describes.
    Whatever the result, the read and write pointers go back to the start
    of the buffer and the write end goes to its end. The call returns 0
    when every byte was written and `c: EOF` otherwise. *)
Lemma wp_wide_do_write_heap fr fb freg fl f2 fd tw off bb breg be db dreg o xs rp rb wp we eb vb vreg Φ :
  let n := Z.of_nat (length xs) in
  let base := mkPtr bb (Obj bb) in
  call_frame Unit_libio_fileops_os.fn__IO_new_do_write [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (db + o) (Obj db)); WInt n] = Some fr ->
  0 < n -> 0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < bb < 2 ^ 63 -> r_end breg <= 2 ^ 63 -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb ->
  0 < db -> 0 <= o -> db + o + n <= r_end dreg -> r_end dreg <= 2 ^ 63 -> (db = bb -> dreg = breg) ->
  Forall (fun x => 0 <= x < 256) xs ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗
  (if decide (db = bb) then True else live db dreg) -∗ bytes db o xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 base -∗ pcell fb 24 rb -∗ pcell fb off_write_base base -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode 1 -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post n fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live bb breg -∗
     (if decide (db = bb) then True else live db dreg) -∗ bytes db o xs -∗ errno_any eb -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end be -∗ pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode 1 -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros n base Hfr. injection Hfr as <-.
  intros Hn0 Hfb Hal Hend Hfreg Hf2 Hf2r Hfd Happ He Hb Hbreg Hbe Hbec Hdb Ho Hdend Hdreg Hdeq Hy.
  iIntros "#Hvt #Hwvt Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hdl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp HK".
  unfold file_size in Hend. unfold io_is_appending in Happ. assert (Hn : n < 2 ^ 63) by lia.
  iDestruct "Hfl" as "[%Hfl0 Hfl]".
  step. step. branch_as true. step. check "Hl". load_s32_group "Hl Hfl". step. branch_as true.
  step. step. norm. check "Hl".
  load_pointer "Hl Hre Hbl" by ar.
  iNext. iIntros "Hl Hre Hbl". step. norm. check "Hl".
  load_pointer "Hl Hwb Hbl" by ar.
  iNext. iIntros "Hl Hwb Hbl". step. step. step. branch_as true.
  iPoseProof (wvtables_slot ge vb slot_write "_IO_new_file_write" with "Hwvt") as "#Hsw"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_write")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfw). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)".
  unfold io_vtables_size in Hvend.
  step. step. norm. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_wfile in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true.
  step. step. norm.
  check_read_dq "Hvl'" by ar.
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsw Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hfw) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfw) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfw) | apply (ge_fn_check _ _ _ Hfw) | vx |
    apply (ge_fn_find _ _ _ Hfw) | reflexivity | reflexivity |].
  iNext. rewrite (Z.mod_small n (2 ^ 64)); [|lia].
  iAssert (live db dreg ∗ (live db dreg -∗ live bb breg ∗ (if decide (db = bb) then True else live db dreg)))%I
    with "[Hbl Hdl]" as "[Hd Hback]".
  { destruct (decide (db = bb)) as [-> | ?].
    - rewrite (Hdeq eq_refl). iSplitL "Hbl"; [iExact "Hbl" | iIntros "H"; by iFrame].
    - iSplitL "Hdl"; [iExact "Hdl" | iIntros "H"; by iFrame]. }
  iApply (wp_glibc__IO_new_file_write_dq Hreg with "Hl [$Hfl //] Hfl2 Hfd Htw Hoff Hd Hxs Herr");
    try first [reflexivity | assumption | left; first [assumption|reflexivity] | lia].
  iNext. iIntros (r fl' tw' off' [Hpost Hfl']) "Hl Hfl Hfl2 Hfd Htw Hoff Hd Hxs Herr".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  assert (Hr : 0 <= r <= n) by (destruct Hpost as [[-> _] | [? _]]; lia).
  rewrite (Z.mod_small r (2 ^ 64)); [|lia].
  iDestruct ("Hback" with "Hd") as "[Hbl Hdl]".
  destruct be as [bea bec]. cbn in Hbe, Hbec. subst bec.
  unfold base. step. norm. check "Hl".
  load_bytes_dq "Hl Hcol" decode (reflexivity) by ar.
  iNext. iIntros "Hl Hcol". branch. step. branch.
  step. step. step. norm. check "Hl".
  load_pointer "Hl Hbase Hbl" by ar.
  iNext. iIntros "Hl Hbase Hbl". check "Hl".
  store_pointer "Hl Hrb" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hrb". step. norm. check "Hl".
  load_pointer "Hl Hbase Hbl" by ar.
  iNext. iIntros "Hl Hbase Hbl". check "Hl".
  store_pointer "Hl Hrp" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hrp". step. norm. check "Hl".
  load_pointer "Hl Hbase Hbl" by ar.
  iNext. iIntros "Hl Hbase Hbl". check "Hl".
  store_pointer "Hl Hre" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hre".
  step. step. norm. check "Hl".
  load_pointer "Hl Hbase Hbl" by ar.
  iNext. iIntros "Hl Hbase Hbl". check "Hl".
  store_pointer "Hl Hwp" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hwp". check "Hl".
  store_pointer "Hl Hwb" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hwb". step. step. norm. check "Hl".
  iDestruct "Hmode" as "[%Hm2 Hmode]". load_s32_group "Hl Hmode". step. branch.
  step. branch. step. step. norm. check "Hl".
  load_pointer "Hl Hbend Hbl" by ar.
  iNext. iIntros "Hl Hbend Hbl". step. step. check "Hl".
  store_pointer "Hl Hwe" by (ar) preserving wi_store.
  iNext. iIntros "Hl Hwe". step. step. step. step. step.
  rewrite !(Z.mod_small r (2 ^ 64)) ?(Z.mod_small n (2 ^ 64)); try lia.
  destruct (Z.eq_dec r n) as [-> | Hrn];
    [rewrite Z.eqb_refl | rewrite (proj2 (Z.eqb_neq _ _) Hrn)]; branch; try (step; branch); try step.
  all: repeat step. all: iApply wp_ret; [reflexivity | vx |]; iNext.
  - iSpecialize ("HK" $! n fl' tw' off'). rewrite Z.eqb_refl.
    iApply ("HK" with "[%] Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hdl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol [$Hmode //] Hvtp");
      split; assumption.
  - iSpecialize ("HK" $! r fl' tw' off'). rewrite (proj2 (Z.eqb_neq _ _) Hrn).
    iApply ("HK" with "[%] Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hdl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol [$Hmode //] Hvtp");
      split; assumption.
Qed.

(** ## The short buffer

    Some streams write each byte as soon as it arrives. When such a
    stream becomes wide it still keeps a one-byte buffer inside the
    stream object. That buffer is too small to convert into, so the wide
    flush always converts into its own stack array and hands that array
    to this call. The small buffer's pointers belong to the stream
    object, so the proof reads them with the stream's own [[capability]].
*)

(** This rule sends n bytes from a separate array on a stream whose
    narrow buffer is that one-byte buffer. Afterwards every read and
    write pointer points at the start of the small buffer and the write
    end points at its end, just as the heap rule above describes. *)
Lemma wp_wide_do_write_short fr fb freg fl f2 fd tw off db dreg o xs rp rb wp we eb vb vreg Φ :
  let n := Z.of_nat (length xs) in
  let sb := short_ptr fb in
  let se := mkPtr (fb + 132) (Obj fb) in
  call_frame Unit_libio_fileops_os.fn__IO_new_do_write [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (db + o) (Obj db)); WInt n] = Some fr ->
  0 < n -> 0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> Z.land fl io_is_appending = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < db -> 0 <= o -> db + o + n <= r_end dreg -> r_end dreg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live db dreg -∗ bytes db o xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 sb -∗ pcell fb 24 rb -∗ pcell fb off_write_base sb -∗
  pcell fb off_write_ptr wp -∗ pcell fb off_write_end we -∗ pcell fb off_buf_base sb -∗ pcell fb off_buf_end se -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode 1 -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post n fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ live db dreg -∗ bytes db o xs -∗ errno_any eb -∗
     pcell fb off_read_ptr sb -∗ pcell fb 16 sb -∗ pcell fb 24 sb -∗ pcell fb off_write_base sb -∗
     pcell fb off_write_ptr sb -∗ pcell fb off_write_end se -∗ pcell fb off_buf_base sb -∗ pcell fb off_buf_end se -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode 1 -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type*.
  intros n sb se Hfr. injection Hfr as <-.
  intros Hn0 Hfb Hal Hend Hfreg Hf2 Hf2r Hfd Happ He Hdb Ho Hdend Hdreg Hy.
  iIntros "#Hvt #Hwvt Hl Hfl Hfl2 Hfd Htw Hoff Hd Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp HK".
  unfold file_size in Hend. unfold io_is_appending in Happ. assert (Hn : n < 2 ^ 63) by lia.
  iPoseProof (wvtables_slot ge vb slot_write "_IO_new_file_write" with "Hwvt") as "#Hsw"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_write")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfw). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)".
  unfold io_vtables_size in Hvend. iDestruct "Hfl" as "[%Hfl0 Hflags]".
  unfold sb, se, short_ptr, off_shortbuf. step. step. branch_as true. adv. load_s32 "Hl" "Hflags". adv. branch_as true.
  adv. load_self_using wp_raw_load_pointer_self "Hl Hre". adv. load_self_using wp_raw_load_pointer_self "Hl Hwb".
  adv. branch_as true. adv.
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_wfile in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". do 5 step. branch_as true. step. step. norm.
  check_read_dq "Hvl'" by ar. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsw Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hfw) |].
  iNext. iIntros "_ _ _". iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfw) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfw) | apply (ge_fn_check _ _ _ Hfw) | vx |
    apply (ge_fn_find _ _ _ Hfw) | reflexivity | reflexivity |]. iNext.
  rewrite (Z.mod_small n (2 ^ 64)); [|lia].
  iApply (wp_glibc__IO_new_file_write_dq Hreg with "Hl [$Hflags //] Hfl2 Hfd Htw Hoff Hd Hxs Herr");
    try first [reflexivity | assumption | left; first [assumption|reflexivity] | lia].
  iNext. iIntros (r fl' tw' off' [Hpost Hfl']) "Hl Hfl Hfl2 Hfd Htw Hoff Hd Hxs Herr".
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  assert (Hr : 0 <= r <= n) by (destruct Hpost as [[-> _] | [? _]]; lia).
  rewrite (Z.mod_small r (2 ^ 64)); [|lia]. adv. load_bytes_dq "Hl Hcol" decode (reflexivity) by ar.
  iNext. iIntros "Hl Hcol". branch. step. branch.
  iDestruct "Hfl" as "[%Hfl1 Hfl]". iDestruct "Hmode" as "[%Hm1 Hmode]".
  adv. load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hrb". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hrp". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hre". adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbase". adv. store "Hl" "Hwp". adv. store "Hl" "Hwb". adv.
  load_s32 "Hl" "Hmode". adv. branch. adv. branch. adv.
  load_self_using wp_raw_load_pointer_self "Hl Hbend". adv. store "Hl" "Hwe". adv.
  rewrite !(Z.mod_small r (2 ^ 64)) ?(Z.mod_small n (2 ^ 64)); try lia.
  destruct (Z.eq_dec r n) as [-> | Hrn];
    [rewrite Z.eqb_refl | rewrite (proj2 (Z.eqb_neq _ _) Hrn)]; branch.
  all: repeat step. all: iApply wp_ret; [reflexivity | vx |]; iNext.
  - iSpecialize ("HK" $! n fl' tw' off'). rewrite Z.eqb_refl.
    iApply ("HK" with "[%] Hl [$Hfl //] Hfl2 Hfd Htw Hoff Hd Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol [$Hmode //] Hvtp");
      split; assumption.
  - iSpecialize ("HK" $! r fl' tw' off'). rewrite (proj2 (Z.eqb_neq _ _) Hrn).
    iApply ("HK" with "[%] Hl [$Hfl //] Hfl2 Hfd Htw Hoff Hd Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol [$Hmode //] Hvtp");
      split; assumption.
Qed.

End rules.
