(** An unbuffered stream has a one-byte buffer. Glibc therefore offers
    the entire input string to the stream's write function, including
    when the source is read-only. The syscall returns the caller's share
    of the input, and the stream keeps its own short byte. *)

From Glibc Require Import Unit_io_write_nocancel_os Unit_io_write_os Unit_libio_fileops_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysWrappers FileInv LibioLogic LibioPutsInv
  LibioWriteDq LibioOverflowBase LibioOverflowShortWrite LibioOverflowShortSend LibioXsputnShortReset.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.

Section write.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write).
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** After flushing the empty stream, xsputn sees the short buffer. It
    needs no seek because the read end and write base coincide. It uses
    the write slot for ordinary and noncanceling writes alike. *)
Lemma wp_xs_short_write fb freg rb fl f2 fd tw off byte mode vb vr dq b reg o c ys eb e from Φ :
  let n := Z.of_nat (length ys) in
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  Z.land fl io_is_appending = 0 -> Z.land fl 514 <> 0 -> (mode = 0 \/ mode = 2^32-1) ->
  (Z.land f2 2 = 0 \/ Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined Unit_io_write_nocancel_os.fn___GI___write_nocancel)) ->
  In fd (ow_fds w0) -> ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  (c = Obj b \/ c = Ro b) -> 0 < b -> 0 <= o -> b+o+n <= r_end reg -> r_end reg <= 2^63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 < n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk11") e = Some (WPtr (mkPtr (fb+off_vtable) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.5") e = Some (WInt n) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b+o) c)) ->
  vtables_ro ge vb vr -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗ short_state fb rb fl tw off byte -∗
  liveq dq b reg -∗ bytesq dq b o ys -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post n fl r fl'⌝ -∗ live fb freg -∗ ovf_fixed fb f2 fd eb mode vb -∗
      short_state fb (short_ptr fb) fl' tw' off' byte -∗ liveq dq b reg -∗ bytesq dq b o ys -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame Unit_libio_fileops_os.fn__IO_new_file_xsputn e [] None (Enter (TAtom "L132") (Some from))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros n Hfb Hal Hend Hrend Happ Hub Hmd Hready Hin He Hc Hb Ho Hen Hr Hy Hn Hv0 Hc0 Hc11 Hv4 Hp5 Hp1.
  iIntros "#Hvt Hl ([%Hf2 Hf2] & Hfd & Herr & Hcol & Hmode & Hvtp) ((Hrp & Hre & Hrb & Hwb & Hwp & Hwe & Hbase & Hbend) & [%Hfl Hflags] & Htw & Hoff & Hbyte) Hbl Hys HK".
  iPoseProof (vtables_slot ge vb vr slot_write "_IO_new_file_write" with "Hvt") as "#Hslot"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_write")) vr) as "Hfc". { rewrite (ge_fn_cap _ _ _ Hfw). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvr) & Hvl & _)".
  unfold file_size in Hend. unfold io_is_appending in Happ. unfold io_vtables_size in Hvend. unfold short_ptr, off_shortbuf.
  adv. load_self_using wp_raw_load_pointer_self "Hl Hbend". adv. load_self_using wp_raw_load_pointer_self "Hl Hbase".
  adv. branch_as true. adv. branch_as false. adv. load_s32 "Hl" "Hflags". adv. branch_as true.
  adv. load_self_using wp_raw_load_pointer_self "Hl Hre". adv. load_self_using wp_raw_load_pointer_self "Hl Hwb". adv. branch_as true. adv.
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl"); [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". do 5 step. branch_as true. step. step. norm.
  check_read_dq "Hvl'" by ar. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hslot Hfc"); [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hfw) |].
  iNext. iIntros "_ _ _". iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfw) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfw) | apply (ge_fn_check _ _ _ Hfw) | vx |
    apply (ge_fn_find _ _ _ Hfw) | reflexivity | reflexivity |]. iNext.
  iApply (wp_glibc__IO_new_file_write_dq Hreg Hext _ fb freg fl f2 fd tw off dq b reg c o ys eb
    with "Hl [$Hflags //] [$Hf2 //] Hfd Htw Hoff Hbl Hys Herr"); try assumption.
  { fold n. rewrite Z.sub_0_r !Z.mod_small //; lia. }
  iNext. iIntros (r fl' tw' off' [Hpost Hrange]) "Hl Hflags Hf2 Hfd Htw Hoff Hbl Hys Herr". fold n in Hpost.
  iExists _. iSplit; [done|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  assert (Hrn : 0 <= r <= n) by (destruct Hpost as [[-> _]|[? _]]; lia).
  assert (Hub' : Z.land fl' 514 <> 0) by (destruct Hpost as [[_ ->]|[_ ->]]; [exact Hub|rewrite land_lor_const //]).
  rewrite (Z.mod_small r (2^64)); [|lia]. adv. load_bytes_dq "Hl Hcol" decode (reflexivity) by ar.
  iNext. iIntros "Hl Hcol". branch. step. branch.
  iApply (wp_xs_short_reset fb freg fl' mode rb n r with "Hl Hflags Hmode [$Hrp $Hre $Hrb $Hwb $Hwp $Hwe $Hbase $Hbend]");
    try first [assumption | lia | lk_prove | lookups; repeat f_equal; unwrap2; lia].
  iNext. iIntros "Hl Hflags Hmode Hptrs". iApply ("HK" with "[%] Hl [$Hf2 $Hfd $Herr $Hcol $Hmode $Hvtp] [$Hptrs $Hflags $Htw $Hoff $Hbyte] Hbl Hys"); exact Hpost.
Qed.
End write.
