From Glibc Require Import Unit_io_write_os Unit_libio_fileops_os Unit_libio_iofflush_os.
From Glibc Require Import GlibcProgram.
(** GNU Hello calls `c: fflush` through glibc's `c: error`, on stdout
    before an error report and on stderr after it. Each of those
    streams is idle between calls, as [FileIdle](FileIdle.v) describes,
    so the call must work for every idle stream. This file proves the
    stream's sync function, `c: _IO_new_file_sync`, for such a stream:

    ```c
    if (fp->_IO_write_ptr > fp->_IO_write_base)
      if (_IO_do_flush (fp)) return EOF;
    delta = fp->_IO_read_ptr - fp->_IO_read_end;
    if (delta != 0) { ... seek back ... }
    if (retval != EOF) fp->_offset = _IO_pos_BAD;
    return retval;
    ```

    An idle stream has its read pointer equal to its read end, so the
    seek never runs. Only a heap buffer can hold pending output. A
    stream without a buffer has null pointers, and a stream on its short
    buffer keeps nothing in it between calls. The pending bytes go to
    `c: _IO_new_do_write`, whose joined proof this file reuses. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysWrappers FileInv FileIdle LibioLogic LibioCloseSteps
  LibioPutsInv FflushAcquire FflushUnlock
  HiAtexitDoWrite GlibcSpec LibioFputsSpec LibioFflushSpec Fix.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L
  FileInv LibioLogic LibioCloseSteps OsWorld SysWrappers.
Open Scope Z_scope.

Section sync.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** ## Loading a buffer pointer

    The sync function loads the stream's read and write pointers. A
    load of a pointer needs the object it points into to be alive, and
    that object depends on the stream's buffer. This rule covers the
    three buffers an idle stream can have, so the proofs below can load
    a pointer without first asking which buffer the stream has. *)

(** The sync function loads a buffer pointer from the stream's own
    fields. A null pointer needs no lifetime. A pointer into the short
    buffer points into the stream itself, whose lifetime the caller
    already holds. A pointer into a heap buffer needs that buffer's
    lifetime, and [buf_idle] holds it. *)
Lemma wp_load_buf_ptr f e ls l d off args rest j classes p fb freg o nb x Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj fb -> raw_address (ptr_addr p) off = fb + o -> (fb + o) mod 8 = 0 ->
  0 < fb -> fb + 132 < 2 ^ 64 -> in_buf fb nb x ->
  live fb freg -∗ pcell fb o x -∗ buf_idle nb -∗
  ▷ (live fb freg -∗ pcell fb o x -∗ buf_idle nb -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j))
       : gexpr) {{ Φ }}.
Proof using Type.
  intros Hc Hx Hp Ha Hal Hfb Hfe Hin. iIntros "Hl Hpc Hb HK".
  destruct nb as [| |bb sz|bb]; cbn [in_buf] in Hin.
  - subst x. iApply (wp_raw_load_null with "Hl Hpc"); try eassumption.
    iNext. iIntros "Hl Hpc". iApply ("HK" with "Hl Hpc Hb").
  - destruct x as [xa xc]. cbn in Hin. destruct Hin as [-> Hxa].
    iApply (wp_raw_load_pointer_self with "Hl Hpc"); try eassumption; [cbn; lia | reflexivity |].
    iNext. iIntros "Hl Hpc". iApply ("HK" with "Hl Hpc Hb").
  - destruct x as [xa xc]. cbn in Hin. destruct Hin as [-> Hxa].
    iDestruct "Hb" as (breg xs cs Hbp) "(Hbl & Hxs & Hcs)".
    pose proof Hbp as (Hk & Hend & Hreg & Hb0 & Hb8 & Hsz & _).
    iApply (wp_raw_load_pointer with "Hl Hpc Hbl"); try eassumption; [cbn; lia |].
    iNext. iIntros "Hl Hpc Hbl". iApply ("HK" with "Hl Hpc [Hbl Hxs Hcs]").
    iExists breg, xs, cs. iFrame. done.
  - iDestruct "Hb" as "[]".
Qed.

(** A pointer that an idle buffer allows lies in the address space. *)
Lemma in_buf_range fb nb x :
  0 < fb -> fb + 132 < 2 ^ 64 -> in_buf fb nb x -> buf_idle nb -∗ ⌜0 <= ptr_addr x < 2 ^ 64⌝.
Proof using Type.
  intros Hfb Hfe Hin. iIntros "Hb". destruct nb as [| |bb sz|bb]; cbn [in_buf] in Hin.
  - subst x. done.
  - iPureIntro. destruct Hin as [_ Hxa]. lia.
  - iDestruct "Hb" as (breg xs cs Hbp) "_". iPureIntro.
    destruct Hbp as (_ & Hend & Hreg & Hb0 & _). destruct Hin as [_ Hxa]. lia.
  - iDestruct "Hb" as "[]".
Qed.

(** This tactic loads one buffer pointer and proves the side
    conditions of the load the way the other load tactics do. *)
Local Ltac load_buf H :=
  iApply (wp_load_buf_ptr with H);
    [reflexivity | vx | reflexivity | a2 | a2 | lia | lia | eassumption |];
  iNext; iIntros H.

(** ## The sync function without pending output *)

(** An idle stream whose write pointer is not past its write base has
    nothing to write. Its read pointer, read end and write base are
    the same pointer p, so the sync function computes no seek, marks the
    offset unknown and returns 0. The rule holds for every buffer an
    idle stream can have. *)
Lemma wp_file_sync_quiet fr fb freg fl off nb p wp Φ :
  call_frame Unit_libio_fileops_os.fn__IO_new_file_sync [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land fl 256 = 0 -> in_buf fb nb p -> in_buf fb nb wp ->
  0 <= ptr_addr p < 2 ^ 64 -> 0 <= ptr_addr wp < 2 ^ 64 -> ptr_addr wp <= ptr_addr p ->
  live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 8 p -∗ pcell fb 16 p -∗ pcell fb 32 p -∗
  pcell fb 40 wp -∗ icell fb 144 off -∗ buf_idle nb -∗
  ▷ (live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 8 p -∗ pcell fb 16 p -∗ pcell fb 32 p -∗
     pcell fb 40 wp -∗ icell fb 144 (2 ^ 64 - 1) -∗ buf_idle nb -∗ Φ (Ret (WInt 0))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hreg Hbackup Hp Hwp Hpr Hwr Hle.
  iIntros "Hl Hfl H8 H16 H32 H40 Hoff Hb HK".
  iDestruct "Hfl" as "[%Hfl Hfl]". unfold file_size in Hend.
  cbn in Hfr. injection Hfr as <-.
  step. step. check "Hl". load_buf "Hl H40 Hb". step. check "Hl". load_buf "Hl H32 Hb".
  step. step. step. branch_as true.
  step. step. check "Hl". load_buf "Hl H8 Hb". step. check "Hl". load_buf "Hl H16 Hb".
  step. step. step. check "Hl". load_s32 "Hl" "Hfl". step. branch_as true.
  step. step. branch_as true. step. step. branch_as false.
  step. step. check "Hl". store_long "Hl" "Hoff". step. step.
  iApply wp_ret; [reflexivity | vx |]. iNext.
  iApply ("HK" with "Hl [Hfl] H8 H16 H32 H40 Hoff Hb"). iSplit; [done | iExact "Hfl"].
Qed.

(** ## The sync function with pending output

    A stream with a heap buffer may hold output between calls. The
    sync function hands those bytes to `c: _IO_new_do_write`, which
    writes them and moves every read and write pointer back to the
    buffer's base. The section below proves that path from the proved
    write function and the joined proof of `c: _IO_new_do_write`. *)

Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hsync : ge_fn ge "_IO_new_file_sync" Unit_libio_fileops_os.fn__IO_new_file_sync).
Context `{Hwrite : !Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  `{Hdwf : !Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.

(** The n bytes xs wait in the heap buffer bb from offset i, so the
    write base and both read pointers are bb + i and the write pointer
    is bb + i + n. The sync function writes them. When the write takes
    all n bytes it marks the offset unknown and returns 0; otherwise it
    returns `c: EOF`, and the write has set the error flag. Either way
    the read and write pointers end at the buffer's base, and the write
    end is the base for a line-buffered or unbuffered stream and the
    buffer's end otherwise. *)
Lemma wp_file_sync_pending fr fb freg fl f2 fd tw off bb breg i xs rb we sz eb vb vreg mode Φ :
  let n := Z.of_nat (length xs) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  let be := mkPtr (bb + sz) (Obj bb) in
  call_frame Unit_libio_fileops_os.fn__IO_new_file_sync [WPtr (mkPtr fb (Obj fb))] = Some fr -> 0 < n ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> 0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 ->
  Z.land fl io_is_appending = 0 -> Z.land fl 256 = 0 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 -> 0 <= bb + sz < 2 ^ 64 ->
  Forall (fun x => 0 <= x < 256) xs -> (mode = 0 \/ mode = 2 ^ 32 - 1) ->
  vtables_ro ge vb vreg -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr wb -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr (mkPtr (bb + i + n) (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode mode -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  ▷ (∀ r fl' tw' off', ⌜fw_post n fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
     live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
     icell fb off_total_written tw' -∗ icell fb off_offset (if r =? n then 2 ^ 64 - 1 else off') -∗
     live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
     pcell fb off_read_ptr base -∗ pcell fb 16 base -∗ pcell fb 24 base -∗ pcell fb off_write_base base -∗
     pcell fb off_write_ptr base -∗ pcell fb off_write_end (if Z.land fl' 514 =? 0 then be else base) -∗
     pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
     bytes fb off_column [0; 0] -∗ int_cell fb off_mode mode -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
     Φ (Ret (WInt (if r =? n then 0 else 2 ^ 32 - 1)))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Hdwf Hext Hfw Hreg Hwrite.
  intros n wb base be Hfr Hn Hfb Hal Hend Hfreg Hf2 Hf2r Hfd Hflr Happ Hbackup He Hb Hi Hbend Hbreg Hbe Hxs Hmd.
  iIntros "#Hvt Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp HK".
  unfold file_size in Hend. cbn in Hfr. injection Hfr as <-.
  iDestruct "Hfl" as "[%Hflr0 Hflb]". iDestruct "Hmode" as "[%Hmr Hmode]".
  step. step. check "Hl". load_pointer "Hl Hwp Hbl" by ar. iNext. iIntros "Hl Hwp Hbl".
  step. check "Hl". load_pointer "Hl Hwb Hbl" by ar. iNext. iIntros "Hl Hwb Hbl".
  step. step. step. branch_as false.
  step. step. check "Hl". load_s32 "Hl" "Hmode". step.
  (* The mode is 0 or -1, so `c: _IO_do_flush` takes the narrow branch. *)
  iStartProof; eapply step_wand; [eapply wp_branch; inst; vx |].
  lazymatch goal with |- context [edge_label (if ?c =? 0 then _ else _)] =>
    let E := fresh "E" in assert (E : (c =? 0) = false) by (destruct Hmd as [-> | ->]; decide_ints);
    rewrite E; clear E end; cbn [edge_label].
  step. step. load_pointer "Hl Hwb Hbl" by ar. iNext. iIntros "Hl Hwb Hbl".
  step. load_pointer "Hl Hwp Hbl" by ar. iNext. iIntros "Hl Hwp Hbl".
  load_pointer "Hl Hwb Hbl" by ar. iNext. iIntros "Hl Hwb Hbl". step. step. step.
  assert (En : (((bb + i + n) mod 2 ^ 64 - (bb + i) mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64 = n).
  { rewrite (Z.mod_small (bb + i + n) (2 ^ 64)); [|lia]. rewrite (Z.mod_small (bb + i) (2 ^ 64)); [|lia].
    replace (bb + i + n - (bb + i)) with n by lia. rewrite !(Z.mod_small n (2 ^ 64)); lia. }
  iApply wp_call_bind; [vx | exact Hdwf | reflexivity |]. iNext. rewrite En.
  iApply (hi_do_write_mode Hreg Hext Hfw _ fb freg fl f2 fd tw off bb breg i xs wb rb
    (mkPtr (bb + i + n) (Obj bb)) we be eb vb vreg mode with
    "Hvt Hl [$Hflb //] Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol [$Hmode //] Hvtp");
    try first [reflexivity | assumption | lia | libio_side].
  iNext. iIntros (r fl2 tw2 off2 [Hpost Hfl2r])
    "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode Hvtp".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  step. cbn [edge_label]. step. destruct (r =? Datatypes.length xs) eqn:Er.
  - (* Everything was written: L6 finds no seek and marks the offset unknown. *)
    branch_as true. step. step. check "Hl". load_pointer "Hl Hrp Hbl" by ar. iNext. iIntros "Hl Hrp Hbl".
    step. check "Hl". load_pointer "Hl Hre Hbl" by ar. iNext. iIntros "Hl Hre Hbl".
    step. step. step. check "Hl". iDestruct "Hfl" as "[%Hfl3 Hflb]". load_s32 "Hl" "Hflb". step.
    apply Z.eqb_eq in Er.
    assert (Efl : fl2 = fl) by (destruct Hpost as [[_ ->] | [Hlt _]]; [reflexivity | lia]). subst fl2.
    branch_as true. step. step. branch_as true. step. step. branch_as false.
    step. step. check "Hl". store_long "Hl" "Hoff". step. step.
    iApply wp_ret; [reflexivity | vx |]. iNext.
    assert (Hrn : (r =? n) = true) by (apply Z.eqb_eq; exact Er).
    iSpecialize ("HK" $! r fl tw2 off2). rewrite Hrn. rewrite !Zmod_0_l.
    iApply ("HK" with "[%] Hl [Hflb] Hfl2 Hfd Htw [Hoff] Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend
      Hcol Hmode Hvtp");
      [split; [left; split; [exact Er | reflexivity] | lia] | iSplit; [done | iExact "Hflb"] |
       rewrite Z.mod_small; [iExact "Hoff" | lia]].
  - (* A short write: L16 returns `c: EOF` and leaves the offset as the write left it. *)
    branch_as false. step. iApply wp_ret; [reflexivity | vx |]. iNext.
    assert (Hrn : (r =? n) = false) by exact Er.
    iSpecialize ("HK" $! r fl2 tw2 off2). rewrite Hrn.
    iApply ("HK" with "[%] Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol Hmode
      Hvtp").
    split; [exact Hpost | exact Hfl2r].
Qed.

(** ## The call through the jump table

    `c: fflush` takes the stream's lock, calls the sync function it
    finds in the stream's jump table, and releases the lock. The rule
    below proves the middle part for any sync function proof, given as
    the hypothesis Hsync. The sync function borrows the stream's
    lifetime, flags and jump table pointer and may set the error flag,
    but it keeps `c: _IO_USER_LOCK` clear, so the unlock still takes
    the lock path. *)
Lemma wp_fflush_dispatch e fb freg fl lb lbreg sb sreg vb vreg (S : iProp Σ) (T : Z -> Z -> iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (forall fr Ψ, call_frame Unit_libio_fileops_os.fn__IO_new_file_sync [WPtr (mkPtr fb (Obj fb))] = Some fr ->
    vtables_ro ge vb vreg -∗ live fb freg -∗ int_cell fb 0 fl -∗ pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗ S -∗
    ▷ (∀ r fl', ⌜(r = 0 \/ r = 2 ^ 32 - 1) /\ Z.land fl' 32768 = 0⌝ -∗ live fb freg -∗ int_cell fb 0 fl' -∗
       pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗ T r fl' -∗ Ψ (Ret (WInt r))) -∗
    WP (ERun fr : gexpr) {{ Ψ }}) ->
  vtables_ro ge vb vreg -∗ pcellq DfracDiscarded vb (vt_file + 96) (sym_ptr ge "_IO_new_file_sync") -∗
  single_ro ge sb sreg -∗ live fb freg -∗ int_cell fb 0 fl -∗
  pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 1 0 (ow_self w0) -∗ S -∗
  ▷ (∀ r fl', ⌜(r = 0 \/ r = 2 ^ 32 - 1) /\ Z.land fl' 32768 = 0⌝ -∗ live fb freg -∗ int_cell fb 0 fl' -∗
     pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) -∗
     pcell fb 136 (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗ T r fl' -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame Unit_libio_iofflush_os.fn___GI__IO_fflush e [] None
    (Enter (TAtom "L22") (Some (TAtom "L32")))) : gexpr) {{ Φ }}.
Proof using Hsync.
  intros Hv0 Hc0 Hfb Hal Hend Hregion Hspec.
  iIntros "#Hvt #Hslot #Hs Hl Hfl Hvtp Hlp Hlk HS HK". iPoseProof "Hvt" as "#Hvt0".
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_sync")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hsync). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  iApply (wp_live_fit1 with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  step. step. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | cbn; unfold vt_file; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true.
  step. step. check_read_dq "Hvl'" by a2. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hslot Hfc");
    [reflexivity | vx | right; reflexivity | a2 | a2 | apply (ge_fn_addr _ _ _ Hsync) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hsync) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hsync) | apply (ge_fn_check _ _ _ Hsync) | vx |
    apply (ge_fn_find _ _ _ Hsync) | reflexivity | reflexivity |]. iNext.
  iApply (Hspec with "Hvt0 Hl Hfl Hvtp HS"); [reflexivity |].
  iNext. iIntros (r fl' [Hr Hfl']) "Hl Hfl Hvtp HT". resume.
  destruct Hr as [-> | ->].
  - branch_as true. step. step.
    iApply (wp_fflush_unlock _ _ _ _ _ _ _ _ _ _ (pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) ∗ T 0 fl')%I
      with "Hs Hl Hfl Hlp Hlk [$Hvtp $HT]"); try close_side.
    { left. auto. }
    iNext. iIntros "Hl Hfl Hlp Hlk (Hvtp & HT)". iApply ("HK" with "[%] Hl Hfl Hvtp Hlp Hlk HT"). auto.
  - branch_as false.
    iApply (wp_fflush_unlock _ _ _ _ _ _ _ _ _ _ (pcell fb 216 (mkPtr (vb + vt_file) (Ro vb)) ∗ T (2 ^ 32 - 1) fl')%I
      with "Hs Hl Hfl Hlp Hlk [$Hvtp $HT]"); try close_side.
    { right. auto. }
    iNext. iIntros "Hl Hfl Hlp Hlk (Hvtp & HT)". iApply ("HK" with "[%] Hl Hfl Hvtp Hlp Hlk HT"). auto.
Qed.

(** ## Flushing an idle stream

    A failed write sets the error bit `c: _IO_ERR_SEEN` in the stream's
    flags and leaves every other bit alone. The two lemmas below show
    that the facts an idle stream keeps about its flags survive that. *)

(** Setting the error bit leaves every other bit as it was. *)
Lemma has_lor_err fl b : Z.land io_err_seen b = 0 -> has (Z.lor fl io_err_seen) b = has fl b.
Proof using Type. intros H. unfold has. rewrite Z.land_lor_distr_l H Z.lor_0_r. reflexivity. Qed.

(** The flags of a stream still pass [flags_ok] after a write sets the
    error bit, as long as an unbuffered stream marks a user buffer. A
    stream with a heap buffer does, because its buffer pointers are not
    null. *)
Lemma flags_ok_err st st' :
  flags_ok st -> (fs_flags st' = fs_flags st \/ fs_flags st' = Z.lor (fs_flags st) io_err_seen) ->
  fs_flags2 st' = fs_flags2 st -> 0 <= fs_flags st' < 2 ^ 32 ->
  (has (fs_flags st) io_unbuffered = true -> has (fs_flags st) io_user_buf = true) -> flags_ok st'.
Proof using Type.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hfl Hf2 Hr Hub. unfold flags_ok. rewrite Hf2.
  assert (E : forall b, Z.land io_err_seen b = 0 -> has (fs_flags st') b = has (fs_flags st) b).
  { intros b Hb. destruct Hfl as [-> | ->]; [reflexivity | apply has_lor_err, Hb]. }
  rewrite !E; try reflexivity. split_and!; try assumption.
  all: try solve [intros Hu; left; apply Hub, Hu | lia].
  destruct Hfl as [-> | ->]; [assumption|]. rewrite Z.land_lor_distr_l H2. reflexivity.
Qed.

(** A call `c: fflush (fp)` on an idle stream writes the output that
    waits in its heap buffer. It releases the lock it took, and it
    leaves the stream idle on the same descriptor. It returns 0, or
    `c: EOF` when the write fell short. A failed write sets errno, so
    the caller lends errno. *)
Lemma wp_fflush_idle fr fp vb vreg sb sreg fd eb Φ :
  call_frame Unit_libio_iofflush_os.fn___GI__IO_fflush [WPtr fp] = Some fr ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> ptr_addr (ow_self w0) <> 0 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗
  file_idle vb (ow_self w0) fp fd -∗ errno_any eb -∗
  ▷ (∀ r, ⌜r = 0 \/ r = 2 ^ 32 - 1⌝ -∗ file_idle vb (ow_self w0) fp fd -∗ errno_any eb -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Hdwf Hext Hfw Hreg Hsync Hwrite.
  intros Hfr Heb Hfd Hself. iIntros "#Hvt #Hs Hf Herr HK".
  iPoseProof (vtables_slot ge vb vreg slot_sync "_IO_new_file_sync" with "Hvt") as "#Hslot"; [cbn; tauto|].
  iDestruct "Hf" as (fb freg st nb Hp) "(Hl & Hf & Hlk & Hb & Hw)".
  destruct Hp as (-> & Hal & Hfb & Hend & Hfreg & Hok & Hidle & Hvt & Hbok & Hshort).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hf2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb &
    Hmd & Htot & Hvtp)".
  iDestruct "Hlk" as (lb lreg Hlb) "Hlk". rewrite Hlb Hvt.
  pose proof Hok as (Hflr & Hmagic & Hfilebuf & Hbk & Hul & Hnl & Hunb).
  unfold has in Hbk, Hul. apply negb_false_iff, Z.eqb_eq in Hbk. apply negb_false_iff, Z.eqb_eq in Hul.
  unfold file_size in Hend.
  iApply (wp_fflush_acquire Hreg Hext with "Hs Hl Hfl Hlp Hlk"); try eassumption; try lia.
  iIntros (e [Hv0 Hc0]) "Hl Hfl Hlp Hlk".
  destruct st as [fl ps fdd f2 oldoff col lk off cv wd frl frb md tw vt].
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable] in *.
  destruct ps as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]]; try discriminate Hlen.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  pose proof (buf_ptrs_in fb nb _ 3 Hbok eq_refl ltac:(lia)) as Hin3.
  pose proof (buf_ptrs_in fb nb _ 4 Hbok eq_refl ltac:(lia)) as Hin4. cbn [nth] in Hin3, Hin4.
  pose proof Hidle as Hidle'.
  unfold idle_ok, fs_ptr in Hidle'. cbn [nth fs_flags fs_ptrs fs_fileno fs_flags2 fs_column fs_mode] in Hidle'.
  destruct Hidle' as (Hfd012 & -> & Hmd & E8 & E9 & E11 & E01 & E13 & Hle34 & Hput & Hnw & Happ & Hlnk & Hf2a & Hf2b & Hcol2 & Hlk0).
  cbn [fs_lock] in Hlk0. rewrite Hlb in Hlk0. cbn [ptr_addr] in Hlk0.
  subst p0 p1.
  iDestruct (in_buf_range fb nb p3 with "Hb") as %Hr3; try first [exact Hin3 | lia].
  iDestruct (in_buf_range fb nb p4 with "Hb") as %Hr4; try first [exact Hin4 | lia].
  destruct (Z_le_gt_dec (ptr_addr p4) (ptr_addr p3)) as [Hq | Hpend].
  - (* Nothing is pending: the sync only marks the offset unknown. *)
    iApply (wp_fflush_dispatch e fb freg fl lb lreg sb sreg vb vreg
      (pcell fb 8 p3 ∗ pcell fb 16 p3 ∗ pcell fb 32 p3 ∗ pcell fb 40 p4 ∗ icell fb 144 off ∗ buf_idle nb)%I
      (fun r fl' => ⌜r = 0 /\ fl' = fl⌝ ∗ pcell fb 8 p3 ∗ pcell fb 16 p3 ∗ pcell fb 32 p3 ∗ pcell fb 40 p4 ∗
         icell fb 144 (2 ^ 64 - 1) ∗ buf_idle nb)%I
      with "Hvt Hslot Hs Hl Hfl Hvtp Hlp Hlk [$P0 $P1 $P3 $P4 $Hoff $Hb]"); try eassumption; try lia.
    { intros fr' Ψ Hfr'. iIntros "_ Hl Hfl Hvtp (H8 & H16 & H32 & H40 & Hoff & Hb) HK".
      iApply (wp_file_sync_quiet with "Hl Hfl H8 H16 H32 H40 Hoff Hb"); try eassumption; try lia.
      iNext. iIntros "Hl Hfl H8 H16 H32 H40 Hoff Hb".
      iApply ("HK" $! 0 fl with "[%] Hl Hfl Hvtp [$H8 $H16 $H32 $H40 $Hoff $Hb]"); [|done]. split; [left; done | exact Hul]. }
    iNext. iIntros (r fl' _) "Hl Hfl Hvtp Hlp Hlk ([-> ->] & P0 & P1 & P3 & P4 & Hoff & Hb)".
    iApply ("HK" with "[%] [-Herr] Herr"); [left; reflexivity|].
    iExists fb, freg, (mkFstate fl [p3; p3; p2; p3; p4; p5; p6; p7; p8; p9; p10; p11] fd f2 oldoff col
      (mkPtr lb (Obj lb)) (2 ^ 64 - 1) cv wd frl frb md tw (mkPtr (vb + vt_file) (Ro vb))), nb.
    iFrame "Hl Hb Hw". iSplitR; [iPureIntro; unfold file_size; split_and!; try done; lia|].
    iSplitR "Hlk"; [|iExists lb, lreg; iSplit; done].
    rewrite /file_fields. cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
      fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable big_opL].
    iFrame "Hfl P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 Hfd Hf2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp".
    iPureIntro. split; done.
  - (* Output is pending, so the buffer is a heap buffer. *)
    destruct nb as [| |bb sz|bb]; cbn [buf_ptrs_ok short_idle take] in Hbok, Hshort.
    { injection Hbok as _ _ _ <- <- _. cbn in Hpend. lia. }
    { unfold fs_ptr in Hshort. unfold short_idle in Hshort. cbn in Hshort. destruct Hshort as (_ & _ & -> & _). lia. }
    2: { iDestruct "Hb" as "[]". }
    cbn [nth] in Hbok. destruct Hbok as (-> & -> & Hall).
    repeat rewrite Forall_cons_iff in Hall.
    destruct Hall as (_ & _ & [Hc2 Ha2] & [Hc3 Ha3] & [Hc4 Ha4] & [Hc5 Ha5] & _).
    iDestruct "Hb" as (breg xs cs Hbp) "(Hbl & Hxs & Hcs)".
    pose proof Hbp as (Hk & Hbe & Hbreg & Hb0 & Hb8 & Hsz & Hlx & Hxr & Hlc).
    destruct p3 as [a3 c3], p4 as [a4 c4]. cbn [ptr_addr ptr_cap] in *. subst c3 c4.
    set (i := a3 - bb). set (k := Z.to_nat (a4 - a3)). set (ys := take k (drop (Z.to_nat i) xs)).
    iDestruct (bytes_take_drop bb 0 xs (Z.to_nat i) with "Hxs") as "[Hxa Hxb]"; [unfold i; lia|].
    iDestruct (bytes_take_drop bb (0 + Z.of_nat (Z.to_nat i)) (drop (Z.to_nat i) xs) k with "Hxb")
      as "[Hxm Hxc]"; [rewrite length_drop; unfold i, k; lia|].
    assert (Hys : Z.of_nat (length ys) = a4 - a3) by (unfold ys, k, i; rewrite length_take length_drop; lia).
    replace (0 + Z.of_nat (Z.to_nat i)) with i by (unfold i; lia).
    iDestruct (bytes_take_drop fb off_column col 2 with "Hcol") as "[Hcol Hcolr]"; [lia|]. rewrite Hcol2.
    change (take k (drop (Z.to_nat i) xs)) with ys.
    assert (Hputp : has fl io_currently_putting = true) by (apply Hput; left; lia).
    set (base := mkPtr bb (Obj bb)). set (be := mkPtr (bb + sz) (Obj bb)).
    iApply (wp_fflush_dispatch e fb freg fl lb lreg sb sreg vb vreg
      (int_cell fb off_flags2 f2 ∗ int_cell fb off_fileno fd ∗ icell fb off_total_written tw ∗ icell fb off_offset off ∗
       live bb breg ∗ bytes bb i ys ∗ errno_any eb ∗ pcell fb off_read_ptr (mkPtr (bb + i) (Obj bb)) ∗
       pcell fb 16 (mkPtr (bb + i) (Obj bb)) ∗ pcell fb 24 p2 ∗ pcell fb off_write_base (mkPtr (bb + i) (Obj bb)) ∗
       pcell fb off_write_ptr (mkPtr (bb + i + Z.of_nat (length ys)) (Obj bb)) ∗ pcell fb off_write_end p5 ∗
       pcell fb off_buf_base base ∗ pcell fb off_buf_end be ∗ bytes fb off_column [0; 0] ∗ int_cell fb off_mode md)%I
      (fun r fl2 => ∃ tw2 off2 we2, ⌜(fl2 = fl \/ fl2 = Z.lor fl io_err_seen) /\ (we2 = base \/ we2 = be)⌝ ∗
       int_cell fb off_flags2 f2 ∗ int_cell fb off_fileno fd ∗ icell fb off_total_written tw2 ∗ icell fb off_offset off2 ∗
       live bb breg ∗ bytes bb i ys ∗ errno_any eb ∗ pcell fb off_read_ptr base ∗ pcell fb 16 base ∗ pcell fb 24 base ∗
       pcell fb off_write_base base ∗ pcell fb off_write_ptr base ∗ pcell fb off_write_end we2 ∗
       pcell fb off_buf_base base ∗ pcell fb off_buf_end be ∗ bytes fb off_column [0; 0] ∗ int_cell fb off_mode md)%I
      with "Hvt Hslot Hs Hl Hfl Hvtp Hlp Hlk [Hf2 Hfd Htot Hoff Hbl Hxm Herr P0 P1 P2 P3 P4 P5 P6 P7 Hcol Hmd]");
      try eassumption; try lia.
    2: { replace (bb + i + Z.of_nat (length ys)) with a4 by (unfold i in *; lia).
         replace (bb + i) with a3 by (unfold i; lia). iFrame. }
    { intros fr2 Ψ Hfr2.
      iIntros "#Hvt1 Hl Hfl Hvtp (Hf2 & Hfd & Htot & Hoff & Hbl & Hxm & Herr & P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 &
        Hcol & Hmd) HK".
      iDestruct "Hf2" as "[%Hf2r Hf2]".
      assert (Happ0 : Z.land fl io_is_appending = 0)
        by (unfold has in Happ; apply negb_false_iff, Z.eqb_eq in Happ; exact Happ).
      iApply (wp_file_sync_pending _ fb freg fl f2 fd tw off bb breg i ys p2 p5 sz eb vb vreg md
        with "Hvt1 Hl Hfl [$Hf2 //] Hfd Htot Hoff Hbl Hxm Herr P0 P1 P2 P3 P4 P5 P6 P7 Hcol Hmd Hvtp");
        try eassumption; try lia.
      { unfold ys. apply Forall_take, Forall_drop, Hxr. }
      iNext. iIntros (r fl2 tw2 off2 [Hpost Hfl2r])
        "Hl Hfl Hf2 Hfd Htot Hoff Hbl Hxm Herr P0 P1 P2 P3 P4 P5 P6 P7 Hcol Hmd Hvtp".
      assert (Hfl2 : fl2 = fl \/ fl2 = Z.lor fl io_err_seen) by (destruct Hpost as [[_ ->] | [_ ->]]; auto).
      iApply ("HK" $! (if r =? Z.of_nat (length ys) then 0 else 2 ^ 32 - 1) fl2 with "[%] Hl Hfl Hvtp [-]").
      { split; [destruct (r =? _); auto|].
        destruct Hfl2 as [-> | ->]; [exact Hul|]. rewrite Z.land_lor_distr_l Hul. reflexivity. }
      iExists tw2, _, _. iFrame. iPureIntro. split; [exact Hfl2|]. destruct (Z.land fl2 514 =? 0); auto. }
    iNext. iIntros (r fl2 [Hr Hul2]) "Hl Hfl Hvtp Hlp Hlk (%tw2 & %off2 & %we2 & %Hpp & Hf2 & Hfd & Htot & Hoff &
      Hbl & Hxm & Herr & P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & Hcol & Hmd)".
    destruct Hpp as [Hfl2 Hwe2].
    iDestruct "Hfl" as "[%Hfl2r Hfl]".
    iApply ("HK" with "[%] [-Herr] Herr"); [exact Hr|].
    (* The buffer's bytes go back together. *)
    iAssert (bytes bb 0 xs) with "[Hxa Hxm Hxc]" as "Hxs".
    { rewrite (bytes_take_drop bb 0 xs (Z.to_nat i)); [|unfold i; lia].
      rewrite (bytes_take_drop bb (0 + Z.of_nat (Z.to_nat i)) (drop (Z.to_nat i) xs) k);
        [|rewrite length_drop; unfold i, k; lia].
      replace (0 + Z.of_nat (Z.to_nat i)) with i by (unfold i; lia). iFrame. }
    iCombine "Hcol Hcolr" as "Hcol". rewrite -Hcol2 -bytes_take_drop; [|lia].
    assert (Hub : has fl io_unbuffered = true -> has fl io_user_buf = true).
    { intros Hu. destruct (Hunb Hu) as [Hu' | Hnull]; [exact Hu'|]. cbn in Hnull. discriminate Hnull. }
    assert (Hhas : forall b, Z.land io_err_seen b = 0 -> has fl2 b = has fl b).
    { intros b Hb. destruct Hfl2 as [-> | ->]; [reflexivity | apply has_lor_err, Hb]. }
    iExists fb, freg, (mkFstate fl2 [base; base; base; base; base; we2; base; be; p8; p9; p10; p11] fd f2 oldoff col
      (mkPtr lb (Obj lb)) off2 cv wd frl frb md tw2 (mkPtr (vb + vt_file) (Ro vb))), (NbHeap bb sz).
    iFrame "Hl Hw". iSplitR.
    { iPureIntro. unfold file_size. split_and!; try done; try lia.
      - apply (flags_ok_err (mkFstate fl [mkPtr a3 (Obj bb); mkPtr a3 (Obj bb); p2; mkPtr a3 (Obj bb);
          mkPtr a4 (Obj bb); p5; base; be; p8; p9; p10; p11] fd f2 oldoff col (mkPtr lb (Obj lb)) off cv wd frl frb
          md tw vt)); cbn; auto.
      - unfold idle_ok, fs_ptr. cbn [nth fs_flags fs_ptrs fs_fileno fs_flags2 fs_column fs_mode ptr_addr].
        rewrite !Hhas; try reflexivity. split_and!; auto; try lia.
      - cbn. split_and!; try reflexivity.
        unfold base, be; destruct Hwe2 as [-> | ->]; repeat constructor; cbn; lia.
      - unfold short_idle in Hshort |- *. cbn [fs_flags] in Hshort |- *.
        rewrite !Hhas; try reflexivity. destruct Hshort as [Hs1 [Hs2 [_ [_ [Hs5 Hs6]]]]].
        split; [exact Hs1|]. split; [exact Hs2|]. unfold fs_ptr; cbn; split_and!; first [reflexivity | exact Hs5 | exact Hs6]. }
    iSplitR "Hlk Hbl Hxs Hcs"; [|iSplitL "Hlk"; [iExists lb, lreg; iSplit; done|]].
    { rewrite /file_fields. cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
        fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable big_opL].
      iFrame "Hfl P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 Hfd Hf2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp".
      iPureIntro. split_and!; first [done | lia]. }
    iExists breg, xs, cs. iFrame. done.
Qed.

End sync.

(** ## The contract

    Glibc's `c: error` flushes stdout and stderr between Hello's
    prints, so Hello needs a contract for that call. The code calls
    `c: fflush` by its internal name `c: __GI__IO_fflush`. The lemma
    below proves [fflush_spec] under that name for every program that
    links glibc's compiled functions. *)

Section has_spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge)
  (Hsync : ge_fn ge "_IO_new_file_sync" Unit_libio_fileops_os.fn__IO_new_file_sync)
  `{Hwrite : !Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  `{Hdwf : !Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}
  `{Hff : !Defines ge "__GI__IO_fflush" Unit_libio_iofflush_os.fn___GI__IO_fflush}.

(** The stream lock records its owner's thread pointer, and glibc's
    lock macros treat a null owner as no owner, so the thread pointer
    must not be null. *)
Lemma fflush_has_spec (Hself : ptr_addr (ow_self w0) <> 0) :
  HasSpec registry (os_wi w0) ge (TAtom "__GI__IO_fflush") fflush_spec.
Proof using Hdwf Hext Hff Hfw Hreg Hsync Hwrite.
  intros [vb fp fd eb]. exists Unit_libio_iofflush_os.fn___GI__IO_fflush. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. cbn [fs_pre fs_post fs_args fflush_spec ff_vb ff_fp ff_fd ff_eb].
  iIntros "([%Heb %Hfd] & Hf & Herr & (%vreg & %sb & %sreg & #Hvt & #Hs)) HK".
  iApply (wp_fflush_idle Hreg Hext Hsync Hfw with "Hvt Hs Hf Herr"); try eassumption.
  iNext. iIntros (r Hr) "Hf Herr". iApply "HK". iExists r. iFrame. iPureIntro. split; [reflexivity | exact Hr].
Qed.

End has_spec.
