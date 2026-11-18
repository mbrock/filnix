(** Glibc can change a stream's flags, counters and short byte while it
    sends a character. The stream stays usable for a second write only
    if every idle-stream fact still holds. In particular the write
    pointers must all point at the short byte, not just at each other. *)

From Stdlib Require Import ZArith List Lia.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Nanofil Require Import Term Syntax Values Memory Runtime Pieces Heap Logic MemLogic.
From Glibc Require Import GlibcProgram FileInv FileIdle FileTidy PrintfStreamInv LibioPutsInv LibioSetb OsBlocks
  LibioOverflowBase LibioOverflowShortWrite LibioOverflowShortStart LibioOverflowShortSend.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv.
Open Scope Z_scope.

(** The setup may set the user-buffer and writing bits. The write itself
    may set the error bit. No other flag changes. *)
Definition short_flags fresh fl fl' :=
  exists fl1, short_setup_flags fresh fl fl1 /\ (fl' = fl1 \/ fl' = Z.lor fl1 io_err_seen).

Lemma short_flags_mask fresh fl fl' m : short_flags fresh fl fl' ->
  Z.land 1 m = 0 -> Z.land 2048 m = 0 -> Z.land io_err_seen m = 0 -> Z.land fl' m = Z.land fl m.
Proof.
  intros (fl1 & Hs & [-> | ->]) H1 H2 He; [|rewrite land_lor_const //];
    destruct fresh; destruct Hs as [-> | ->]; unfold setb_flags, io_user_buf; cbn [Z.eqb];
    repeat rewrite land_lor_const //; reflexivity.
Qed.

Lemma short_flags_user fresh fl fl' : short_flags fresh fl fl' ->
  (fresh = false -> has fl io_user_buf = true) -> has fl' io_user_buf = true.
Proof.
  intros (fl1 & Hs & [-> | ->]) Hu; unfold has in *; [|rewrite land_lor_const //];
    destruct fresh; destruct Hs as [-> | ->]; unfold setb_flags, io_user_buf; cbn [Z.eqb];
    try rewrite (land_lor_const _ 2048 1 eq_refl); try apply (Hu eq_refl);
    rewrite Z.land_lor_distr_l; change (Z.land 1 1) with 1; apply Bool.negb_true_iff, Z.eqb_neq;
    intro H; apply Z.lor_eq_0_iff in H; lia.
Qed.

(** The write changes only the first eight buffer pointers. The next
    four pointers still link the same objects as before the call. *)
Definition short_after st fb fl rb tw off col mode :=
  let sb := short_ptr fb in
  mkFstate fl [sb; sb; rb; sb; sb; sb; sb; mkPtr (fb+132) (Obj fb); fs_ptr st 8; fs_ptr st 9; fs_ptr st 10; fs_ptr st 11]
    (fs_fileno st) (fs_flags2 st) (fs_old_offset st) col (fs_lock st) off
    (fs_codecvt st) (fs_wide st) (fs_freeres_list st) (fs_freeres_buf st) mode tw (fs_vtable st).

(** The next write needs an empty stream on both return paths. An empty
    flush can leave the read base alone, while a byte write resets it.
    In both cases the write pointers point at the short byte. *)
Lemma short_after_idle st fresh fd fb fl rb tw off col mode :
  let nb := if fresh : bool then NbNone else NbShort in let st' := short_after st fb fl rb tw off col mode in
  flags_ok st -> idle_ok fd (fs_with_flags2 st 0) -> short_idle nb st -> buf_ptrs_ok fb nb (fs_ptrs st) ->
  has (fs_flags st) io_unbuffered = true -> has (fs_flags st) io_no_writes = false ->
  short_flags fresh (fs_flags st) fl -> 0 <= fl < 2^32 ->
  in_buf fb NbShort rb -> take 2 col = [0;0] -> (mode = 0 \/ mode = 2^32-1) ->
  flags_ok st' /\ idle_ok fd (fs_with_flags2 st' 0) /\ short_idle NbShort st' /\ buf_ptrs_ok fb NbShort (fs_ptrs st').
Proof.
  cbn zeta. intros (Hf & Hmagic & Hfile & Hbk & Hul & Hlock & Huser) Hi [[Hline _] Hshort] Hb Hu Hnw0 Hfl Hrange Hrb Hcol Hmd.
  assert (E : forall m, Z.land 1 m = 0 -> Z.land 2048 m = 0 -> Z.land io_err_seen m = 0 ->
    has fl m = has (fs_flags st) m) by (intros; unfold has; rewrite (short_flags_mask _ _ _ _ Hfl) //).
  assert (Euser : has fl io_user_buf = true).
  { apply (short_flags_user _ _ _ Hfl). intros ->. destruct (Huser Hu) as [H|H]; [exact H|].
    destruct Hb as [Hb _]. assert (H6 : nth 6 (fs_ptrs st) null = nth 6 (take 8 (fs_ptrs st)) null).
    { destruct (fs_ptrs st) as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 xs]]]]]]]; reflexivity. }
    rewrite H6 H in Hb. discriminate. }
  destruct Hi as (Hfd & Hid & _ & H8 & H9 & H11 & _ & _ & _ & _ & Hnw & Happ & Hlnk & _ & _ & _ & Hlk0).
  unfold flags_ok, idle_ok, short_idle, short_after, fs_with_flags2, fs_ptr in *.
  cbn [fs_flags fs_flags2 fs_ptrs fs_mode fs_fileno fs_column app nth] in *.
  split_and!;
    try solve [assumption | reflexivity | reflexivity || lia | rewrite E; auto; reflexivity |
      rewrite (short_flags_mask _ _ _ _ Hfl); auto; reflexivity | intros; left; assumption |
      intros; rewrite E; auto; reflexivity | intros; apply Hline; assumption | intros [Ha|Ha]; lia |
      rewrite E; auto; [rewrite Hnw0; discriminate | reflexivity..]].
  unfold buf_ptrs_ok. cbn [app nth take]. split_and!; try reflexivity.
  unfold in_buf in Hrb. unfold short_ptr, off_shortbuf. repeat constructor; cbn in *; intuition lia.
Qed.

Section fields.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The first call sees null pointers. A later call sees the short byte
    as the start and end of the write window. The read base need not
    coincide with the other read pointers. *)
Definition short_input fb (fresh : bool) rb : iProp Σ :=
  let p := if fresh then null else short_ptr fb in
  let be := if fresh then null else mkPtr (fb+132) (Obj fb) in
  pcell fb off_read_ptr p ∗ pcell fb 16 p ∗ pcell fb 24 rb ∗ pcell fb off_write_base p ∗
  pcell fb off_write_ptr p ∗ pcell fb off_write_end p ∗ pcell fb off_buf_base p ∗ pcell fb off_buf_end be.

(** The caller lends the fields used by overflow and keeps the rest of
    the stream. In particular, writing the fourth byte of the column
    field must not change the first two bytes, which hold the column. *)
Lemma short_fields vb self fb freg st (fresh : bool) fd flags2 held eb :
  let nb := if fresh then NbNone else NbShort in let fl := fs_flags st in
  fb mod 8 = 0 -> 0 < fb -> fb + file_size <= r_end freg -> r_end freg <= 2^63 ->
  flags_ok st -> idle_ok fd (fs_with_flags2 st 0) -> fs_flags2 st = flags2 ->
  fs_vtable st = mkPtr (vb+vt_file) (Ro vb) -> buf_ptrs_ok fb nb (fs_ptrs st) -> short_idle nb st ->
  has fl io_unbuffered = true -> has fl io_no_writes = false ->
  file_fields fb st -∗ lock_inv self (fs_lock st) held -∗ wide_idle vb (fs_wide st) (fs_codecvt st) -∗
  errno_any eb -∗ ∃ rb byte,
  short_input fb fresh rb ∗ int_cell fb off_flags fl ∗ icell fb off_total_written (fs_total st) ∗
  icell fb off_offset (fs_offset st) ∗ bytes fb off_shortbuf [byte] ∗ ovf_fixed fb flags2 fd eb (fs_mode st) vb ∗
  (∀ rb' byte' fl' tw' off' mode', ⌜((fresh = false /\ rb' = rb) \/ rb' = short_ptr fb) /\
       short_flags fresh fl fl' /\ (mode' = 0 \/ mode' = 2^32-1)⌝ -∗
    live fb freg -∗ short_state fb rb' fl' tw' off' byte' -∗ ovf_fixed fb flags2 fd eb mode' vb -∗
    file_tidy vb self (mkPtr fb (Obj fb)) fd flags2 held ∗ errno_any eb).
Proof using Type.
  cbn zeta. intros Hal Hfb Hend Hrend Hok Hi Hf2 Hvt Hb Hshort Hu Hnw0.
  iIntros "(%Hlen & Hfl & Hps & Hfd & Hf2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb & Hmd & Htw & Hvt) Hlk Hw Herr".
  pose proof (buf_ptrs_in _ _ _ 2 Hb Hlen ltac:(lia)) as Hin.
  pose proof Hi as (_ & Hfd & _ & _ & _ & _ & H01 & H13 & _ & _ & _ & _ & _ & _ & _ & Hcol & _).
  cbn [fs_with_flags2 fs_fileno fs_column] in Hfd, Hcol. subst fd flags2.
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Hps; try discriminate Hlen.
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  destruct (fs_column st) as [|a [|b [|c [|x xs]]]] eqn:Hcs; try discriminate Hcl. injection Hcol as -> ->.
  change (0::0::c::x::xs) with ([0;0] ++ [c] ++ [x] ++ xs).
  iEval (rewrite !bytes_app) in "Hcol". iDestruct "Hcol" as "(Hcol & Hc & Hx & Hxs)".
  iExists p2, x. iFrame "Hfl Htw Hoff Hx". iSplitL "P0 P1 P2 P3 P4 P5 P6 P7".
  { unfold fs_ptr, fs_with_flags2 in H01, H13. cbn [fs_ptrs] in H01, H13. rewrite Hps in H01, H13. cbn [nth] in H01, H13.
    subst p0 p1. destruct fresh; cbn [short_input].
    - injection Hb as ? ? ? ? ? ? ? ?. subst. iFrame.
    - destruct Hb as (Hb6 & Hb7 & _). cbn [nth] in Hb6, Hb7.
      destruct Hshort as (_ & _ & H43 & H54 & H36). unfold fs_ptr in H43, H54, H36.
      rewrite Hps in H43, H54, H36. cbn [nth] in H43, H54, H36. subst. iFrame. }
  iEval (rewrite Hvt) in "Hvt". iFrame "Hf2 Hfd Herr Hcol Hmd Hvt".
  iIntros (rb' byte' fl' tw' off' mode' (Hrb & Hflags & Hmode)) "Hl (Hs & [%Hrange Hfl] & Htw & Hoff & Hx) (Hf2 & Hfd & $ & Hcol & Hmd & Hvt)".
  set (col' := [0;0;c;byte'] ++ xs). set (st' := short_after st fb fl' rb' tw' off' col' mode').
  assert (Hin' : in_buf fb NbShort rb').
  { destruct Hrb as [[-> ->]| ->]; [exact Hin | unfold in_buf, short_ptr, off_shortbuf; cbn; intuition lia]. }
  pose proof (short_after_idle st fresh (fs_fileno st) fb fl' rb' tw' off' col' mode' Hok Hi Hshort
    ltac:(rewrite Hps; exact Hb) Hu Hnw0 Hflags Hrange Hin' eq_refl Hmode) as Hpost.
  iExists fb, freg, st', NbShort. iSplit; [iPureIntro; intuition|]. iFrame "Hl Hlk Hw".
  iDestruct "Hs" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7)".
  unfold st', short_after, file_fields, fs_ptr. cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
    fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable]. rewrite Hps Hvt. cbn [nth big_opL].
  iFrame "Hfd Hf2 Hold Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htw Hvt P0 P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11".
  iSplit; [done|]. iSplitL "Hfl"; [iFrame; done|]. iSplit; [iPureIntro; unfold col'; cbn in *; lia|].
  change col' with ([0;0] ++ [c] ++ [byte'] ++ xs). rewrite !bytes_app. iFrame.
Qed.
End fields.
