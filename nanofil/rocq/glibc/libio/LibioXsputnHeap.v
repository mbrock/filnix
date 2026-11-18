(** A buffered stream that may be written has either no buffer yet or
    a heap buffer. Writing a string to such a stream runs glibc's whole
    `c: _IO_new_file_xsputn`: it copies bytes into the buffer, calls the
    overflow function to allocate or flush the buffer, and writes long
    strings straight to the descriptor. LibioXsputn.v proves that code
    over the stream's write buffer and a few of its fields. This file
    gives that proof a tidy stream and takes a tidy stream back, so that
    `c: fputs` and the formatter's flush can call it on stdout. *)

From Glibc Require Import GlibcProgram GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysCode SysWrappers FileInv FileIdle FileTidy LibioLogic
  LibioGenCode LibioReadCode LibioDoWriteCode LibioXsputnCode LibioOverflowBase LibioStreamTidy
  LibioFputsSpec PrintfStreamInv AllocRo AllocLogic MemFwdCode LibioDefaultXsputnBuf LibioXsputnBase LibioXsputn LibioWriteDq
  LibioOverflowHeapBuffer LibioOverflowHeapIdle.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

(** ## The flags a string write keeps

    String output keeps a fact about the stream's flags from one block
    to the next, as the class [XsFlags] in LibioXsputnBase.v describes.
    For a tidy stream that fact is the part of [flags_ok], [idle_ok] and
    [short_idle] that the flags alone decide. *)

(** A buffered stream that may be written keeps these flags across a
    write. It is a file stream with the magic number, it has no backup
    area or user lock, it is buffered, writable, not appending, and it
    stays on the list of open streams. *)
Definition tidy_fl (fl : Z) : Prop :=
  Z.land fl 4294901760 = io_magic /\ has fl io_is_filebuf = true /\ has fl io_in_backup = false /\
  has fl io_user_lock = false /\ has fl io_unbuffered = false /\ has fl io_no_writes = false /\
  has fl io_is_appending = false /\ has fl io_linked = true.

(** Such a stream is putting exactly when it has a buffer, and its
    heap buffer belongs to the stream rather than to the user. *)
Definition tidy_xs_flags (nb : option (Z * Z)) (fl : Z) : Prop :=
  tidy_fl fl /\ match nb with
  | None => has fl io_currently_putting = false
  | Some _ => has fl io_currently_putting = true /\ has fl io_user_buf = false
  end.

(** A bit other than the error bit has the same value after a failed
    write sets the error bit. *)
Lemma has_err_other fl m : Z.land io_err_seen m = 0 -> has (Z.lor fl io_err_seen) m = has fl m.
Proof. intros H. unfold has. rewrite land_lor_const //. Qed.

(** A failed write sets only the error bit, so it keeps the fact. *)
Lemma tidy_xs_flags_error nb fl : tidy_xs_flags nb fl -> tidy_xs_flags nb (Z.lor fl io_err_seen).
Proof.
  unfold tidy_xs_flags, tidy_fl. rewrite land_lor_const; [|reflexivity].
  rewrite !has_err_other; try reflexivity. tauto.
Qed.

(** A clear bit has a zero mask. *)
Lemma has_false_land fl m : has fl m = false -> Z.land fl m = 0.
Proof. unfold has. intros H. apply Bool.negb_false_iff, Z.eqb_eq in H. exact H. Qed.

(** The overflow function allocates a buffer or flushes the one it has.
    Either way it leaves the stream putting, with a buffer that the
    stream owns, and it touches no other bit of the fact. *)
Lemma tidy_xs_flags_ovf nb fl fl' bb sz :
  tidy_xs_flags nb fl -> heap_overflow_flags nb fl fl' -> tidy_xs_flags (Some (bb, sz)) fl'.
Proof.
  intros [Hfl Hput] Hov.
  destruct (heap_flags_owned nb fl fl' Hov) as [Hub Hp].
  { intros Hnb. destruct nb; [tauto | congruence]. }
  assert (E : forall m, Z.land 4294967294 m = m -> Z.land io_line_buf m = 0 -> Z.land 2048 m = 0 ->
    Z.land io_err_seen m = 0 -> has fl' m = has fl m)
    by (intros; unfold has; rewrite (heap_flags_mask _ _ _ _ Hov) //).
  unfold tidy_xs_flags, tidy_fl in *. rewrite (heap_flags_mask _ _ _ _ Hov); try reflexivity.
  rewrite (E io_is_filebuf) ?(E io_in_backup) ?(E io_user_lock) ?(E io_unbuffered) ?(E io_no_writes)
    ?(E io_is_appending) ?(E io_linked); try reflexivity. tauto.
Qed.

(** ## A tidy stream as the string writer's state

    The proof of `c: _IO_new_file_xsputn` owns the write buffer and the
    fields that the overflow function and the direct write use. A tidy
    stream owns those and more. This section splits a tidy stream into
    the writer's part and the rest, and puts it back together after the
    write, whatever buffer the write leaves behind. *)

Section tidy.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The writer keeps the second flags word f20 and the descriptor fd0
    of the stream it was given. *)
Context (f20 fd0 : Z).
#[local] Instance tidy_xs : XsFlags :=
  {| xs_flags := tidy_xs_flags; xs_flags_error := tidy_xs_flags_error; xs_fixed := fun f2 fd => f2 = f20 /\ fd = fd0 |}.

(** To rebuild the stream, the caller must know where the write
    pointers lie. They are null before the first allocation and lie
    inside the heap buffer after it. *)
Definition wroom_ok (nb : option (Z * Z)) (wp we : ptr) : Prop :=
  match nb with
  | None => wp = null /\ we = null
  | Some (b, sz) => 0 < b /\ 0 < sz /\ in_buf b sz wp /\ in_buf b sz we
  end.

Lemma wroom_facts nb wp we : wroom nb wp we ⊢ ⌜wroom_ok nb wp we⌝ ∗ wroom nb wp we.
Proof using Type.
  destruct nb as [[b sz]|]; cbn [wroom wroom_ok].
  - iIntros "(%reg & %xs & %cs & %Hr & H)". iSplit; [iPureIntro; unfold room_ok in Hr; tauto|].
    iExists reg, xs, cs. iFrame. done.
  - iIntros "%H". iSplit; done.
Qed.

(** The state after a write keeps every field the writer does not own.
    The writer's own fields come from what it hands back. *)
Definition xs_after (st : fstate) (nb : option (Z * Z)) (wp we : ptr) (fl tw off m : Z) : fstate :=
  let b := nb_base nb in
  mkFstate fl ([b; b; b; b; wp; we; b; nb_end nb] ++ drop 8 (fs_ptrs st)) (fs_fileno st) (fs_flags2 st)
    (fs_old_offset st) (fs_column st) (fs_lock st) off (fs_codecvt st) (fs_wide st) (fs_freeres_list st)
    (fs_freeres_buf st) m tw (fs_vtable st).

(** After a write, the next call on the stream must find it tidy
    again. The stream is putting exactly when it has a buffer, and every
    read and write pointer lies inside that buffer. *)
Lemma xs_after_idle st nb wp we fl tw off m fb :
  length (fs_ptrs st) = 12%nat -> flags_ok st -> idle_ok (fs_fileno st) (fs_with_flags2 st 0) ->
  tidy_xs_flags nb fl -> 0 <= fl < 2 ^ 32 -> (m = 0 \/ m = 2 ^ 32 - 1) -> wroom_ok nb wp we ->
  let st' := xs_after st nb wp we fl tw off m in
  flags_ok st' /\ idle_ok (fs_fileno st) (fs_with_flags2 st' 0) /\
  buf_ptrs_ok fb (heap_kind nb) (fs_ptrs st') /\ short_idle (heap_kind nb) st'.
Proof.
  intros Hlen Hok Hi [Hfl Hput] Hrange Hm Hw. cbn zeta.
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Hps;
    try discriminate Hlen.
  unfold tidy_fl in Hfl. unfold flags_ok, idle_ok, short_idle, xs_after, fs_with_flags2, fs_ptr in *.
  rewrite Hps in Hi |- *.
  cbn [fs_flags fs_flags2 fs_ptrs fs_fileno fs_mode fs_lock fs_column nth drop app] in *.
  decompose [and] Hi. decompose [and] Hok. decompose [and] Hfl.
  destruct nb as [[b sz]|]; cbn [heap_kind nb_base nb_end wroom_ok buf_ptrs_ok take] in *.
  - destruct Hw as (Hb & Hsz & [Hwpc Hwpa] & [Hwec Hwea]). destruct Hput as [Hput Hub].
    split_and!; try solve [assumption | reflexivity | lia | congruence | intros; assumption];
      try (cbn; lia); repeat constructor; cbn; first [assumption | lia].
  - destruct Hw as [-> ->].
    split_and!; try solve [assumption | reflexivity | lia | congruence | intros; assumption];
      cbn; first [lia | intros [H|H]; lia].
Qed.

(** The writer needs only some of the stream's fields, but the caller
    owns the whole stream. So the caller lends the writer the buffer,
    the fields it writes and the jump-table pointer, and keeps the
    rest. When the writer returns any buffer and fields that keep its
    facts, the caller puts the stream back together as a tidy stream. *)
Lemma tidy_xs_open fb st nb eb vb :
  fs_flags2 st = f20 -> fs_fileno st = fd0 ->
  flags_ok st -> idle_ok (fs_fileno st) (fs_with_flags2 st 0) -> short_idle nb st ->
  buf_ptrs_ok fb nb (fs_ptrs st) -> fs_vtable st = mkPtr (vb + vt_file) (Ro vb) ->
  has (fs_flags st) io_unbuffered = false -> has (fs_flags st) io_no_writes = false -> In (fs_fileno st) (ow_fds w0) ->
  file_fields fb st -∗ buf_idle nb -∗ errno_any eb -∗
  ∃ onb, ⌜nb = heap_kind onb⌝ ∗ wbuf fb onb (fs_ptr st 4) (fs_ptr st 5) ∗ xfields w0 eb fb onb ∗
    pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) ∗
    (∀ nb' wp' we', wbuf fb nb' wp' we' -∗ xfields w0 eb fb nb' -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
      ∃ st', ⌜flags_ok st' /\ idle_ok (fs_fileno st) (fs_with_flags2 st' 0) /\ fs_flags2 st' = fs_flags2 st /\
        fs_vtable st' = fs_vtable st /\ buf_ptrs_ok fb (heap_kind nb') (fs_ptrs st') /\ short_idle (heap_kind nb') st' /\
        fs_lock st' = fs_lock st /\ fs_wide st' = fs_wide st /\ fs_codecvt st' = fs_codecvt st⌝ ∗
      file_fields fb st' ∗ buf_idle (heap_kind nb') ∗ errno_any eb).
Proof using Type.
  intros Hf2 Hfd Hok Hi Hshort Hb Hvt Hu Hnw Hin.
  iIntros "(%Hlen & Hfl & Hps & Hfdc & Hfl2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb & Hmd & Htw & Hvtp) Hb Herr".
  iAssert (∃ onb, ⌜nb = heap_kind onb⌝ ∗ buf_idle nb)%I with "[Hb]" as (onb ->) "Hb".
  { destruct nb as [| |bb sz|b]; [iExists None; iFrame; done | destruct Hshort as (_ & H & _); congruence |
    iExists (Some (bb,sz)); iFrame; done | iDestruct "Hb" as "[]"]. }
  iExists onb. iSplit; [done|]. unfold fs_with_flags2, fs_ptr in *. cbn [fs_ptrs] in *.
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Hps; try discriminate Hlen.
  pose proof Hi as (Hfd012 & _ & Hmd & _ & _ & _ & H01 & H13 & _ & _ & _ & Happ & Hlk & _ & _ & Hcol0 & _).
  pose proof Hok as (_ & Hmag & Hfb & Hbk & Hul & _ & _).
  unfold fs_with_flags2, fs_ptr in *. cbn [fs_flags fs_mode fs_column fs_ptrs nth] in *.
  assert (Hflags : tidy_xs_flags onb (fs_flags st)).
  { split; [unfold tidy_fl; tauto|]. destruct onb as [[bb sz]|]; cbn [heap_kind short_idle] in Hshort.
    - destruct Hshort as (_ & _ & _ & _ & Hub & Hput). auto.
    - destruct Hshort as (_ & Hput). exact Hput. }
  iDestruct "Hps" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  iSplitL "P0 P1 P2 P3 P4 P5 P6 P7 Hb".
  { destruct onb as [[bb sz]|]; cbn [heap_kind] in *.
    - destruct Hshort as (_ & _ & H26 & H36 & _). unfold fs_ptr in H26, H36. rewrite Hps in H26, H36. cbn [nth] in H26, H36.
      destruct Hb as (H6 & H7 & Hall). cbn [nth take] in H6, H7, Hall. subst p0 p1 p2 p3 p6 p7.
      repeat (apply Forall_cons_1 in Hall; destruct Hall as [? Hall]).
      iDestruct "Hb" as (br xs cs (Hheap & Hend & Hr & Hbb & Hal & Hsz & Hlenx & Hxs & Hlenc)) "(Hl & Hxs & Hcs)".
      unfold wbuf, wcells. cbn [nb_base nb_end]. iFrame.
      iPureIntro. unfold room_ok, in_buf. split_and!; first [assumption | tauto | lia].
    - cbn [buf_ptrs_ok take] in Hb. injection Hb as -> -> -> -> -> -> -> ->. unfold wbuf, wcells. cbn [nb_base nb_end wroom].
      iFrame "P0 P1 P2 P3 P4 P5 P6 P7". done. }
  iEval (rewrite -{1}(take_drop 2 (fs_column st)) Hcol0 bytes_app) in "Hcol". iDestruct "Hcol" as "[Hcol Htail]".
  iEval (rewrite Hvt) in "Hvtp". iFrame "Hvtp".
  iSplitL "Hfl Hfl2 Hfdc Htw Hoff Hcol Hmd Herr".
  { iExists (fs_flags st), (fs_flags2 st), (fs_fileno st), (fs_total st), (fs_offset st), (fs_mode st).
    iFrame. iPureIntro. split_and!; try assumption; try lia; [apply has_false_land, Happ | split; assumption]. }
  iIntros (nb' wp' we') "((Q0 & Q1 & Q2 & Q3 & Q6 & Q7) & Q4 & Q5 & Hroom) Hxf Hvtp".
  iDestruct (wroom_facts with "Hroom") as "[%Hw Hroom]".
  iDestruct "Hxf" as (fl f2 fd tw off m (Happ' & [Ef2 Efd] & Hin' & Hm & Hflags' & Hfd31))
    "(Hfl & Hfl2 & Hfdc & Htw & Hoff & Hcol & Hmode & Herr)".
  iDestruct "Hfl" as "[%Hrange Hfl]". subst f2 fd.
  iExists (xs_after st nb' wp' we' fl tw off m).
  pose proof (xs_after_idle st nb' wp' we' fl tw off m fb ltac:(rewrite Hps; reflexivity) Hok ltac:(unfold fs_with_flags2; rewrite Hps; exact Hi) Hflags' Hrange Hm Hw)
    as (Hok' & Hi' & Hb' & Hsh').
  iSplit. { iPureIntro. unfold xs_after. cbn [fs_flags2 fs_vtable fs_lock fs_wide fs_codecvt]. tauto. }
  iSplitR "Hroom Herr"; last first.
  { iFrame "Herr". destruct nb' as [[bb sz]|]; cbn [heap_kind buf_idle wroom]; [|done].
    iDestruct "Hroom" as (br xs cs Hr) "(Hl & Hxs & Hcs)". iExists br, xs, cs. iFrame. iPureIntro.
    unfold room_ok in Hr. tauto. }
  unfold xs_after, file_fields. rewrite Hps. cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
    fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable drop app big_opL].
  rewrite Hf2 Hfd. iEval (rewrite -Hvt) in "Hvtp".
  iFrame "Hfdc Hfl2 Hold Hlp Hoff Hcv Hwd Hfrl Hfrb Hmode Htw Hvtp Q0 Q1 Q2 Q3 Q4 Q5 Q6 Q7 P8 P9 P10 P11".
  iSplit; [done|]. iSplitL "Hfl"; [iFrame; done|]. iSplit; [done|].
  iEval (rewrite -{1}(take_drop 2 (fs_column st)) Hcol0 bytes_app). iFrame.
Qed.

End tidy.

(** ## The write

    A string write calls two other functions of glibc. It calls the
    overflow function when the buffer is full, and it writes a long
    string straight to the descriptor. The proof of the writer takes a
    rule for each call, and this section proves both rules for a tidy
    stream before it proves the write itself. *)

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" glibc__IO_file_stat)
  `{!Defines ge "__GI___fstat64" glibc___fstat64} `{!Defines ge "__gnu_dev_major" glibc___gnu_dev_major}
  `{!Defines ge "__isatty_nostatus" glibc___isatty_nostatus} `{!Defines ge "__GI__IO_setb" glibc__IO_setb}.
Context `{!Defines ge "free" free_fn} (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context `{!Defines ge "malloc" malloc_fn} `{!Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn}.
Context (Hda : ge_fn ge "__GI__IO_file_doallocate" glibc__IO_file_doallocate)
  `{!Defines ge "__GI__IO_doallocbuf" glibc__IO_doallocbuf}.
Context `{!Defines ge "__GI___write" glibc___libc_write} (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  `{!Defines ge "_IO_new_do_write" glibc__IO_new_do_write}.
Context (Hov : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow).
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  `{!Defines ge "__GI_memcpy" glibc_memcpy} `{!Defines ge "__GI_mempcpy" glibc_mempcpy}
  `{!Defines ge "__GI__IO_default_xsputn" glibc__IO_default_xsputn}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The direct write may use the noncanceling system call only when the
    program has it. The stream keeps the second flags word it started
    with, so the caller's fact about that word covers every write. *)
Lemma tidy_fwq f20 fd0 :
  (Z.land f20 2 = 0 \/ Z.land f20 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  xs_fwq_spec (XF := tidy_xs f20 fd0) w0 registry ge.
Proof using Type*.
  intros Hready. split.
  - intros fr fb freg fl f2 fd tw off dq' b reg o c xs eb Φ Hfr Hc Hfb Hal Hend Hregend Hf2 Hf2r Hfd Hfl Heb
      Hb Ho Hbend Hbreg Hxs.
    iIntros "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK".
    iApply (wp_glibc__IO_new_file_write_dq Hreg Hext fr fb freg fl f2 fd tw off dq' b reg c o xs eb with
      "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK"); try assumption.
  - intros f2 fd [-> _]. exact Hready.
Qed.

(** The overflow call allocates the first buffer or flushes the one the
    stream has. It keeps the descriptor, the second flags word and the
    flags fact, and it leaves a buffer behind on every path. *)
Lemma tidy_overflow f20 fd0 eb :
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd0 (ow_fds w0) ->
  (Z.land f20 2 = 0 \/ Z.land f20 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  overflow_spec w0 registry ge (xos (XF := tidy_xs f20 fd0) w0 eb (fun _ _ => malloc_ro)).
Proof using Type*.
  intros He Hin Hready fr fb freg nb wp we ch vb vreg Φ Hfr Hch Hfb Hal Hend Hr.
  iIntros "#Hvt Hl Hvtp Hbuf [Hxf #HM] HK".
  iDestruct "Hxf" as (fl f2 fd tw off m (Happ & [-> ->] & _ & Hm & Hflags & Hfd31))
    "(Hfl & Hfl2 & Hfdc & Htw & Hoff & Hcol & Hmode & Herr)".
  destruct Hflags as [Hfl Hput]. pose proof Hfl as (_ & _ & Hbk & _ & Hu & Hnw & _ & _).
  iApply (wp_heap_file_buffer Hreg Hext Hstat Hfh Hzf Hzg Hda Hfw fr fb freg ch f20 fd0 eb m vb vreg nb wp we fl tw off
    with "Hvt HM Hl [$Hfl2 $Hfdc $Herr $Hcol $Hmode $Hvtp] Hbuf Hfl Htw Hoff"); try first [assumption | lia].
  1-3: apply has_false_land; assumption.
  { intros ->. apply has_false_land. exact Hput. }
  iNext. iIntros (r bb sz k we' fl' tw' off' (Hr' & Hnb & Hflags')) "Hl (Hfl2 & Hfdc & Herr & Hcol & Hmode & Hvtp) Hbuf Hfl Htw Hoff".
  pose proof (tidy_xs_flags_ovf nb fl fl' bb sz (conj Hfl Hput) Hflags') as Hxs'.
  iApply ("HK" with "[%] Hl Hvtp Hbuf [-]"); [split; [exact Hr' | discriminate]|].
  iFrame "HM". iExists fl', f20, fd0, tw', off', m. iFrame. iPureIntro.
  pose proof Hxs' as [(_ & _ & _ & _ & _ & _ & Happ' & _) _].
  split_and!; try assumption; try lia; try (apply has_false_land, Happ'); try (split; reflexivity).
Qed.

(** A buffered stream that may be written takes a string and gives
    back a tidy stream with the same descriptor, second flags word and
    lock state. It returns the caller's share of the source, whether the
    write succeeded, wrote part of the string or failed. *)
Theorem wp_xsputn_heap : xsputn_heap_rule.
Proof using Type*.
  intros fr vb self fb freg st nb flags2 held dq b reg o c ys eb Φ fp n fd Hfr Hal Hfb Hend Hr Hok Hi Ef2 Hvt Hbp
    Hshort Hu Hnw Hready He Hin Hg Hc Hb Hb8 Ho Hbend Hbreg Hy.
  iIntros "#Hro #HM Hl Hf Hlk Hb Hw Herr Hbl Hys HK". subst fp fd n.
  iDestruct "Hro" as (vr sb sr) "[#Hvt _]".
  iDestruct (tidy_xs_open (fs_flags2 st) (fs_fileno st) fb st nb eb vb with "Hf Hb Herr")
    as (onb ->) "(Hwb & Hxf & Hvtp & Hclose)"; try done.
  iApply (wp_glibc__IO_new_file_xsputn (XF := tidy_xs (fs_flags2 st) (fs_fileno st)) Hmove Hmove_fn Hmove_sym Hfw
    (tidy_fwq (fs_flags2 st) (fs_fileno st) ltac:(rewrite Ef2; exact Hready)) fr eb (fun _ _ => malloc_ro) fb freg vb vr onb (fs_ptr st 4) (fs_ptr st 5)
    dq b reg o c ys with "Hvt Hl Hvtp Hwb [$Hxf $HM] Hbl Hys"); try assumption.
  { apply tidy_overflow; [exact He | exact Hin | rewrite Ef2; exact Hready]. }
  iNext. iIntros (r nb' wp' we' [Hret _]) "Hl Hvtp Hwb [Hxf _] Hbl Hys".
  iDestruct ("Hclose" with "Hwb Hxf Hvtp") as (st' (Hok' & Hi' & Hf2' & Hvt' & Hbp' & Hsh' & Hlk' & Hwd' & Hcv'))
    "(Hf & Hb & Herr)".
  iApply ("HK" with "[%] [-Herr Hbl Hys] Herr Hbl Hys"); [exact Hret|].
  iExists fb, freg, st', (heap_kind nb'). rewrite Hlk' Hwd' Hcv'. iFrame "Hl Hf Hlk Hb Hw".
  iPureIntro. split_and!; try assumption; try congruence; reflexivity.
Qed.
End rules.
