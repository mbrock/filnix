(** A call of `c: fprintf` formats into a small buffer object, and that
    buffer hands its bytes to the stream. The buffer either borrows the
    free room of the stream's character buffer and writes there
    directly, or it collects bytes in a staging array of its own and
    passes them to the stream when the array is full. While the
    formatter runs, the stream is therefore in one of two states. It is
    whole, as its owner left it, or a part of its character buffer is
    on loan to the formatter.

    Every function that appends to a buffer may have to flush it, and
    a flush to a stream needs the stream. The formatter's invariant in
    [PrintfOut](PrintfOut.v) therefore has a parameter for what the
    flush needs. This module fills that parameter in for a buffer that
    prints to a stream. Its predicate owns the stream in either state,
    together with the parts of the buffer object that the window does
    not cover. Its lemmas take the stream's two write fields out of a
    stream on loan, put them back, and turn the stream and the returned
    window into a whole stream again. *)

From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv FileIdle FileTidy PrintfStreamInv LibioLogic LibioFputsSpec
  AllocRo CStruct PrintfLayout PrintfOut PrintfSpec.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

(** ## The stream of one call *)

(** One call of the formatter prints to one stream, and the facts
    about that stream do not change during the call. The record [fout]
    collects them: the object of the stream's jump tables, the thread,
    the stream's object, its descriptor, its second flags word, the
    state of its lock and the object of errno. *)
Record fout : Type := FOut {
  fo_vb : Z; fo_self : ptr; fo_fb : Z; fo_fd : Z; fo_flags2 : Z; fo_held : option Z; fo_eb : Z
}.

(** The stream's pointer points to the start of the stream's object. *)
Definition fo_fp (a : fout) : ptr := mkPtr (fo_fb a) (Obj (fo_fb a)).

(** The function [fs_with_wptr] gives the state of a stream after a
    store to its write pointer, which is the fifth of its twelve buffer
    pointers. *)
Definition fs_with_wptr (st : fstate) (p : ptr) : fstate :=
  mkFstate (fs_flags st) (<[4%nat := p]> (fs_ptrs st)) (fs_fileno st) (fs_flags2 st) (fs_old_offset st)
    (fs_column st) (fs_lock st) (fs_offset st) (fs_codecvt st) (fs_wide st) (fs_freeres_list st)
    (fs_freeres_buf st) (fs_mode st) (fs_total st) (fs_vtable st).

(** A stream lends the free room of its character buffer to the
    formatter. The definition [lent_ok] states the facts that hold of
    such a stream's fields, and the flush relies on them when it moves
    the stream's write pointer. The character buffer is a heap object
    db of sz bytes in the region dreg. The write pointer is at the
    address p, and the write end is at the address e inside the buffer.
    The formatter has the bytes from the address lo to the write end,
    and lo is at or below the write pointer. The stream's flags record
    that it has written before, because a stream has free room only
    after its first write. Every other fact also holds of a stream that
    has lent nothing. *)
Definition lent_ok (a : fout) (freg : region) (st : fstate) (db sz : Z) (dreg : region) (lo p e : Z) : Prop :=
  fo_fb a mod 8 = 0 /\ 0 < fo_fb a /\ fo_fb a + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\
  flags_ok st /\ idle_ok (fo_fd a) (fs_with_flags2 st 0) /\ fs_flags2 st = fo_flags2 a /\
  fs_vtable st = mkPtr (fo_vb a + vt_file) (Ro (fo_vb a)) /\
  buf_ptrs_ok (fo_fb a) (NbHeap db sz) (fs_ptrs st) /\ short_idle (NbHeap db sz) st /\
  r_kind dreg = Heap /\ db + sz <= r_end dreg /\ r_end dreg <= 2 ^ 63 /\ 0 < db /\ db mod 8 = 0 /\ 0 < sz /\
  fs_ptr st 4 = mkPtr p (Obj db) /\ fs_ptr st 5 = mkPtr e (Obj db) /\
  has (fs_flags st) io_currently_putting = true /\ db <= lo /\ lo <= p /\ p <= e /\ e <= db + sz.

(** A store to the write pointer keeps these facts when the new
    address is between the old one and the write end. *)
Lemma lent_ok_move a freg st db sz dreg lo p e p' :
  length (fs_ptrs st) = 12%nat -> lent_ok a freg st db sz dreg lo p e -> p <= p' <= e ->
  lent_ok a freg (fs_with_wptr st (mkPtr p' (Obj db))) db sz dreg lo p' e.
Proof.
  intros Hlen H Hp. destruct st as [fl ps fno fl2 oo col lk off cv wd frl frb md tot vt]. cbn [fs_ptrs] in Hlen.
  do 12 (destruct ps as [|? ps]; [discriminate Hlen|]). destruct ps; [|discriminate Hlen].
  unfold lent_ok, fs_with_wptr, idle_ok, short_idle, buf_ptrs_ok, fs_ptr, fs_with_flags2 in *.
  cbn [fs_ptrs fs_flags fs_flags2 fs_fileno fs_mode fs_column fs_vtable nth take] in *.
  destruct H as (A1 & A2 & A3 & A4 & Hfl & (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11 & I12 & I13 & I14 & I15) & A5 & A6 & (B1 & B2 & B3) & ((S1 & S1b) & S2 & S3 & S4 & S5) & D1 & D2 & D3 & D4 & D5 & D6 & E4 & E5 & Hput & Hlo).
  destruct Hfl as (F1 & F2 & F3 & F4 & F5 & F6 & F7). cbn [fs_flags fs_flags2 fs_ptrs] in F1, F2, F3, F4, F5, F6, F7.
  unfold flags_ok. cbn [insert list_insert nth take fs_flags fs_flags2 fs_ptrs fs_fileno fs_mode fs_column fs_vtable].
  subst p4 p5. cbn [ptr_addr] in *.
  repeat (apply Forall_cons_1 in B3; destruct B3 as [[? ?] B3]). cbn [ptr_addr ptr_cap] in *.
  repeat match goal with
    | |- _ /\ _ => split
    | |- Forall _ (_ :: _) => apply Forall_cons
    | |- Forall _ [] => apply Forall_nil
    end; cbn [ptr_addr ptr_cap]; try (first [assumption | reflexivity | lia | by rewrite S2 | by intros _]).
Qed.

Section out.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## Windows *)

(** A window's bytes come out of a larger run of bytes and go back
    into it. Two runs of owned bytes that meet at the address mid are
    one run, and one run splits at any address inside it. *)
Lemma win_own_join b lo mid hi :
  lo <= mid <= hi -> win_own b lo mid ∗ win_own b mid hi ⊣⊢ win_own b lo hi.
Proof using Type.
  intros Hm. iSplit.
  - iIntros "[(%xs & %cs & (%Hl & %Hc & %Hf) & Hx & Hc) (%ys & %ds & (%Hl' & %Hd & %Hf') & Hy & Hd)]".
    iExists (xs ++ ys), (cs ++ ds). rewrite bytes_app auxes_app Hc.
    replace (lo - b + Z.of_nat (length xs)) with (mid - b) by lia. iFrame "Hx Hc Hy Hd". iPureIntro.
    rewrite !length_app Forall_app. split_and!; [lia | lia | assumption | assumption].
  - iIntros "(%xs & %cs & (%Hl & %Hc & %Hf) & Hx & Hc)". set (n := Z.to_nat (mid - lo)).
    iDestruct (bytes_take_drop _ _ _ n with "Hx") as "[Hx Hy]"; [lia|].
    iDestruct (auxes_take_drop _ _ _ n with "Hc") as "[Hc Hd]"; [lia|].
    replace (lo - b + Z.of_nat n) with (mid - b) by lia.
    iSplitL "Hx Hc".
    + iExists _, _. iFrame "Hx Hc". iPureIntro. rewrite !length_take. split_and!; [lia | lia | by apply Forall_take].
    + iExists _, _. iFrame "Hy Hd". iPureIntro. rewrite !length_drop. split_and!; [lia | lia | by apply Forall_drop].
Qed.

(** ## A stream on loan *)

(** The formatter writes into a part of the stream's character
    buffer, so the formatter must own those bytes. It must also own the
    lifetime of the character buffer, because every store checks that
    the object is alive. The predicate [file_lent_at] owns what is left
    of the stream. That is the stream's object and fields, its lock,
    its wide data, the bytes of the character buffer below the address
    lo, and the bytes from the write end on. *)
Definition file_lent_at (a : fout) (db : Z) (dreg : region) (lo p e : Z) : iProp Σ :=
  ∃ freg st sz, ⌜lent_ok a freg st db sz dreg lo p e⌝ ∗
    live (fo_fb a) freg ∗ file_fields (fo_fb a) st ∗ lock_inv (fo_self a) (fs_lock st) (fo_held a) ∗
    wide_idle (fo_vb a) (fs_wide st) (fs_codecvt st) ∗
    win_own db db lo ∗ win_own db e (db + sz).

(** The two write fields of a stream at the addresses p and e of the
    object db. *)
Definition write_cells (a : fout) (db p e : Z) : iProp Σ :=
  file_cells (fo_fb a)
    [("_IO_write_ptr", VPtr (mkPtr p (Obj db))); ("_IO_write_end", VPtr (mkPtr e (Obj db)))].

(** The formatter's flush stores the buffer's write pointer into the
    stream. For that store it borrows the stream's lifetime and its two
    write fields, and it gives them back with a write pointer that has
    moved towards the write end. *)
Lemma file_lent_fields a db dreg lo p e :
  file_lent_at a db dreg lo p e ⊢ ∃ freg,
    file_liveq (DfracOwn 1) (fo_fb a) freg ∗ write_cells a db p e ∗
    (∀ p', ⌜p <= p' <= e⌝ -∗ file_liveq (DfracOwn 1) (fo_fb a) freg -∗ write_cells a db p' e -∗
       file_lent_at a db dreg lo p' e).
Proof using Type.
  iIntros "(%freg & %st & %sz & %Hok & Hl & Hf & Hlk & Hw & Hlo & Hhi)". iExists freg.
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hrest)".
  pose proof Hok as (A1 & A2 & A3 & A4 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E4 & E5 & _).
  destruct st as [fl ps fno fl2 oo col lk off cv wd frl frb md tot vt]. cbn [fs_ptrs fs_flags] in *. unfold fs_ptr in E4, E5. cbn [fs_ptrs] in E4, E5.
  do 12 (destruct ps as [|? ps]; [discriminate Hlen|]). destruct ps; [|discriminate Hlen]. cbn [nth] in E4, E5. subst.
  iEval (cbn [big_opL]) in "Hps". iDestruct "Hps" as "(H0 & H1 & H2 & H3 & H4 & H5 & Hps)".
  iSplitL "Hl". { iEval (struct_sizes). iSplit; [iPureIntro; unfold file_size in A3; lia | iExact "Hl"]. }
  iSplitL "H4 H5". { unfold write_cells. struct_close. }
  iIntros (p' Hp') "Hl Hc". struct_live_open "Hl" as "[_ Hl]". unfold write_cells. struct_open "Hc" as "(H4 & H5 & _)".
  iExists freg, (fs_with_wptr _ (mkPtr p' (Obj db))), sz. iSplit.
  { iPureIntro. eapply lent_ok_move; [|exact Hok|exact Hp']. reflexivity. }
  unfold file_fields, fs_with_wptr. cbn [fs_ptrs fs_flags fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable insert list_insert big_opL].
  iFrame "Hlk Hw Hlo Hhi Hfl H0 H1 H2 H3 Hps Hrest". iFrame "Hl H4 H5". done.
Qed.

(** When the window moves up, the bytes below its new start go back to
    the stream. *)
Lemma file_lent_shrink a db dreg lo lo' p e :
  lo <= lo' <= p -> file_lent_at a db dreg lo p e ∗ win_own db lo lo' ⊢ file_lent_at a db dreg lo' p e.
Proof using Type.
  intros Hlo'. iIntros "[(%freg & %st & %sz & %Hok & Hl & Hf & Hlk & Hw & Hlo & Hhi) Hmid]".
  iExists freg, st, sz. iFrame "Hl Hf Hlk Hw Hhi". iSplit; [iPureIntro; unfold lent_ok in *; intuition lia|].
  iApply (win_own_join db db lo lo'); [unfold lent_ok in Hok; intuition lia|]. iFrame.
Qed.

(** When the whole window comes back, with the buffer's lifetime, the
    stream is tidy again. *)
Lemma file_lent_tidy a db dreg lo p e :
  file_lent_at a db dreg lo p e ∗ live db dreg ∗ win_own db lo e ⊢
  file_tidy (fo_vb a) (fo_self a) (fo_fp a) (fo_fd a) (fo_flags2 a) (fo_held a).
Proof using Type.
  iIntros "((%freg & %st & %sz & %Hok & Hl & Hf & Hlk & Hw & Hlo & Hhi) & Hd & Hmid)".
  assert (Hb : db <= lo <= e /\ e <= db + sz) by (unfold lent_ok in Hok; intuition lia).
  iExists (fo_fb a), freg, st, (NbHeap db sz). iFrame "Hl Hf Hlk Hw". iSplit.
  { iPureIntro. unfold lent_ok in Hok. split; [reflexivity|]. intuition. }
  iCombine "Hlo Hmid" as "Hlo". rewrite (win_own_join db db lo e); [|lia].
  iCombine "Hlo Hhi" as "Hlo". rewrite (win_own_join db db e (db + sz)); [|lia].
  iDestruct "Hlo" as "(%xs & %cs & (%Hxs & %Hcs & %Hrange) & Hx & Hc)".
  rewrite Z.sub_diag. iExists dreg, xs, cs. iFrame "Hd Hx Hc". iPureIntro. unfold lent_ok in Hok.
  split_and!; [intuition..| lia | exact Hrange | lia].
Qed.

(** ## Opening a tidy stream *)

(** The two functions that choose a window read the stream's write
    pointer and write end. This lemma takes what they read out of a
    tidy stream, for a buffer bb in the region breg. The caller gives
    it back in one of two ways. It gets the tidy stream again, which is
    right when the staging array was chosen. Or the stream has room,
    and the caller keeps the room and the lifetime of the character
    buffer for the window and gets the stream on loan. *)
Lemma file_tidy_fwin a bb breg :
  file_tidy (fo_vb a) (fo_self a) (fo_fp a) (fo_fd a) (fo_flags2 a) (fo_held a) ⊢
  ∃ freg dqf cs, let i := FWinIn bb breg (fo_fb a) freg dqf cs in
    fwin_stream i ∗
    ((fwin_stream i -∗ file_tidy (fo_vb a) (fo_self a) (fo_fp a) (fo_fd a) (fo_flags2 a) (fo_held a)) ∧
     (∀ c, ⌜cs = Some c /\ fc_bo c < fc_eo c⌝ -∗ fwin_stream i -∗
        let w := data_win (fc_data c) (fc_reg c) (fc_bo c) (fc_eo c) in
        live (fc_data c) (fc_reg c) ∗ win_own (fc_data c) (pw_lo w) (pw_end w) ∗
        file_lent_at a (fc_data c) (fc_reg c) (pw_lo w) (pw_base w) (pw_end w))).
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %HP & Hl & Hf & Hlk & Hb & Hw)".
  pose proof HP as (Hfp & A1 & A2 & A3 & A4 & Hfl & Hidle & A5 & A6 & Hbp & Hsh).
  unfold fo_fp in Hfp. injection Hfp as Hfb _. subst fb.
  iDestruct "Hf" as "(%Hlen & Hflg & Hps & Hrest)".
  destruct Hidle as (_ & _ & _ & _ & _ & _ & _ & _ & I9 & I10 & _). destruct Hsh as [_ Hsh].
  unfold fs_ptr in I9, I10, Hsh. cbn [fs_with_flags2 fs_ptrs fs_flags] in I9, I10.
  remember (fs_ptrs st) as ps eqn:Eps.
  destruct ps as [|q0 [|q1 [|q2 [|q3 [|q4 [|q5 [|q6 [|q7 [|q8 [|q9 [|q10 [|q11 [|? ?]]]]]]]]]]]]]; try discriminate Hlen.
  cbn [nth] in I9, I10, Hsh.
  iEval (cbn [big_opL]) in "Hps". iDestruct "Hps" as "(H0 & H1 & H2 & H3 & H4 & H5 & Hps)".
  destruct nb as [| |db sz|?]; cbn [buf_idle buf_ptrs_ok take nth] in *.
  - injection Hbp as -> -> -> -> -> -> -> ->. iExists freg, (DfracOwn 1), None. cbn zeta. iSplitL "Hl H4 H5".
    { unfold fwin_stream. cbn [fi_dqf fi_file fi_freg fi_chars fwin_ptrs fst snd]. iSplitL "Hl".
      - iEval (struct_sizes). iSplit; [iPureIntro; unfold file_size in A3; lia | iExact "Hl"].
      - iSplit; [struct_close | done]. }
    iSplit.
    + unfold fwin_stream. cbn [fi_dqf fi_file fi_freg fi_chars fwin_ptrs fst snd]. iIntros "(Hl & Hc & _)".
      struct_live_open "Hl" as "[_ Hl]". struct_open "Hc" as "(H4 & H5 & _)".
      iExists (fo_fb a), freg, st, NbNone. iSplit; [iPureIntro; rewrite -Eps; exact HP|]. iFrame "Hl Hlk Hw".
      unfold file_fields. rewrite -Eps. cbn [big_opL]. iFrame "Hflg H0 H1 H2 H3 H4 H5 Hps Hrest". done.
    + iIntros (c [Hc _]). discriminate Hc.
  - destruct Hbp as (B6 & B7 & B3). destruct Hsh as (_ & S4 & S5 & S3). subst q4 q5 q3 q6.
    iExists freg, (DfracOwn (1/2)), (Some (FChars (fo_fb a) freg 131 131 (DfracOwn (1/2)))). cbn zeta.
    iEval (rewrite /live pts_ptsq -(Qp.half_half) ptsq_split) in "Hl". iDestruct "Hl" as "[Hl Hl']".
    iSplitL "Hl Hl' H4 H5".
    { unfold fwin_stream. cbn [fi_dqf fi_file fi_freg fi_chars fwin_ptrs fst snd fc_data fc_bo fc_eo fc_dq fc_reg]. iSplitL "Hl".
      - iEval (struct_sizes). iSplit; [iPureIntro; unfold file_size in A3; lia | iExact "Hl"].
      - iSplitR "Hl'"; [struct_close | iFrame "Hl'"]. iPureIntro. unfold fchars_ok, file_size in *. cbn [fc_data fc_bo fc_eo fc_reg]. lia. }
    iSplit.
    + unfold fwin_stream. cbn [fi_dqf fi_file fi_freg fi_chars fwin_ptrs fst snd fc_data fc_bo fc_eo fc_dq fc_reg]. iIntros "(Hl & Hc & _ & Hl')".
      struct_live_open "Hl" as "[_ Hl]". struct_open "Hc" as "(H4 & H5 & _)".
      iCombine "Hl Hl'" as "Hl". iEval (rewrite /liveq -ptsq_split Qp.half_half -pts_ptsq) in "Hl".
      iExists (fo_fb a), freg, st, NbShort. iSplit; [iPureIntro; rewrite -Eps; exact HP|]. iFrame "Hl Hlk Hw".
      unfold file_fields. rewrite -Eps. cbn [big_opL]. iFrame "Hflg H0 H1 H2 H3 H4 H5 Hps Hrest". done.
    + iIntros (c [Hc Hlt]). injection Hc as <-. cbn [fc_bo fc_eo] in Hlt. lia.
  - iDestruct "Hb" as (dreg xs cs) "((%D1 & %D2 & %D3 & %D4 & %D5 & %D6 & %Hxs & %Hrange & %Hcs) & Hd & Hx & Hc)".
    destruct Hbp as (B6 & B7 & B3). repeat (apply Forall_cons_1 in B3; destruct B3 as [[? ?] B3]).
    destruct q4 as [a4 c4], q5 as [a5 c5]. cbn [ptr_addr ptr_cap] in *. subst c4 c5.
    iExists freg, (DfracOwn 1), (Some (FChars db dreg (a4 - db) (a5 - db) (DfracOwn 1))). cbn zeta.
    iSplitL "Hl Hd H4 H5".
    { unfold fwin_stream. cbn [fi_dqf fi_file fi_freg fi_chars fwin_ptrs fst snd fc_data fc_bo fc_eo fc_dq fc_reg].
      replace (db + (a4 - db)) with a4 by lia. replace (db + (a5 - db)) with a5 by lia. iSplitL "Hl".
      - iEval (struct_sizes). iSplit; [iPureIntro; unfold file_size in A3; lia | iExact "Hl"].
      - iSplitR "Hd"; [struct_close | iFrame "Hd"]. iPureIntro. unfold fchars_ok. cbn [fc_data fc_bo fc_eo fc_reg]. lia. }
    unfold fwin_stream. cbn [fi_dqf fi_file fi_freg fi_chars fwin_ptrs fst snd fc_data fc_bo fc_eo fc_dq fc_reg].
    replace (db + (a4 - db)) with a4 by lia. replace (db + (a5 - db)) with a5 by lia. iSplit.
    + iIntros "(Hl & Hc' & _ & Hd)". struct_live_open "Hl" as "[_ Hl]". struct_open "Hc'" as "(H4 & H5 & _)".
      iExists (fo_fb a), freg, st, (NbHeap db sz). iSplit; [iPureIntro; rewrite -Eps; exact HP|]. iFrame "Hl Hlk Hw".
      iSplitR "Hd Hx Hc"; [|iExists dreg, xs, cs; iFrame "Hd Hx Hc"; done].
      unfold file_fields. rewrite -Eps. cbn [big_opL]. iFrame "Hflg H0 H1 H2 H3 H4 H5 Hps Hrest". done.
    + iIntros (c [Hc Hlt]) "(Hl & Hc' & _ & Hd)". injection Hc as <-. cbn [fc_bo fc_eo fc_data fc_reg data_win pw_lo pw_base pw_end] in *.
      replace (db + (a4 - db)) with a4 by lia. replace (db + (a5 - db)) with a5 by lia.
      struct_live_open "Hl" as "[_ Hl]". struct_open "Hc'" as "(H4 & H5 & _)". iFrame "Hd".
      assert (Hlo : db <= a4 - a4 mod 8 <= a4).
      { pose proof (Z.mod_pos_bound a4 8 ltac:(lia)). split; [|lia].
        replace a4 with (db + (a4 - db)) by lia. rewrite Z.add_mod // D5 Z.add_0_l Z.mod_mod //.
        pose proof (Z.mod_le (a4 - db) 8 ltac:(lia) ltac:(lia)). lia. }
      unfold pw_lo. cbn [data_win pw_base]. replace (db + (a4 - db)) with a4 by lia. set (lo := a4 - a4 mod 8) in *.
      iAssert (win_own db db (db + sz)) with "[Hx Hc]" as "Hall".
      { iExists xs, cs. rewrite Z.sub_diag. iFrame "Hx Hc". iPureIntro. split_and!; [lia | lia | exact Hrange]. }
      rewrite -(win_own_join db db a5 (db + sz)); [|lia]. rewrite -(win_own_join db db lo a5); [|lia].
      iDestruct "Hall" as "[[Hlo $] Hhi]". iExists freg, st, sz. iFrame "Hlk Hw Hlo Hhi". iSplit.
      { iPureIntro. destruct HP as (_ & _ & _ & _ & _ & Hfl' & Hidle & _ & _ & _ & Hsh'). unfold lent_ok.
        rewrite -Eps. unfold fs_ptr. rewrite -Eps. cbn [nth buf_ptrs_ok take].
        split_and!; try first [assumption | reflexivity | lia | apply I10; lia].
        repeat apply Forall_cons; cbn [ptr_addr ptr_cap]; try (split; [first [assumption | reflexivity]|lia]). apply Forall_nil. }
      iEval (rewrite /liveq -pts_ptsq) in "Hl". iFrame "Hl".
      unfold file_fields. rewrite -Eps. cbn [big_opL]. iFrame "Hflg H0 H1 H2 H3 H4 H5 Hps Hrest". done.
  - iDestruct "Hb" as "[]".
Qed.

(** ## What the flush needs *)

(** A flush to a stream needs more than the five fields of the buffer.
    It reads the buffer's pointer to the stream, it may call the
    stream's write functions, and those functions may set errno. The
    predicate [file_R] owns these things for a buffer that prints to
    the stream of a, and the formatter's invariant carries it beside
    the buffer. The buffer is the object bb in the region breg, and pl
    is the place of its window. The predicate says that the buffer's
    object reaches to the end of the staging array. It owns the
    buffer's field that points to the stream, errno, and the read-only
    data that a write to the stream reads.

    A buffer writes either into its own staging array or straight
    into the stream's character buffer. In the first case the stream
    is whole. The predicate then owns the stream and the bytes of the
    staging array that come after the bytes the buffer is using. In the
    second case the stream has lent a part of its character buffer.
    The predicate then owns the whole staging array and the rest of
    the stream. The lent part has room for at least one byte, and its
    end does not lie inside the buffer's object. The flush compares
    addresses and relies on both facts. *)
Definition file_R (a : fout) (bb : Z) (breg : region) (pl : Z * region * Z * Z) : iProp Σ :=
  let '(obj, reg, base, e) := pl in
  ⌜bb + stage_end <= r_end breg⌝ ∗ pbuf_file bb [("fp", VPtr (fo_fp a))] ∗
  errno_any (fo_eb a) ∗ fputs_ro (fo_vb a) ∗ malloc_ro ∗
  if Z.eq_dec obj bb then
    (⌜(base = bb + stage_off /\ (e = bb + stage_end \/ e = bb + stage_off + 1))%Z⌝ ∗
     win_own bb e (bb + stage_end) ∗
     file_tidy (fo_vb a) (fo_self a) (fo_fp a) (fo_fd a) (fo_flags2 a) (fo_held a))%I
  else
    (⌜base < e /\ (e <= bb \/ bb + stage_end < e)⌝ ∗
     win_own bb (bb + stage_off) (bb + stage_end) ∗
     file_lent_at a obj reg (base - base mod 8) base e)%I.

(** The formatter saves errno when it starts, and the predicate lends
    errno for that. *)
Lemma file_R_lends_errno a bb : ⊢ lends_errno (file_R a) bb (fo_eb a).
Proof using Type.
  iModIntro. iIntros (breg [[[obj reg] base] e]) "(Hext & Hfp & Herrno & Hrest)". iFrame "Herrno".
  iIntros "Herrno". iFrame.
Qed.

End out.
