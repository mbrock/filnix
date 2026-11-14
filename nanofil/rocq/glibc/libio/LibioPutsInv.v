(** What the proofs of `c: puts` and `c: fputs` (LibioPutsCode.v)
    share: a stream at a known mode and lock state ([file_at]), the
    fields each part of the two functions opens from it, the triples
    they call through the jump table and by name, taken as hypotheses
    ([xsputn_spec], [overflow_spec]), and a load of a pointer into the
    object that holds it ([wp_raw_load_pointer_self]).

    FileInv.v's [file_inv] hides the stream's mode and whether its lock
    is held. Both functions take the lock, orient the stream narrow and
    release the lock again, so their triples are stated over
    [file_at], which is [file_inv] with the mode and the lock count
    named ([file_inv_at]). Two lemmas open what the code touches and
    close the stream again:

    | Lemma | Opens |
    |---|---|
    | [file_at_live] | the life |
    | [file_at_open] | the life, `c: _flags`, `c: _lock` and its lock, `c: _mode` and the jump table pointer |
    | [file_at_nl] | the life, `c: _IO_write_ptr`, `c: _IO_write_end`, the bytes at 128 holding `c: _shortbuf` and the buffer |

    The second is what `c: puts` needs to store its newline: the write
    pointers point into the stream's buffer ([in_buf]), and the closing
    half takes any new write pointer there. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioCloseSteps
  WordString LibioGenCode LibioXsputnCode.
From Glibc Require FileInv LibioCloseSteps LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** The stream state st with `c: _mode` m. *)
Definition fs_with_mode (st : fstate) (m : Z) : fstate :=
  mkFstate (fs_flags st) (fs_ptrs st) (fs_fileno st) (fs_flags2 st) (fs_old_offset st) (fs_column st)
    (fs_lock st) (fs_offset st) (fs_codecvt st) (fs_wide st) (fs_freeres_list st) (fs_freeres_buf st) m
    (fs_total st) (fs_vtable st).

(** A pointer the narrow buffer nb of the stream fb allows as a read or
    write pointer: null with no buffer, else one into the buffer or to
    its end. *)
Definition in_buf (fb : Z) (nb : nbuf) (p : ptr) : Prop :=
  match nb with
  | NbNone | NbFreeres _ => p = null
  | NbShort => ptr_cap p = Obj fb /\ fb + 131 <= ptr_addr p <= fb + 132
  | NbHeap bb sz => ptr_cap p = Obj bb /\ bb <= ptr_addr p <= bb + sz
  end.

(** The pointers [buf_ptrs_ok] allows at an index below 8 of the
    twelve are [in_buf]. *)
Lemma buf_ptrs_in fb nb ps i :
  buf_ptrs_ok fb nb ps -> length ps = 12%nat -> (i < 8)%nat -> in_buf fb nb (nth i ps null).
Proof.
  intros Hok Hlen Hi. destruct (lookup_lt_is_Some_2 ps i ltac:(lia)) as [x Hx].
  rewrite (nth_lookup_Some ps i null x Hx).
  assert (Ht : take 8 ps !! i = Some x) by (rewrite lookup_take_lt; [exact Hx | lia]).
  destruct nb as [| |bb sz|bb]; cbn [buf_ptrs_ok in_buf] in Hok |- *.
  - rewrite Hok in Ht. apply lookup_replicate in Ht. tauto.
  - destruct Hok as (_ & _ & Hf). exact (Forall_lookup_1 _ _ _ _ Hf Ht).
  - destruct Hok as (_ & _ & Hf). exact (Forall_lookup_1 _ _ _ _ Hf Ht).
  - rewrite Hok in Ht. apply lookup_replicate in Ht. tauto.
Qed.

(** The write pointer of [buf_ptrs_ok]'s twelve replaced by one
    [in_buf] keeps them [buf_ptrs_ok]. *)
Lemma buf_ptrs_set4 fb nb p0 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 wp :
  buf_ptrs_ok fb nb [p0; p1; p2; p3; p4; p5; p6; p7; p8; p9; p10; p11] -> in_buf fb nb wp ->
  buf_ptrs_ok fb nb [p0; p1; p2; p3; wp; p5; p6; p7; p8; p9; p10; p11].
Proof.
  intros Hok Hin. destruct nb as [| |bb sz|bb]; cbn [buf_ptrs_ok in_buf] in Hok, Hin |- *.
  - injection Hok as -> -> -> -> -> -> -> ->. subst wp. reflexivity.
  - destruct Hok as (H6 & H7 & Hf). split; [exact H6|]. split; [exact H7|].
    exact (Forall_insert _ _ 4 wp Hf Hin).
  - destruct Hok as (H6 & H7 & Hf). split; [exact H6|]. split; [exact H7|].
    exact (Forall_insert _ _ 4 wp Hf Hin).
  - injection Hok as -> -> -> -> -> -> -> ->. subst wp. reflexivity.
Qed.


Section streams.
Context `{!gen_heapGS piece pval Σ}.

(** [file_at] vb self fp mode held: FileInv.v's [file_inv] with the
    stream's `c: _mode` the bits mode and its lock held as held
    says ([lock_inv]). *)
Definition file_at (vb : Z) (self fp : ptr) (mode : Z) (held : option Z) : iProp Σ :=
  ∃ fb freg st nb vt_off, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ flags_ok st /\ fs_mode st = mode /\
     mode_vtable mode vt_off /\ fs_vtable st = mkPtr (vb + vt_off) (Ro vb) /\
     buf_ptrs_ok fb nb (fs_ptrs st)⌝ ∗
    live fb freg ∗ file_fields fb st ∗ lock_inv self (fs_lock st) held ∗ buf_own nb.

(** [file_inv] is [file_at] at some mode and lock state. *)
Lemma file_inv_at vb self fp : file_inv vb self fp ⊣⊢ ∃ mode held, file_at vb self fp mode held.
Proof.
  iSplit.
  - iIntros "(%fb & %freg & %st & %nb & %vt & %held & %Hp & Hl & Hf & Hk & Hb)".
    destruct Hp as (Hfp & Hal & Hfb & Hend & Hreg & Hok & Hmv & Hvt & Hbok).
    iExists (fs_mode st), held, fb, freg, st, nb, vt. iFrame "Hl Hf Hk Hb". iPureIntro. tauto.
  - iIntros "(%mode & %held & %fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
    destruct Hp as (Hfp & Hal & Hfb & Hend & Hreg & Hok & Hm & Hmv & Hvt & Hbok). subst mode.
    iExists fb, freg, st, nb, vt, held. iFrame "Hl Hf Hk Hb". iPureIntro. tauto.
Qed.

(** A [file_at] stream's life, and the stream back from it. *)
Lemma file_at_live vb self fp mode held :
  file_at vb self fp mode held ⊢
  ∃ fb freg, ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\
              r_end freg <= 2 ^ 63⌝ ∗ live fb freg ∗ (live fb freg -∗ file_at vb self fp mode held).
Proof.
  iIntros "(%fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
  pose proof Hp as (-> & Hal & Hfb & Hend & Hreg & _).
  iExists fb, freg. iFrame "Hl". iSplitR; [iPureIntro; split_and!; first [reflexivity | assumption]|].
  iIntros "Hl". iExists fb, freg, st, nb, vt. iFrame "Hl Hf Hk Hb". iPureIntro. exact Hp.
Qed.

(** Taking the lock and choosing narrow output leave the buffer alone.
    This view lets those steps return the caller's full stream state,
    including any buffer facts needed for a later close. *)
Definition file_open (vb : Z) (self : ptr) (F : ptr -> Z -> option Z -> iProp Σ)
    (fp : ptr) (mode : Z) (held : option Z) : iProp Σ :=
  ∃ fb freg fl lb vt_off, ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\
       r_end freg <= 2 ^ 63 /\ 0 <= fl < 2 ^ 32 /\ has fl io_user_lock = false /\ mode_vtable mode vt_off⌝ ∗
    live fb freg ∗ int_cell fb off_flags fl ∗ pcell fb off_lock (mkPtr lb (Obj lb)) ∗
    lock_inv self (mkPtr lb (Obj lb)) held ∗ int_cell fb off_mode mode ∗
    pcell fb off_vtable (mkPtr (vb + vt_off) (Ro vb)) ∗
    (∀ mode' held', ⌜mode_vtable mode' vt_off⌝ -∗ live fb freg -∗ int_cell fb off_flags fl -∗
       pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_inv self (mkPtr lb (Obj lb)) held' -∗
       int_cell fb off_mode mode' -∗ pcell fb off_vtable (mkPtr (vb + vt_off) (Ro vb)) -∗
       F fp mode' held').

(** The generic stream predicate supports locking and orientation
    without restricting its descriptor, flags or buffer to stdout's. *)
Lemma file_at_open vb self fp mode held :
  file_at vb self fp mode held ⊢ file_open vb self (file_at vb self) fp mode held.
Proof.
  iIntros "(%fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
  destruct Hp as (-> & Hal & Hfb & Hend & Hreg & Hok & Hm & Hmv & Hvt & Hbok).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hf2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb &
    Hmd & Htot & Hvtp)".
  iDestruct "Hk" as (lb lreg Hlb) "Hk".
  pose proof Hok as (Hflr & _ & _ & _ & Hul & _).
  iExists fb, freg, (fs_flags st), lb, vt. rewrite Hm Hvt Hlb. iFrame "Hl Hfl Hlp Hmd Hvtp".
  iSplitR; [iPureIntro; split_and!; first [reflexivity | assumption | lia]|].
  iSplitL "Hk"; [iExists lb, lreg; iSplit; done|].
  iIntros (mode' held' Hmv') "Hl Hfl Hlp Hk Hmd Hvtp".
  iExists fb, freg, (fs_with_mode st mode'), nb, vt. unfold fs_with_mode, file_fields.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable]. rewrite Hlb Hvt.
  iSplitR; [iPureIntro; unfold flags_ok in *; cbn [fs_flags fs_flags2]; tauto|].
  iFrame "Hl Hb Hk Hfl Hps Hfd Hf2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp". iSplit; done.
Qed.

(** Unlocking touches neither the mode nor the buffer. This view
    exposes only the resources it needs and returns the caller's
    predicate with the new lock state. *)
Definition file_lock_open (self fp : ptr) (F : option Z -> iProp Σ) (held : option Z) : iProp Σ :=
  ∃ fb freg fl lb, ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\
       r_end freg <= 2 ^ 63 /\ 0 <= fl < 2 ^ 32 /\ has fl io_user_lock = false⌝ ∗
    live fb freg ∗ int_cell fb off_flags fl ∗ pcell fb off_lock (mkPtr lb (Obj lb)) ∗
    lock_inv self (mkPtr lb (Obj lb)) held ∗
    (∀ held', live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_lock (mkPtr lb (Obj lb)) -∗
       lock_inv self (mkPtr lb (Obj lb)) held' -∗ F held').

(** A generic stream supplies the lock-only view while framing its
    mode, jump table and buffer unchanged. *)
Lemma file_at_lock vb self fp mode held :
  file_at vb self fp mode held ⊢ file_lock_open self fp (file_at vb self fp mode) held.
Proof.
  iIntros "Hf".
  iDestruct (file_at_open with "Hf") as (fb freg fl lb vt) "(%Hp & Hl & Hfl & Hlp & Hlk & Hmd & Hvtp & Hcl)".
  destruct Hp as (Hfp & Hfb & Hal & Hend & Hreg & Hflr & Hul & Hmv).
  iExists fb, freg, fl, lb. iFrame "Hl Hfl Hlp Hlk". iSplitR; [iPureIntro; tauto|].
  iIntros (held') "Hl Hfl Hlp Hlk".
  iApply ("Hcl" with "[//] Hl Hfl Hlp Hlk Hmd Hvtp").
Qed.

(** What the newline of `c: puts` takes from a [file_at] stream fp: its
    life, `c: _IO_write_ptr` wp and `c: _IO_write_end` we, both
    pointers into its buffer nb ([in_buf]), the 8 bytes col at 128
    holding `c: _shortbuf`, and the buffer; the stream comes back with
    any write pointer into the buffer and any 8 bytes at 128. *)
Lemma file_at_nl vb self fp mode held :
  file_at vb self fp mode held ⊢
  ∃ fb freg nb wp we col, ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb + file_size <= r_end freg /\
       r_end freg <= 2 ^ 63 /\ in_buf fb nb wp /\ in_buf fb nb we /\ length col = 8%nat⌝ ∗
    live fb freg ∗ pcell fb off_write_ptr wp ∗ pcell fb off_write_end we ∗ bytes fb off_column col ∗ buf_own nb ∗
    (∀ wp' col', ⌜in_buf fb nb wp' /\ length col' = 8%nat⌝ -∗ live fb freg -∗ pcell fb off_write_ptr wp' -∗
       pcell fb off_write_end we -∗ bytes fb off_column col' -∗ buf_own nb -∗ file_at vb self fp mode held).
Proof.
  iIntros "(%fb & %freg & %st & %nb & %vt & %Hp & Hl & Hf & Hk & Hb)".
  destruct Hp as (-> & Hal & Hfb & Hend & Hreg & Hok & Hm & Hmv & Hvt & Hbok).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hf2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb &
    Hmd & Htot & Hvtp)".
  destruct st as [fl ps fd f2 old col lk off cv wd frl frb md tot vtp]; cbn [fs_ptrs fs_column] in *.
  destruct ps as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]];
    try discriminate Hlen.
  pose proof (buf_ptrs_in fb nb _ 4 Hbok eq_refl ltac:(lia)) as Hw.
  pose proof (buf_ptrs_in fb nb _ 5 Hbok eq_refl ltac:(lia)) as He. cbn [nth] in Hw, He.
  iDestruct "Hps" as "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & _)".
  iExists fb, freg, nb, p4, p5, col. iFrame "Hl H4 H5 Hcol Hb".
  iSplitR; [iPureIntro; split_and!; first [reflexivity | assumption | lia]|].
  iIntros (wp' col' [Hin Hcl']) "Hl H4 H5 Hcol Hb".
  iExists fb, freg, (mkFstate fl [p0; p1; p2; p3; wp'; p5; p6; p7; p8; p9; p10; p11] fd f2 old col' lk off cv wd
    frl frb md tot vtp), nb, vt. unfold file_fields.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable big_opL length].
  iSplitR; [iPureIntro; split_and!; try assumption;
    [reflexivity | exact (buf_ptrs_set4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hbok Hin)]|].
  iFrame "Hl Hb Hk Hfl H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 Hfd Hf2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot
    Hvtp". iSplit; done.
Qed.

End streams.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance puts_inv_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A whole life of b is two half lives. *)
Lemma live_halves b reg : live b reg ⊣⊢ liveq (DfracOwn (1 / 2)) b reg ∗ liveq (DfracOwn (1 / 2)) b reg.
Proof. rewrite /live /liveq pts_ptsq -ptsq_split Qp.half_half. done. Qed.

(** [wp_raw_load_pointer] of a pointer x into the object b that holds
    it: one life gives both shares the load reads. *)
Lemma wp_raw_load_pointer_self f e ls l d off args rest j classes p b reg o x Φ :
  op_arg_classes (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> (b + o) mod 8 = 0 ->
  0 <= ptr_addr x < 2 ^ 64 -> ptr_cap x = Obj b ->
  live b reg -∗ pcell b o x -∗
  ▷ (live b reg -∗ pcell b o x -∗
     WP (ERun (mkFrame f (put d (WPtr x) e) ls None (Exec l rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) args :: rest) j))
       : sexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp Ha Hal Hr Hxc. iIntros "Hl Hc HK".
  rewrite live_halves. iDestruct "Hl" as "[Hl1 Hl2]".
  iAssert (pcellq (DfracOwn 1) b o x) with "[Hc]" as "Hc"; [rewrite /pcell pts_ptsq; done|].
  iAssert (live_capq (DfracOwn (1 / 2)) (ptr_cap x) reg) with "[Hl2]" as "Hl2"; [rewrite Hxc; done|].
  iApply (wp_raw_load_pointer_dq with "Hl1 Hc Hl2");
    [exact Hc | exact Hx | left; exact Hp | exact Ha | exact Hal | exact Hr |].
  iNext. iIntros "Hl1 Hc Hl2". rewrite Hxc. iApply ("HK" with "[Hl1 Hl2] [Hc]").
  - cbn [live_capq]. iFrame "Hl1 Hl2".
  - done.
Qed.

(** The string-output call returns the source and the caller's other
    resources. Its postcondition may depend on the input string, so
    nonempty output can establish buffer allocation even when the
    returned count indicates failure. Generic callers keep the same
    stream predicate before and after the call. *)
Definition xsputn_spec_for (F : ptr -> Z -> option Z -> iProp Σ)
    (G : list Z -> ptr -> Z -> option Z -> iProp Σ) (Rx : iProp Σ) : Prop := forall fr fp p dq s Φ,
  call_frame glibc__IO_new_file_xsputn [WPtr fp; WPtr p; WInt (Z.of_nat (length s))] = Some fr ->
  F fp (2 ^ 32 - 1) (Some 0) -∗ word_string dq p s -∗ Rx -∗
  ▷ (∀ r, ⌜0 <= r < 2 ^ 64⌝ -∗ G s fp (2 ^ 32 - 1) (Some 0) -∗ word_string dq p s -∗ Rx -∗
     Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

(** Existing callers keep the same stream resources before and after
    string output. This definition retains that original interface. *)
Definition xsputn_spec (vb : Z) (Rx : iProp Σ) : Prop :=
  xsputn_spec_for (file_at vb (ow_self w0)) (fun _ => file_at vb (ow_self w0)) Rx.

(** `c: __overflow(fp, '\n')`'s triple as `c: puts` calls it on a full
    buffer, with the stream's lock held once and its mode -1: any
    `c: int` comes back, with the stream at the same mode and lock and
    the resources Rx. *)
Definition overflow_spec (vb : Z) (Rx : iProp Σ) : Prop := forall fr fp Φ,
  call_frame glibc___overflow [WPtr fp; WInt 10] = Some fr ->
  file_at vb (ow_self w0) fp (2 ^ 32 - 1) (Some 0) -∗ Rx -∗
  ▷ (∀ r, ⌜0 <= r < 2 ^ 32⌝ -∗ file_at vb (ow_self w0) fp (2 ^ 32 - 1) (Some 0) -∗ Rx -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

End rules.

(** A string's length is below 2^48, as its window is. *)
Lemma word_string_len `{!gen_heapGS piece pval Σ} dq p s :
  word_string dq p s ⊢ ⌜Z.of_nat (length s) < 2 ^ 48⌝.
Proof.
  iIntros "(%b & %reg & %ws & %Hs & _)". iPureIntro. destruct Hs as [Hc Hb0 _ Hst Hf Hsp Hl _ _ _].
  unfold wstart in Hf. pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)). lia.
Qed.

