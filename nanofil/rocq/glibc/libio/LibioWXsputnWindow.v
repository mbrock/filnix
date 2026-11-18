(** The wide writers count their room in characters, but the stream
    stores byte addresses. This file lends the writers the cursor cells
    and the backing storage. Moving the write cursor returns the whole
    stream as long as the new character index fits the physical buffer.
    It need not fit below the write end on a line-buffered stream. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic.
From Glibc Require Import Fix OsWorld FileInv LibioLogic LibioWIdle.
Import ListNotations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Definition window_base wd w := match w with WbNone => null | WbShort => mkPtr (wd+216) (Obj wd)
  | WbHeap b _ => mkPtr b (Obj b) end.
Definition window_size w := match w with WbNone => 0 | WbShort => 1 | WbHeap _ sz => sz / 4 end.
Definition wpos wd w i := let p := window_base wd w in mkPtr (ptr_addr p + 4*i) (ptr_cap p).
Definition window_slots wd w i j := let p := window_base wd w in
  [p; p; p; p; wpos wd w i; wpos wd w j; p; wpos wd w (window_size w); null; null; null].

(** A heap window holds whole characters and ends within the address
    space. The other two windows have their bounds in the wide data
    object itself or have no storage at all. *)
Definition window_bound w := match w with WbHeap b sz => 0 < b /\ 0 < sz /\ sz mod 4 = 0 /\ b+sz <= 2^63
  | _ => True end.

Local Lemma slot_index p b e c : wcursor b e c p ->
  ∃ i, 0 <= i <= (e-b)/4 /\ p = mkPtr (b+4*i) c.
Proof. destruct p as [a t]. unfold wcursor. cbn [ptr_cap ptr_addr]. intros (-> & Ha & Hmod). exists ((a-b)/4).
  pose proof (Z.div_mod (a-b) 4 ltac:(lia)). split; [split; [apply Z.div_pos|apply Z.div_le_mono]; lia|].
  f_equal. lia. Qed.

Local Lemma window_at wd w b e c : window_base wd w = mkPtr b c -> e = b+4*window_size w ->
  forall ps, length ps = 11%nat -> drop 8 ps = replicate 3 null -> wbuf_at b e c ps ->
  ∃ i j, 0 <= i <= window_size w /\ 0 <= j <= window_size w /\ ps = window_slots wd w i j.
Proof.
  intros B -> ps L D (H4 & Hi & Hj & H6 & H7).
  destruct (slot_index _ _ _ _ Hi) as (i & Ri & Ei). destruct (slot_index _ _ _ _ Hj) as (j & Rj & Ej).
  replace ((b+4*window_size w-b)/4) with (window_size w) in Ri, Rj by (apply Z.div_unique_exact; lia).
  exists i, j. split; [done|]. split; [done|]. rewrite /window_slots /wpos B. cbn [ptr_addr ptr_cap].
  do 11 (destruct ps as [|? ps]; [discriminate|]). destruct ps; [|discriminate].
  cbn in H4, D, Ei, Ej, H6, H7. congruence.
Qed.

Lemma window_indices wd w ps : window_bound w -> wbuf_ptrs_ok wd w ps ->
  ∃ i j, 0 <= i <= window_size w /\ 0 <= j <= window_size w /\ ps = window_slots wd w i j.
Proof.
  intros B (L & D & A). destruct w as [| |b sz].
  - exists 0, 0. split; [done|]. split; [done|]. rewrite <-(take_drop 8 ps), A, D. done.
  - eapply window_at; [reflexivity|reflexivity|exact L|exact D|exact A].
  - eapply window_at; [reflexivity| |exact L|exact D|exact A]. cbn [window_size]. destruct B as (_ & _ & Hmod & _).
    pose proof (Z.div_mod sz 4 ltac:(lia)). lia.
Qed.

Lemma window_ptrs_ok wd w i j : window_bound w -> 0 <= i <= window_size w -> 0 <= j <= window_size w ->
  wbuf_ptrs_ok wd w (window_slots wd w i j).
Proof.
  intros B Hi Hj. destruct w as [| |b sz]; cbn [window_size] in Hi, Hj.
  - assert (i=0) as -> by lia. assert (j=0) as -> by lia. done.
  - unfold wbuf_ptrs_ok, wbuf_at, wcursor, woff_shortbuf, window_slots, wpos, window_base, window_size. cbn [nth ptr_cap ptr_addr].
    repeat split; try reflexivity; try (f_equal; lia); try lia; (apply Z.mod_divide; [lia|first [exists i; ring|exists j; ring]]).
  - destruct B as (_ & Hsz & Hmod & _). pose proof (Z.div_mod sz 4 ltac:(lia)).
    unfold wbuf_ptrs_ok, wbuf_at, wcursor, window_slots, wpos, window_base, window_size. cbn [nth ptr_cap ptr_addr].
    repeat split; try reflexivity; try (f_equal; lia); try lia; (apply Z.mod_divide; [lia|first [exists i; ring|exists j; ring]]).
Qed.

Section view.
Context `{!gen_heapGS piece pval Σ}.

(** The two writers inspect the flags, follow the wide-data pointer and
    move the write pointer. They do not borrow the narrow buffer or the
    conversion state. The short buffer's last four padding bytes and
    its shadow slots stay in the frame during a scalar copy. *)
Definition write_window fb fr wd wr fl w i j : iProp Σ := live fb fr ∗ int_cell fb off_flags fl ∗
  pcell fb off_wide (mkPtr wd (Obj wd)) ∗ live wd wr ∗ pcell wd 24 (window_base wd w) ∗
  pcell wd 32 (wpos wd w i) ∗ pcell wd 40 (wpos wd w j) ∗ pcell wd 56 (wpos wd w (window_size w)) ∗
  (∃ sb : list Z, ⌜length sb = 4%nat /\ Forall (fun b => 0 <= b < 256) sb⌝ ∗ bytes wd woff_shortbuf sb) ∗ wbuf_idle w.

Local Lemma bound_from_storage w : wbuf_idle w -∗ ⌜window_bound w⌝.
Proof using Type. destruct w; [by iIntros "_"|by iIntros "_"|]. iIntros "(%r & %xs & %cs & %H & _)".
  iPureIntro. unfold window_bound. lia. Qed.

Lemma wide_write_window ge vb self fp fd : file_wide ge vb self fp fd -∗ ∃ fb fr wd wr fl w i j,
  ⌜fp = mkPtr fb (Obj fb) /\ 0 < fb /\ fb mod 8 = 0 /\ fb+224 <= r_end fr /\ r_end fr <= 2^63 /\
    0 < wd /\ wd mod 8 = 0 /\ wd+232 <= r_end wr /\ r_end wr <= 2^63 /\ 0 <= fl < 2^32 /\
    window_bound w /\ 0 <= i <= window_size w /\ 0 <= j <= window_size w⌝ ∗ write_window fb fr wd wr fl w i j ∗
  (∀ k, ⌜0 <= k <= window_size w⌝ -∗ write_window fb fr wd wr fl w k j -∗ file_wide ge vb self fp fd).
Proof using Type.
  iIntros "(%fb & %fr & %st & %nb & %wd & %w & %tw & %tm & %Hp & Hf & Hfields & Hlock & Hnb & Hwide)".
  pose proof Hp as (Hfp & Hfa & Hfb & He & Hr & Hfl & _ & _ & _ & _ & _ & _ & Hwd & _).
  iDestruct "Hfields" as "(%L & Hfl & Hptrs & Hfd & Hf2 & Ho & %Hcol & Hc & Hlk & Hof & Hcv & Hwd & Hfr & Hbuf & Hm & Htw & Hvt)".
  iDestruct "Hwide" as (wr ps ib ie ob oe ifl icnt ofl ocnt sb scs H) "(Hl & Hps & Hst & Ha & Hin & Hout & Hsb & Hpad & Hslots & Hwvt & Hwb)".
  destruct H as (Hwd0 & Hwa & Hwe & Hwr & Hps & Hif & Hofl & Lsb & Vsb & Lscs).
  iDestruct (bound_from_storage with "Hwb") as %B. destruct (window_indices _ _ _ B Hps) as (i & j & Hi & Hj & ->).
  unfold window_slots. cbn [big_sepL]. iDestruct "Hps" as "(H0 & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & _)".
  iExists fb, fr, wd, wr, (fs_flags st), w, i, j. iSplit; [iPureIntro; unfold wflags_ok, file_size in *; tauto|].
  rewrite Hwd. iSplitL "Hf Hfl Hwd Hl H3 H4 H5 H7 Hsb Hwb".
  { rewrite /write_window. by iFrame. }
  iIntros (k Hk) "(Hf & Hfl & Hwd & Hl & H3 & H4 & H5 & H7 & (%sb' & (%Lsb' & %Vsb') & Hsb) & Hwb)".
  iExists fb, fr, st, nb, wd, w, tw, tm. iFrame "Hf Hlock Hnb". iSplit; [done|].
  iSplitR "Hl H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 Hst Ha Hin Hout Hsb Hpad Hslots Hwvt Hwb".
  { rewrite /file_fields Hwd. by iFrame. }
  iExists wr, (window_slots wd w k j), ib, ie, ob, oe, ifl, icnt, ofl, ocnt, sb', scs.
  iSplit; [iPureIntro; split_and!; try assumption; by apply window_ptrs_ok|]. rewrite /window_slots /=. by iFrame.
Qed.
End view.
