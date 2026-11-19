(** Overflow borrows the stream's cursor cells and both buffers. The
    lock, conversion descriptors and counters stay with the caller.
    Returning the cells with both cursors at the base recovers the
    stream at wide character index zero. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces Heap Language Logic MemLogic.
From Glibc Require Import Fix FileInv FileIdle LibioLogic LibioWIdle LibioWXsputnWindow LibioWOverflowState.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.

Definition wo_ptrs st := [fs_ptr st 0; fs_ptr st 1; fs_ptr st 2; fs_ptr st 3;
  fs_ptr st 4; fs_ptr st 5; fs_ptr st 6; fs_ptr st 7].
Definition wo_reset_ptrs (b stop : ptr) := [b; b; b; b; b; stop; b; stop].

Section loan.
Context `{!gen_heapGS piece pval Σ}.

(** To give the stream new buffers, glibc needs both the storage and
    the fields that point into it. It also records whether the stream
    must free each buffer when it closes. *)
Definition wo_cells vb fb fr fl f2 nb wd wr w ns ws : iProp Σ :=
  live fb fr ∗ int_cell fb off_flags fl ∗ int_cell fb off_flags2 f2 ∗
  int_cell fb off_fileno 1 ∗ int_cell fb off_mode 1 ∗ pcell fb off_vtable (mkPtr (vb+vt_wfile) (Ro vb)) ∗
  pcell fb off_wide (mkPtr wd (Obj wd)) ∗ ([∗ list] i ↦ p ∈ ns, pcell fb (off_ptr i) p) ∗ buf_idle nb ∗
  live wd wr ∗ ([∗ list] i ↦ p ∈ ws, pcell wd (woff_ptr i) p) ∗ pcell wd woff_vtable (mkPtr (vb+vt_wfile) (Ro vb)) ∗ wbuf_idle w.

Definition wo_close ge vb self fb fr st wd wr : iProp Σ := ∀ fl f2 nb w b stop j,
  ⌜wo_storage fb nb fl b stop /\ 0 <= fl < 2^32 /\
    (forall m, Z.land 513 m = 0 -> Z.land fl m = Z.land (fs_flags st) m) /\
    (forall m, (m = 2 \/ m = 32 \/ m = io_need_lock) -> Z.land f2 m = Z.land (fs_flags2 st) m) /\
    wbuf_user_ok w f2 /\ window_bound w /\ 0 <= j <= window_size w⌝ -∗
  wo_cells vb fb fr (Z.lor fl 2048) f2 nb wd wr w (wo_reset_ptrs b stop) (window_slots wd w 0 j) -∗
  file_pending ge vb self (mkPtr fb (Obj fb)) 1 wd w 0.

Lemma wo_open ge vb self fb wd w i : file_pending ge vb self (mkPtr fb (Obj fb)) 1 wd w i -∗
  ∃ fr st nb tw tm wr j, ⌜wide_file_ok ge vb (mkPtr fb (Obj fb)) 1 fb fr st nb wd w tw tm /\
    0 < wd /\ wd mod 8 = 0 /\ wd+232 <= r_end wr /\ r_end wr <= 2^63 /\
    window_bound w /\ 0 <= i <= window_size w /\ 0 <= j <= window_size w⌝ ∗
  wo_cells vb fb fr (fs_flags st) (fs_flags2 st) nb wd wr w (wo_ptrs st) (window_slots wd w i j) ∗ wo_close ge vb self fb fr st wd wr.
Proof using Type.
  iIntros "(%fb' & %fr & %st & %nb & %tw & %tm & %wr & %j & %R & %P & Hf & Hfields & Hlk & Hnb & Hd)".
  pose proof P as (Eq & _ & _ & _ & _ & _ & I & Mode & Vt & _ & _ & _ & Wd & _). injection Eq as <-.
  destruct I as (_ & Fd & _). change (fs_fileno st = 1) in Fd.
  iDestruct "Hfields" as "(%L & Hfl & Hp & Hfd & Hf2 & Ho & %C & Hcol & Hlock & Hof & Hcv & Hwd & Hfr & Hbuf & Hm & Htot & Hvt)".
  iDestruct "Hd" as (ib ie ob oe ifl icnt ofl ocnt sb scs U) "(Hl & Hw & Hst & Ha & Hin & Hout & Hsb & Hpad & Haux & Hwvt & Hb)".
  iExists fr, st, nb, tw, tm, wr, j. iSplit; [iPureIntro; tauto|].
  destruct (fs_ptrs st) as [|p0 [|p1 [|p2 [|p3 [|p4 [|p5 [|p6 [|p7 [|p8 [|p9 [|p10 [|p11 [|]]]]]]]]]]]]] eqn:Ps; try discriminate L.
  iDestruct "Hp" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & _)".
  iSplitL "Hf Hfl Hf2 Hfd Hm Hvt Hwd P0 P1 P2 P3 P4 P5 P6 P7 Hnb Hl Hw Hwvt Hb".
  { rewrite /wo_cells /wo_ptrs /fs_ptr Ps Mode Vt Wd Fd /=. by iFrame. }
  iIntros (fl f2 nb' w' b stop j' (S & F & Bits & B2 & User & Bound & End)) "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & Hb)".
  iExists fb, fr, (wo_state st fl f2 b stop), nb', tw, tm, wr, j'. iSplit; [iPureIntro; split; [done|lia]|].
  rewrite /file_wide_at. iSplit; [iPureIntro; eapply wo_state_ok; eassumption|]. iFrame "Hf Hlk Hnb".
  iSplitL "Hfl Hp P8 P9 P10 P11 Hfd Hf2 Ho Hcol Hlock Hof Hcv Hwd Hfr Hbuf Hm Htot Hvt".
  { rewrite /file_fields /wo_state /fs_ptr /wo_reset_ptrs Ps /= Mode Vt Wd Fd. iDestruct "Hp" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & _)". by iFrame. }
  iExists ib, ie, ob, oe, ifl, icnt, ofl, ocnt, sb, scs. iFrame. iPureIntro.
  destruct U as (? & ? & ? & ? & _ & ? & ? & ? & ? & ?). split_and!; try assumption. apply window_ptrs_ok; try assumption; lia.
Qed.
End loan.
