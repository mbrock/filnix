(** Glibc resumes a short-option cluster through a saved character pointer.
    An index bound alone cannot justify that resume: the pointer must still
    belong to the argument selected by the public index. This file describes
    the private cells and their relation to the caller's argument vector.

    The caller keeps the argument array and public option variables separate
    from the parser's private object. Saved character pointers borrow their
    strings read-only, including the surrounding words that glibc loads.
    These definitions describe valid sessions; the scanner must still be
    proved to preserve them. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv WordString.
From Glibc Require FileInv.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** These values correspond to the fields of the captured 56-byte structure. *)
Record getopt_state := mkGetoptState {
  gs_ind : Z;
  gs_err : Z;
  gs_opt : Z;
  gs_arg : ptr;
  gs_initialized : Z;
  gs_next : ptr;
  gs_order : Z;
  gs_first : Z;
  gs_last : Z
}.

(** Static storage initially contains zeroes, before the wrapper copies globals. *)
Definition getopt_zero : getopt_state := mkGetoptState 0 0 0 null 0 null 0 0 0.

(** Pending nonoptions occupy a bounded interval. At end of input, glibc
    rewinds optind to the first nonoption while last_nonopt may remain argc. *)
Definition getopt_bounds (n i : Z) (s : getopt_state) : Prop :=
  1 <= n < 2 ^ 31 /\ 0 <= i <= n /\
  0 <= gs_first s <= gs_last s /\ gs_last s <= n /\ gs_first s <= i.

(** Restarting an idle scan clamps both endpoints before exchanging arguments. *)
Lemma getopt_clamped_bounds n i s : getopt_bounds n i s ->
  0 <= Z.min (gs_first s) i <= Z.min (gs_last s) i /\ Z.min (gs_last s) i <= i.
Proof. unfold getopt_bounds. intros H. lia. Qed.

(** The all-zero private object is compatible with the initial public index. *)
Lemma getopt_zero_bounds n : 1 <= n < 2 ^ 31 -> getopt_bounds n 1 getopt_zero.
Proof. unfold getopt_bounds, getopt_zero; cbn. lia. Qed.

(** The parser and its caller use the same [[separation-logic]] instance
    so that their descriptions of the heap remain compatible. *)
(** File-field rules supply the existing four-byte integer representation. *)
Import FileInv FileInv.ML FileInv.LG FileInv.L.

Section state.
Context `{!gen_heapGS piece pval Σ}.

(** Private fields occupy their captured offsets; padding remains framed out. *)
Definition getopt_state_own (b : Z) (r : region) (s : getopt_state) : iProp Σ :=
  ⌜0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48⌝ ∗ live b r ∗
  int_cell b 0 (gs_ind s) ∗ int_cell b 4 (gs_err s) ∗ int_cell b 8 (gs_opt s) ∗
  pcell b 16 (gs_arg s) ∗ int_cell b 24 (gs_initialized s) ∗ pcell b 32 (gs_next s) ∗
  int_cell b 40 (gs_order s) ∗ int_cell b 44 (gs_first s) ∗ int_cell b 48 (gs_last s).

(** An idle cursor is null or points at a readable terminator. A live cursor
    points into the current argument, which must precede the argv sentinel. *)
Definition getopt_cursor (ps : list ptr) (i : Z) (s : getopt_state) : iProp Σ :=
  ⌜gs_next s = null⌝ ∨ word_string DfracDiscarded (gs_next s) [] ∨
  ∃ q prefix suffix,
    ⌜0 <= i < Z.of_nat (length ps) /\ nth_error ps (Z.to_nat i) = Some q /\
      suffix <> [] /\ gs_next s = ptr_add q (Z.of_nat (length prefix)) /\ gs_last s <= i⌝ ∗
    word_string DfracDiscarded q (prefix ++ suffix).

(** The session ties the private object to this argv shape and public index.
    A fresh object needs no saved cursor; initialized state must agree with
    the public index and retain one of glibc's three ordering modes. *)
Definition getopt_session (b : Z) (r : region) (av : Z) (ar : region)
    (ps : list ptr) (i : Z) : iProp Σ :=
  ⌜0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar /\
    r_end ar <= 2 ^ 48⌝ ∗
  ∃ s, getopt_state_own b r s ∗ ⌜getopt_bounds (Z.of_nat (length ps)) i s⌝ ∗
    (⌜s = getopt_zero /\ i = 1⌝ ∨
      (⌜gs_initialized s = 1 /\ gs_ind s = i /\ 0 <= gs_order s <= 2⌝ ∗ getopt_cursor ps i s)).

(** Initial session construction consumes the real zeroed private fields.
    It neither allocates fictional ownership nor assumes the next call safe. *)
Lemma getopt_session_initial b r av ar ps :
  1 <= Z.of_nat (length ps) < 2 ^ 31 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  getopt_state_own b r getopt_zero -∗ getopt_session b r av ar ps 1.
Proof.
  intros Hn Hav Ha Hfit Hspace. iIntros "Hs". iSplit; [iPureIntro; lia|].
  iExists getopt_zero. iFrame. iSplit; [iPureIntro; by apply getopt_zero_bounds|].
  iLeft. done.
Qed.

(** Reading a saved cursor exposes its suffix without losing the containing
    word. A nonempty suffix also supplies the strict index bound for resume. *)
Lemma getopt_cursor_read ps i s : getopt_cursor ps i s -∗
  ⌜gs_next s = null⌝ ∨ ∃ tail, word_string DfracDiscarded (gs_next s) tail ∗
    ⌜tail <> [] -> 0 <= i < Z.of_nat (length ps) /\ gs_last s <= i⌝.
Proof.
  iIntros "[Hnull | [Hempty | Hactive]]".
  - iLeft. iExact "Hnull".
  - iRight. iExists []. iFrame. iPureIntro. congruence.
  - iDestruct "Hactive" as (q prefix suffix) "(%H & Hs)".
    destruct H as (Hi & Hq & Hne & Hnext & Hlast).
    iRight. iExists suffix. rewrite Hnext.
    iSplit; [by iApply word_string_suffix|]. iPureIntro. auto.
Qed.

End state.
