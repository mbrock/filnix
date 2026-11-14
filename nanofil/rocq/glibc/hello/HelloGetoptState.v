From Glibc Require Import GlibcProgram.
(** Hello calls getopt_long in a loop, and glibc keeps the parser's
    progress in a private object between the calls. A contract for the
    call must say what that object holds when the loop starts and after
    each call. This file names the states that Hello may start from and
    that each call leaves. The object may hold a session that matches the
    argument vector and the public index. It may also hold a session that
    the public index restarts by being zero, or zeroed storage before the
    first call. The lemmas below show that each such state lets the
    wrapper copy the public index in, that a session after a call is such
    a state, and that the loader's zeroed object gives one. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv WordString GetoptState GetoptEntryPre GetoptWrapParse GetoptInitial.
From Glibc Require FileInv GetoptState GetoptWrapParse GetoptInitial.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Import GetoptState FileInv FileInv.ML FileInv.LG FileInv.L.

Section state.
Context `{!gen_heapGS piece pval Σ}.

(** ## The states Hello admits

    Hello may start the loop with the parser fresh or part way through,
    and with optind anywhere from zero to argc. glibc accepts two kinds of
    object then. One holds a session that optind continues, or that optind
    restarts by being zero. The other holds only zeroes, as the loader
    leaves it, and then any optind up to argc works. *)

(** The object b holds a session that the index i continues or restarts.
    Otherwise it holds zeroes, and i lies within the count. *)
Definition hello_getopt_state (b : Z) (r : region) (av : Z) (ar : region) (ps : list ptr) (i : Z) : iProp Σ :=
  (∃ i0, ⌜i = i0 \/ i = 0⌝ ∗ getopt_session b r av ar ps i0) ∨
  (⌜0 < av /\ av mod 8 = 0 /\ av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar /\ r_end ar <= 2 ^ 48 /\
     1 <= Z.of_nat (length ps) < 2 ^ 31 /\ 0 <= i <= Z.of_nat (length ps)⌝ ∗ getopt_state_own b r getopt_zero).

(** A session that a call leaves at its own index is admissible. *)
Lemma hello_getopt_state_session b r av ar ps i :
  getopt_session b r av ar ps i ⊢ hello_getopt_state b r av ar ps i.
Proof. iIntros "H". iLeft. iExists i. iFrame "H". iPureIntro. left. reflexivity. Qed.

(** Zeroed storage is admissible at any index within the count. *)
Lemma hello_getopt_state_zero b r av ar ps i :
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  1 <= Z.of_nat (length ps) < 2 ^ 31 -> 0 <= i <= Z.of_nat (length ps) ->
  getopt_state_own b r getopt_zero ⊢ hello_getopt_state b r av ar ps i.
Proof. intros. iIntros "H". iRight. iFrame "H". iPureIntro. split_and!; lia. Qed.

(** The loader leaves the parser's object zeroed, so its pieces give such a state. *)
Lemma hello_getopt_state_loader av ar ps i :
  0 < av -> av mod 8 = 0 -> av + 8 * (Z.of_nat (length ps) + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  1 <= Z.of_nat (length ps) < 2 ^ 31 -> 0 <= i <= Z.of_nat (length ps) ->
  pts getopt_private_pieces ⊢ hello_getopt_state 65584 getopt_private_region av ar ps i.
Proof.
  intros. rewrite getopt_private_own. by apply hello_getopt_state_zero.
Qed.

End state.

Section copy.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** ## The copy of the public index

    The wrapper writes optind and opterr into the object before the
    parser runs. Every admissible state lets the wrapper do so with the
    public index i and any error flag. *)

(** Each of these states lets the wrapper copy the index i into the object. *)
Lemma hello_getopt_state_copy_in b r av ar ps i err :
  hello_getopt_state b r av ar ps i ⊢ copy_in_view b r av ar ps i err.
Proof.
  iIntros "[(%i0 & %Hi & Hs) | (%H & Hz)]".
  - iApply (session_copy_in with "Hs"). exact Hi.
  - destruct H as (H1 & H2 & H3 & H4 & H5 & H6). iApply (zero_copy_in with "Hz"); assumption.
Qed.

End copy.
