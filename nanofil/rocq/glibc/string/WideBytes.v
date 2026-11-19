(** Each wide character occupies four little-endian bytes. A reader
    can borrow any character and return it to recover the array. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Values Memory Pieces Heap StringLogic MemLogic WordBits.
From Glibc Require Import Fix.
Import ListNotations Fix.LG0 Fix.ML0.
Open Scope Z_scope.

(** The stream counts characters, but the array stores four bytes per character. *)
Definition stage_bytes (cs : list Z) := flat_map (fun c => le_bytes c 4) cs.
Lemma stage_bytes_length cs : length (stage_bytes cs) = (4 * length cs)%nat.
Proof. induction cs as [|c cs IH]; [done|]. change (length (le_bytes c 4 ++ stage_bytes cs) = (4 * S (length cs))%nat).
  rewrite length_app length_le_bytes IH. lia. Qed.

Lemma stage_bytes_valid cs : Forall (fun b => 0 <= b < 256) (stage_bytes cs).
Proof. induction cs as [|c cs IH]; [constructor|]. apply Forall_app. split; [|exact IH].
  apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (i & <- & _). apply byte_of_range. Qed.

Section read.
Context `{!gen_heapGS piece pval Σ}.

(** The reader borrows one whole character. The same rule applies to
    the mutable argument and the read-only format literal. *)
Lemma wchar_at dq b o cs k x : cs !! k = Some x ->
  bytesq dq b o (stage_bytes cs) ⊢ bytesq dq b (o + 4*Z.of_nat k) (le_bytes x 4) ∗
    (bytesq dq b (o + 4*Z.of_nat k) (le_bytes x 4) -∗ bytesq dq b o (stage_bytes cs)).
Proof using Type.
  intros Hk. rewrite -{1 2}(take_drop_middle cs k x Hk) /stage_bytes flat_map_app. cbn [flat_map].
  rewrite /bytesq byte_ps_app byte_ps_app !ptsq_app. fold (stage_bytes (take k cs)).
  rewrite stage_bytes_length length_take_le; [|apply lookup_lt_Some in Hk; lia].
  replace (Z.of_nat (4*k)) with (4*Z.of_nat k) by lia. iIntros "(Hp & Hc & Hs)". iFrame "Hc". iIntros "Hc". iFrame.
Qed.

End read.
