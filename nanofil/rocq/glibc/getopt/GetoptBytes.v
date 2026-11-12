(** The option scanner reads single characters from argument strings,
    from its option string and from saved cursors. Those strings are
    shared read-only, so the scanner owns only a discarded share of each
    one. This file turns such a share into the lifetime and byte pieces
    that one checked character load needs.

    The scanner compares each loaded character with small constants.
    A signed byte load extends characters above 127 to negative values,
    so this file also states which comparisons that extension preserves. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  Pieces Heap Language Logic StringLogic MemLogic StepRules.
From Glibc Require Import StrlenBits StrlenLogic WordString.
Import ListNotations.
Open Scope Z_scope.

(** ## Characters as signed bytes

    The captured scanner loads characters with signed byte loads into
    32-bit registers. The following definitions name that register value
    and show that it equals a small constant exactly when the byte does. *)

(** A signed byte load of the character x produces this register value. *)
Definition chr_w (x : Z) : Z := sign_extension 256 128 x mod 2 ^ 32.

(** The scanner loads exactly [chr_w] for a single byte. *)
Lemma extended_chr x : extended Sb W (of_bytes [x]) = Some (WInt (chr_w x)).
Proof. unfold extended, chr_w, of_bytes. cbn. rewrite Z.add_0_r. reflexivity. Qed.

(** A character below 128 keeps its value after extension. *)
Lemma chr_w_small x : 0 <= x < 128 -> chr_w x = x.
Proof.
  intros Hx. unfold chr_w, sign_extension. rewrite (Z.mod_small x 256); [|lia].
  rewrite (proj2 (Z.leb_gt 128 x)); [|lia]. apply Z.mod_small. lia.
Qed.

(** A character from 128 upward becomes a large unsigned register value. *)
Lemma chr_w_large x : 128 <= x < 256 -> chr_w x = x - 256 + 2 ^ 32.
Proof.
  intros Hx. unfold chr_w, sign_extension. rewrite (Z.mod_small x 256); [|lia].
  rewrite (proj2 (Z.leb_le 128 x)); [|lia].
  rewrite <- (Z.mod_small (x - 256 + 2 ^ 32) (2 ^ 32)) by lia.
  rewrite Zplus_mod Z_mod_same_full Z.add_0_r Z.mod_mod; [reflexivity | lia].
Qed.

(** Every extended character is a 32-bit register value. *)
Lemma chr_w_range x : 0 <= chr_w x < 2 ^ 32.
Proof. unfold chr_w. apply Z.mod_pos_bound. lia. Qed.

(** An extended byte equals a constant below 128 exactly when the byte does. *)
Lemma chr_w_eqb x k : 0 <= x < 256 -> 0 <= k < 128 -> (chr_w x =? k) = (x =? k).
Proof.
  intros Hx Hk. destruct (Z.lt_ge_cases x 128).
  - rewrite chr_w_small; [reflexivity | lia].
  - rewrite chr_w_large; [|lia]. rewrite (proj2 (Z.eqb_neq _ _)); [|lia].
    symmetry. apply Z.eqb_neq. lia.
Qed.

(** This function reads the byte at index k of a string, and index [length s] reads its terminator. *)
Definition sbyte (s : list Z) (k : nat) : Z := nth k (s ++ [0]) 0.

(** The terminator of a string is zero. *)
Lemma sbyte_end s : sbyte s (length s) = 0.
Proof. unfold sbyte. rewrite app_nth2; [|lia]. rewrite Nat.sub_diag. reflexivity. Qed.

(** Bytes before the terminator are the string's own characters. *)
Lemma sbyte_in s k : (k < length s)%nat -> sbyte s k = nth k s 0.
Proof. intros Hk. unfold sbyte. rewrite app_nth1; [reflexivity | exact Hk]. Qed.

(** A string's bytes, including its terminator, fit in an unsigned byte. *)
Lemma sbyte_range s k : Forall (fun c => 0 < c < 256) s -> 0 <= sbyte s k < 256.
Proof.
  intros Hs. unfold sbyte. destruct (Nat.lt_ge_cases k (length s)) as [Hk|Hk].
  - rewrite app_nth1; [|exact Hk]. rewrite Forall_forall in Hs.
    specialize (Hs (nth k s 0) (nth_In s 0 Hk)). lia.
  - rewrite app_nth2; [|exact Hk]. destruct (k - length s)%nat as [|[|j]]; cbn; lia.
Qed.

(** Only the terminator of a string is zero. *)
Lemma sbyte_zero s k : Forall (fun c => 0 < c < 256) s -> (k <= length s)%nat ->
  sbyte s k = 0 <-> k = length s.
Proof.
  intros Hs Hk. split; [|intros ->; apply sbyte_end].
  intros Hz. destruct (Nat.eq_dec k (length s)) as [|Hne]; [assumption|].
  assert (Hlt : (k < length s)%nat) by lia.
  rewrite sbyte_in in Hz; [|exact Hlt]. rewrite Forall_forall in Hs.
  specialize (Hs (nth k s 0) (nth_In s 0 Hlt)). lia.
Qed.

(** Byte support shares the caller's [[runtime]] and logic instance. *)
Module GetoptBytesOn (R : Runtime) (LG0 : LogicSig R).
(** The string window comes from the word-string module. *)
Module WS := WordStringOn R LG0.
(** Byte ownership comes from the memory logic. *)
Module ML := MemLogicOn R LG0.
Import ML.
Import LG0 LG0.L WS.

Section bytes.
Context `{!gen_heapGS piece pval Σ}.

(** A shared string is a well-formed string window. *)
Lemma ws_shape p s : word_string DfracDiscarded p s ⊢
  ⌜Forall (fun c => 0 < c < 256) s /\ 0 < ptr_addr p /\
   ptr_addr p + Z.of_nat (length s) + 1 <= 2 ^ 48⌝.
Proof.
  iIntros "(%b & %reg & %ws & %Hs & _)". iPureIntro.
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hr Hby Hch]. unfold wstart in Hf.
  pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)). split; [exact Hch | lia].
Qed.

(** A shared string supplies the lifetime and byte piece at any index up
    to its terminator. The lifetime covers the terminator, so the scanner
    can check a one-byte read at that index. *)
Lemma ws_byte p s (k : nat) : (k <= length s)%nat ->
  word_string DfracDiscarded p s ⊢ ∃ b reg,
    ⌜(ptr_cap p = Obj b \/ ptr_cap p = Ro b) /\ 0 < b /\ b <= ptr_addr p /\
     ptr_addr p + Z.of_nat (length s) + 1 <= r_end reg /\ r_end reg <= 2 ^ 48⌝ ∗
    liveq DfracDiscarded b reg ∗ bytesq DfracDiscarded b (ptr_addr p + Z.of_nat k - b) [sbyte s k].
Proof.
  intros Hk. iIntros "(%b & %reg & %ws & %Hs & Hl & Hw)".
  pose proof Hs as [Hc Hb0 Hb8 Hst Hf Hsp Hlen Hr Hby Hch]. unfold wstart in Hf.
  pose proof (Z.div_mod (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p mod 8 + Z.of_nat (length s) + 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)).
  iExists b, reg. iSplit; [iPureIntro; repeat split; auto; lia|]. iFrame "Hl".
  pose proof (str_shape_byte p b reg ws s k Hs Hk) as E.
  assert (Hx : wbytes ws !! (Z.to_nat (ptr_addr p mod 8) + k)%nat = Some (sbyte s k)).
  { rewrite E. destruct ((s ++ [0]) !! k) as [x|] eqn:Ek.
    - unfold sbyte. by rewrite (nth_lookup_Some _ _ 0 _ Ek).
    - apply lookup_ge_None in Ek. rewrite length_app in Ek. cbn in Ek. lia. }
  pose proof (words_ps_elem b (ptr_addr p - ptr_addr p mod 8 - b) ws _ _ Hx) as Hin.
  replace (ptr_addr p - ptr_addr p mod 8 - b + Z.of_nat (Z.to_nat (ptr_addr p mod 8) + k))
    with (ptr_addr p + Z.of_nat k - b) in Hin by lia.
  rewrite /bytesq byte_ps_cons /byte_ps /ptsq /=. iSplit; [|done].
  iApply (big_sepL_elem_of _ _ _ Hin with "Hw").
Qed.

(** A shared string remains readable at every advanced position. *)
Lemma ws_suffix p s k : (k <= length s)%nat ->
  word_string DfracDiscarded p s ⊢
  word_string DfracDiscarded (ptr_add p (Z.of_nat k)) (drop k s).
Proof.
  intros Hk. iIntros "H". rewrite -{1}(take_drop k s).
  iDestruct (word_string_suffix with "H") as "H".
  assert (Hl : length (take k s) = k) by (apply length_take_le; exact Hk).
  iEval (rewrite Hl) in "H". iExact "H".
Qed.

(** Reading the first byte of an advanced position reads the original byte. *)
Lemma sbyte_drop s k j : (k <= length s)%nat -> sbyte (drop k s) j = sbyte s (k + j).
Proof.
  intros Hk. unfold sbyte.
  assert (Hl : length (take k s) = k) by (apply length_take_le; exact Hk).
  rewrite -{2}(take_drop k s) -app_assoc (app_nth2 (take k s)); rewrite Hl; [|lia].
  f_equal. lia.
Qed.

End bytes.
End GetoptBytesOn.
