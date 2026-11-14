From Glibc Require Import GlibcProgram.
(** The getopt wrapper copies the parser's argument pointer into the
    public optarg. Fil-C pointers carry a capability, so a caller that
    later reads optarg needs to know that the capability names a live
    object and that the address fits in a machine word. The long-option
    parser leaves the argument where it was, points it after the equals
    sign of the current word, or points it at the next word of the
    vector. This file shows that each choice carries such a capability,
    using the strings the caller already shares with the parser. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Values Memory Runtime Pieces Heap Logic.
From Glibc Require Import FileInv WordString GetoptState GetoptBytes GetoptArgv GetoptExchange GetoptLongScan
  GetoptLongExact GetoptLongStore GetoptLongJoinMiss.
From Glibc Require FileInv GetoptExchange GetoptLongJoinMiss GetoptState.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** ## Where the argument can point

    The capability of a pointer survives pointer arithmetic, so a
    pointer into the middle of a word names the same object as the
    word. A pointer past the end of the vector is null, and a null
    pointer carries no capability. The controls below check both facts
    on small examples. *)

(** A pointer three bytes into a read-only word keeps the word's capability. *)
Lemma long_cap_ctl_add : ptr_cap (ptr_add (mkPtr 4096 (Ro 4096)) 3) = Ro 4096 /\
  ptr_addr (ptr_add (mkPtr 4096 (Ro 4096)) 3) = 4099.
Proof. split; reflexivity. Qed.

(** The vector [q0; q1] has no word at index 2, so the next word there is null. *)
Lemma long_cap_ctl_end : nth 2 [mkPtr 64 (Obj 64); mkPtr 96 (Obj 96)] null = null /\
  nth 1 [mkPtr 64 (Obj 64); mkPtr 96 (Obj 96)] null = mkPtr 96 (Obj 96).
Proof. split; reflexivity. Qed.

Import GetoptLongJoinMiss GetoptExchange GetoptState FileInv FileInv.ML FileInv.LG FileInv.L GetoptArgv.

Section cap.
Context `{!gen_heapGS piece pval Σ}.

(** ## The parser's return with a usable argument

    The wrapper needs the argument's capability at the moment it copies
    the argument out. The state below is the state after a long-option
    return, with one more fact about the argument. The original state
    stays available for the proofs that already use it. *)

(** After a return, the caller holds everything that the original
    return state gives it. In addition, the argument's capability names
    a live object, or no object at all, and its address lies below 2^64. *)
Definition plo_res_cap (b : Z) (r : region) (av : Z) (ar : region) (ps : list ptr) (li : ptr) (F : list ptr)
    (G M : iProp Σ) (i n : Z) (cur : ptr) (s : list Z) (a : ptr) (os : list lopt) (x : Z) : iProp Σ :=
  ∃ i' oo' a' c', live b r ∗ int_cell b 0 i' ∗ int_cell b 8 oo' ∗ pcell b 16 a' ∗ pcell b 32 c' ∗
    live av ar ∗ argv_cells av ps ∗ G ∗ flags_own F ∗ M ∗ longind_own li ∗
    (∃ ra, live_capq DfracDiscarded (ptr_cap a') ra) ∗ ⌜0 <= ptr_addr a' < 2 ^ 64⌝ ∗
    ⌜((i <= i' <= i + 1 \/ (i' = i + 2 /\ i + 1 < n)) /\
      (c' = null \/ (c' = cur /\ i' = i) \/ c' = ptr_add cur (Z.of_nat (List.length s))) /\
      (a' = a \/ a' = ptr_add cur (Z.of_nat (eq_len s) + 1) \/ a' = nth (Z.to_nat (i + 1)) ps null) /\
      0 <= x < 2 ^ 32 /\ (x = 4294967295 -> (c' = cur /\ i' = i) \/
        exists y, y ∈ os /\ lo_flag y = null /\ lo_val y mod 2 ^ 32 = 4294967295))%Z⌝.

(** Consumers of the original return state can drop the new fact. *)
Lemma plo_res_cap_old b r av ar ps li F (G M : iProp Σ) i n cur s a os x :
  plo_res_cap b r av ar ps li F G M i n cur s a os x ⊢ plo_res b r av ar ps li F G M i n cur s a os x.
Proof.
  iIntros "(%i' & %oo' & %a' & %c' & Hl & Hi & Ho & Ha & Hc & Hav & Hcl & HG & HF & HM & Hli & _ & _ & %H)".
  iExists i', oo', a', c'. iFrame. done.
Qed.

(** The argument that the parser chose has a usable capability. If the
    parser kept the old argument, the caller supplies its capability,
    because nothing about the private object constrains that pointer.
    If the argument points after the equals sign, the current word gives
    it. If it points at the next word, the vector gives it, or it is
    null when no next word exists. *)
Lemma plo_res_capped b r av ar ps li F (G M : iProp Σ) i n cur s a os x ra :
  word_string DfracDiscarded cur s -∗ argv_strs ps -∗
  live_capq DfracDiscarded (ptr_cap a) ra -∗ ⌜0 <= ptr_addr a < 2 ^ 64⌝ -∗
  plo_res b r av ar ps li F G M i n cur s a os x -∗
  plo_res_cap b r av ar ps li F G M i n cur s a os x.
Proof.
  iIntros "#Hws #Hs Hca %Ha (%i' & %oo' & %a' & %c' & Hl & Hi & Ho & Hab & Hc & Hav & Hcl & HG & HF & HM & Hli & %H)".
  iAssert ((∃ ra', live_capq DfracDiscarded (ptr_cap a') ra') ∗ ⌜0 <= ptr_addr a' < 2 ^ 64⌝)%I with "[Hca]" as "[Hcap %Hr]".
  { destruct H as (_ & _ & [-> | [-> | ->]] & _).
    - iSplitL "Hca"; [by iExists ra | done].
    - iDestruct (ws_shape with "Hws") as %(_ & Hc0 & Hce). pose proof (eq_len_le s).
      iDestruct (argv_str_cap with "Hws") as (rc) "[Hcc _]".
      iSplitL "Hcc"; [by iExists rc|]. iPureIntro. unfold ptr_add; cbn. lia.
    - destruct (Nat.lt_ge_cases (Z.to_nat (i + 1)) (List.length ps)) as [Hlt | Hge].
      + iDestruct (argv_strs_cap ps (Z.to_nat (i + 1)) Hlt with "Hs") as (rn) "[Hcn %Hn]".
        iSplitL "Hcn"; [by iExists rn | done].
      + rewrite (nth_overflow ps null Hge). iSplit; [by iExists ar | iPureIntro; cbn; lia]. }
  iExists i', oo', a', c'. iFrame "Hl Hi Ho Hab Hc Hav Hcl HG HF HM Hli Hcap". iPureIntro. auto.
Qed.

(** The first blocks of every call clear the argument, so a call that
    reaches the long-option parser from them holds a null argument. A
    null argument needs no capability from the caller. *)
Lemma plo_res_capped_null b r av ar ps li F (G M : iProp Σ) i n cur s os x :
  word_string DfracDiscarded cur s -∗ argv_strs ps -∗
  plo_res b r av ar ps li F G M i n cur s null os x -∗
  plo_res_cap b r av ar ps li F G M i n cur s null os x.
Proof.
  iIntros "#Hws #Hs H". iApply (plo_res_capped _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ar with "Hws Hs [] [] H").
  - done.
  - iPureIntro. cbn. lia.
Qed.

End cap.
