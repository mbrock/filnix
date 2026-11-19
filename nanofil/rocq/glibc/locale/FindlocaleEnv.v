(** Glibc chooses a locale by looking for a variable in the environment.
    When several entries have the same name, getenv returns a pointer
    into the first one. The caller needs the bytes at that pointer, not
    just the fact that some entry has an allowed value. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import List String ZArith.
From Nanofil Require Import Term Syntax Values Memory Pieces Heap Logic.
From Glibc Require Import WordString ByteRead GetenvCompare GetenvScan GetenvStatic.
Import ListNotations.
Open Scope Z_scope.
Open Scope list_scope.

Section lookup.
Context `{!gen_heapGS piece pval Σ}.

(** A missing variable has a null pointer. A present variable has a
    readable string whose bytes satisfy the caller's restriction. The
    empty string is a present value, not a null pointer. *)
Definition findlocale_value (ok : list Z -> Prop) q : iProp Σ :=
  ⌜q = null⌝ ∨ ∃ v, ⌜ok v⌝ ∗ word_string DfracDiscarded q v.

Local Lemma findlocale_cells p s dq dqt b o es ok :
  s <> [] -> (forall v, In (s ++ 61 :: v) (map entry_text es) -> ok v) ->
  word_string DfracDiscarded p s -∗ getenv_cells dq dqt b o es -∗
  getenv_cells dq dqt b o es ∗ findlocale_value ok (getenv_scan_result s es).
Proof using Type.
  intros Hne. revert o. induction es as [|x xs IH]; intros o Hok;
    iIntros "#Hname Hcells"; cbn [getenv_cells getenv_scan_result].
  - iFrame. iLeft. done.
  - iDestruct "Hcells" as "(Hcell & Htarget & #Ht & Htail)".
    destruct (getenv_entry_matches s (entry_text x)) eqn:E.
    + iDestruct (ws_shape with "Hname") as %(Hs & _). iDestruct (ws_shape with "Ht") as %(Hx & _).
      destruct (proj1 (getenv_entry_matches_iff _ _ Hs Hx Hne) E) as [v Hv].
      iFrame "Hcell Htarget Ht Htail". iRight. iExists v. iSplit; [iPureIntro; apply Hok; left; exact Hv|].
      iEval (rewrite Hv) in "Ht". replace (s ++ 61 :: v) with ((s ++ [61]) ++ v) by (rewrite <- app_assoc; reflexivity).
      iPoseProof (word_string_suffix DfracDiscarded (entry_ptr x) (s ++ [61]) v with "Ht") as "Hv".
      rewrite length_app Nat2Z.inj_add. cbn. iExact "Hv".
    + iDestruct (IH (o+8) with "Hname Htail") as "[Htail Hv]"; [intros v H; apply Hok; right; exact H|].
      iFrame "Hcell Htarget Ht Htail Hv".
Qed.

(** The environment keeps all its shares. Every matching entry must
    meet the restriction, so the first matching entry meets it too. *)
Lemma findlocale_getenv_value p s dq dqt ep es (ok : list Z -> Prop) :
  (forall v, In (s ++ 61 :: v) (map entry_text es) -> ok v) ->
  word_string DfracDiscarded p s -∗ getenv_storage dq dqt ep es -∗
  getenv_storage dq dqt ep es ∗ findlocale_value ok (getenv_result s es).
Proof using Type.
  intros Hok. iIntros "#Hname HS". destruct s as [|c s]; [iFrame; iLeft; done|].
  iDestruct "HS" as "[%Hnil|HS]".
  - destruct Hnil as [-> ->]. iSplit; iLeft; done.
  - iDestruct "HS" as (b reg o ->) "(%Hfit & Hl & Hcells)".
    iDestruct (findlocale_cells _ _ _ _ _ _ _ ok with "Hname Hcells") as "[Hcells Hv]"; [discriminate|exact Hok|].
    iFrame "Hv". iRight. iExists b, reg, o. iSplit; [done|]. iFrame. done.
Qed.
End lookup.
