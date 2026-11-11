(** The length and output routines read the same string in different
    ways: one reads whole machine words, and the other reads bytes.
    This file converts between their memory requirements without
    losing any part of the string, including the bytes surrounding
    it in the first and last words. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import StrlenBits StrlenLogic WordString LibioDefaultXsputnBuf HiAtexitBase HiAtexitOutputState.
Import ListNotations.
Open Scope Z_scope.

(** The byte borrowing rules use the interpreter's memory logic. *)
Import HXS.XE.XL.XU.XW.XD.XC.XR.XF.XS.
Import XB.DX.RM.SM.TL.BY.BF XB.DX.RM.SM.TL.BY.BF.CP XB.DX.RM.SM.TL.BY.BF.CP.CS
  XB.DX.RM.SM.TL.BY.BF.CP.CS.SW XB.DX.RM.SM.TL.BY.BF.CP.CS.SW.FI.ML
  XB.DX.RM.SM.TL.BY.BF.CP.CS.SW.FI.LG XB.DX.RM.SM.TL.BY.BF.CP.CS.SW.FI.L.

(** The byte pieces owned by a word window are exactly the pieces
    owned by its flattened byte sequence. *)
Lemma hi_words_ps_bytes b o ws : words_ps b o ws = byte_ps b o (wbytes ws).
Proof.
  revert o. induction ws as [|w ws IH]; intros o; [reflexivity|].
  cbn [words_ps]. rewrite wbytes_cons byte_ps_app IH. cbn [length map idx8].
  f_equal. unfold cell. cbn [map idx8]. rewrite !byte_ps_cons.
  cbn [byte_ps length seqZ zip_with]. repeat first [reflexivity | lia | f_equal].
Qed.

Section strings.
Context `{!gen_heapGS piece pval Σ}.

(** The string's bytes can be lent out at its existing share. Returning
    them and the object's life restores the full aligned word window,
    including bytes before the string and after its terminating NUL. *)
Lemma hi_word_string_bytes dq p s :
  word_string dq p s ⊢ ∃ b reg so,
    ⌜p = mkPtr (b + so) (ptr_cap p) /\ (ptr_cap p = Obj b \/ ptr_cap p = Ro b) /\
      0 < b /\ b mod 8 = 0 /\ 0 <= so /\ b + so + Z.of_nat (length s) <= r_end reg /\
      r_end reg <= 2 ^ 48 /\ Forall (fun y => 0 <= y < 256) s⌝ ∗
    liveq dq b reg ∗ bytesq dq b so s ∗
    (liveq dq b reg -∗ bytesq dq b so s -∗ word_string dq p s).
Proof.
  iIntros "(%b & %reg & %ws & %Hs & Hl & Hw)".
  pose proof Hs as Hshape.
  destruct Hshape as [Hcap Hb Hal Hstart Hfit Hspace Hlen Hwords Hbytes Hchars].
  set (j := Z.to_nat (ptr_addr p mod 8)).
  assert (Hj : Z.of_nat j = ptr_addr p mod 8) by (unfold j; pose proof (Z.mod_pos_bound (ptr_addr p) 8 ltac:(lia)); lia).
  fold j in Hbytes.
  assert (Hroom : (j + length s <= length (wbytes ws))%nat).
  { pose proof (f_equal (@length Z) Hbytes) as Hlength.
    rewrite length_take length_drop length_app in Hlength. cbn [length] in Hlength. lia. }
  assert (Htake : take (length s) (drop j (wbytes ws)) = s).
  { apply (f_equal (take (length s))) in Hbytes.
    rewrite take_take Nat.min_l in Hbytes; [|lia].
    rewrite take_app_length in Hbytes. exact Hbytes. }
  iAssert (bytesq dq b (wstart p - b) (wbytes ws)) with "[Hw]" as "Hw".
  { unfold bytesq. rewrite -hi_words_ps_bytes. iExact "Hw". }
  iDestruct (bytesq_sub dq b (wstart p - b) (wbytes ws) j (length s) Hroom with "Hw") as "[Hbytes Hback]".
  rewrite Htake. replace (wstart p - b + Z.of_nat j) with (ptr_addr p - b) by (unfold wstart; lia).
  iExists b, reg, (ptr_addr p - b). iFrame "Hl Hbytes".
  iSplitR.
  - iPureIntro. split_and!; try assumption; try lia.
    + destruct p. cbn. f_equal; lia.
    + rewrite wbytes_length in Hroom. unfold wstart in Hfit. lia.
    + apply Forall_forall. intros x Hx.
      apply Forall_forall with (x := x) in Hchars; [lia | exact Hx].
  - iIntros "Hl Hbytes". iDestruct ("Hback" with "Hbytes") as "Hw".
    iExists b, reg, ws. iSplit; [done|]. unfold wwin. iFrame "Hl".
    unfold bytesq in *. rewrite hi_words_ps_bytes. iExact "Hw".
Qed.

End strings.
