(** This file connects Hello's small memory calls to their proved glibc
    implementations. It proves zeroing, string length, bounded comparison
    and errno lookup over the concrete resources used by main.

    The interface exports the call contracts but hides their internal
    proof modules. Later composition therefore reuses the results
    without repeating the large proof substitutions. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloLeaf.
From Glibc Require Import OsWorld OsRegistry WordString StrlenLogic StrcmpBits StrncmpBits StrncmpCode
  LeavesLogic StrlenWord StrncmpLogic MemFwdLogic HelloGlibcDebts HelloGlibcLibsT.
From Glibc Require LeavesLogic MemFwdLogic OsWorld StrlenWord StrncmpLogic.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** strcmp's answer lies in a `c: int`'s bits. *)
Lemma strcmp_res_range s1 s2 : 0 <= strcmp_res s1 s2 < 2 ^ 32.
Proof.
  revert s2. induction s1 as [|c1 s1 IH]; intros [|c2 s2]; cbn;
    try (apply Z.mod_pos_bound; lia); [lia|].
  destruct (c1 =? c2); [apply IH | apply Z.mod_pos_bound; lia].
Qed.

(** A multiple of 16 is a multiple of 8. *)
Lemma mod16_mod8' b : b mod 16 = 0 -> b mod 8 = 0.
Proof. intros H. apply Z.mod_divide; [lia|]. apply Z.mod_divide in H; [|lia]. destruct H as [k ->]. exists (2 * k). lia. Qed.

(** This interface exposes the proved string and memory call contracts. *)
Module Type HelloLibsStrSig (D : HelloDebtsT).
Import LG0 LG0.L D D.SW.FI.ML.
(** `mbszero` zeroes the 16-byte object b, over glibc's `memset`. *)
Parameter libs_mbszero : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv)
  (o : hello_objs),
  hello_link ge o -> forall b, 0 < b -> b mod 16 = 0 -> b + 16 <= 2 ^ 48 ->
  D.fn_triple w0 ge (TAtom "mbszero") [WPtr (mkPtr b (Obj b))] (obj b (heap_req 4 8))
    (fun r => ⌜r = RetVoid⌝ ∗ obj b (heap_req 4 8))%I.
(** glibc's `strlen` of a string at any share returns its length. *)
Parameter libs_strlen : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv)
  (o : hello_objs),
  hello_link ge o -> forall dq p s,
  D.fn_triple w0 ge (TAtom "strlen") [WPtr p] (word_string dq p s)
    (fun r => ⌜r = Ret (WInt (Z.of_nat (length s)))⌝ ∗ word_string dq p s)%I.
(** glibc's `strncmp` of two read-only strings and 3 returns a `c: int`. *)
Parameter libs_strncmp : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv)
  (o : hello_objs),
  hello_link ge o -> forall p1 p2 s1 s2,
  D.fn_triple w0 ge (TAtom "strncmp") [WPtr p1; WPtr p2; WInt 3]
    (word_string DfracDiscarded p1 s1 ∗ word_string DfracDiscarded p2 s2)
    (fun r => ∃ k, ⌜r = Ret (WInt k) /\ 0 <= k < 2 ^ 32⌝)%I.
(** glibc's `__errno_location` returns the pointer to `c: errno`. *)
Parameter libs_errno : forall `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ} (w0 : os_world) (ge : genv)
  (o : hello_objs),
  hello_link ge o ->
  D.fn_triple w0 ge (TAtom "__errno_location") [] True
    (fun r => ⌜r = Ret (WPtr (mkPtr (ho_eb o) (Obj (ho_eb o))))⌝)%I.
End HelloLibsStrSig.

(** The implementation proves the triples over the caller's runtime and logic. *)
Module HelloGlibcLibsStrOn (D : HelloDebtsT) : HelloLibsStrSig D.
(** The memory proof supplies the memset call used by mbszero. *)
Module MF := MemFwdLogic.
(** The length proof reads glibc strings one word at a time. *)
Module SL := StrlenWord.
(** The comparison proof bounds the number of bytes read. *)
Module SN := StrncmpLogic.
(** The leaf proofs provide the concrete errno call. *)
Module LV := LeavesLogic.
Import LG0 LG0.L D D.SW.FI.ML.

Section libs.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The 16-byte object of an 8-byte request, zeroed, splits at 8. *)
Lemma obj16_split b : obj b (heap_req 4 8) ⊢
  live b (mkRegion b (b + 16) Heap Live) ∗ bytes b 0 (replicate 8 0) ∗ bytes b 8 (replicate 8 0) ∗
  auxes b 0 (replicate 8 CNone) ∗ auxes b 8 (replicate 8 CNone).
Proof.
  rewrite (obj_zero_block b _); [|vm_compute; congruence].
  change (req_extent (heap_req 4 8)) with 16. change (req_kind (heap_req 4 8)) with Heap.
  change (replicate (Z.to_nat 16) 0) with (replicate 8 0 ++ replicate 8 0).
  change (replicate (Z.to_nat 16) CNone) with (replicate 8 CNone ++ replicate 8 CNone).
  rewrite bytes_app auxes_app. cbn [length replicate]. iIntros "($ & [$ $] & [$ $])".
Qed.

(** The cleared slots combine with the other pieces to reconstruct the object. *)
Lemma obj16_join b :
  live b (mkRegion b (b + 16) Heap Live) -∗ bytes b 0 (replicate 8 0) -∗ bytes b 8 (replicate 8 0) -∗
  auxes b 0 (MemLogic.clear_slots 0 (replicate 8 CNone)) -∗ auxes b 8 (replicate 8 CNone) -∗ obj b (heap_req 4 8).
Proof.
  rewrite (obj_zero_block b _); [|vm_compute; congruence].
  change (req_extent (heap_req 4 8)) with 16. change (req_kind (heap_req 4 8)) with Heap.
  change (replicate (Z.to_nat 16) 0) with (replicate 8 0 ++ replicate 8 0).
  change (replicate (Z.to_nat 16) CNone) with (replicate 8 CNone ++ replicate 8 CNone).
  rewrite bytes_app auxes_app. cbn [length replicate].
  change (MemLogic.clear_slots 0 (replicate 8 CNone)) with (replicate 8 CNone).
  iIntros "$ $ $ $ $".
Qed.

Context (w0 : os_world) (ge : genv) (o : hello_objs).

(** [os_wi] w0 survives safepoints. *)
Local Instance str_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses glibc's OS registry and concrete world interpretation. *)
Local Instance str_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry ge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) ge.

(** `mbszero` zeroes the 16-byte object b, over glibc's `memset`. *)
Lemma libs_mbszero :
  hello_link ge o -> forall b, 0 < b -> b mod 16 = 0 -> b + 16 <= 2 ^ 48 ->
  D.fn_triple w0 ge (TAtom "mbszero") [WPtr (mkPtr b (Obj b))] (obj b (heap_req 4 8))
    (fun r => ⌜r = RetVoid⌝ ∗ obj b (heap_req 4 8))%I.
Proof.
  intros Hk b Hb0 Hb16 Hb48. exists mbszero_fn. split; [exact (hk_mbszero _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  assert (Ei : invocation mbszero_fn [WPtr (mkPtr b (Obj b))] = fr) by (unfold invocation; rewrite Hfr; reflexivity).
  replace (mkPtr b (Obj b)) with (mkPtr (b + 0) (Obj b)) in Ei by (f_equal; lia). subst fr.
  iIntros "Hb HK". iDestruct (obj16_split with "Hb") as "(Hl & Hx & Hx' & Hc & Hc')".
  destruct (hk_zmemset _ _ Hk) as [Hzf Hzs].
  rewrite mbszero_entry.
  iApply wp_enter; [exact find_z_start | reflexivity |]. iNext. cbn [b_insts b_jump z_start].
  iApply (MemFwdLogic.wp_call_glibc_memset w0 glibc_os_registry ge eq_refl Hzf Hzs _ _ _ _ _ _ _ _ _
    b (mkRegion b (b + 16) Heap Live) 0 (replicate 8 0) (replicate 8 CNone) 0 with "Hl Hx Hc");
    [reflexivity | exact (hk_memset _ _ Hk) | reflexivity | cbn; lia | cbn; lia |
     apply mod16_mod8'; exact Hb16 | reflexivity | lia | cbn; lia | reflexivity |].
  iNext. iIntros "Hl Hx Hc". cbn [length replicate].
  iApply wp_ret_void. iNext. iApply "HK". iSplit; [done|].
  iApply (obj16_join with "Hl Hx Hx' Hc Hc'").
Qed.

(** glibc's `strlen` of a string at any share returns its length. *)
Lemma libs_strlen :
  hello_link ge o -> forall dq p s,
  D.fn_triple w0 ge (TAtom "strlen") [WPtr p] (word_string dq p s)
    (fun r => ⌜r = Ret (WInt (Z.of_nat (length s)))⌝ ∗ word_string dq p s)%I.
Proof.
  intros Hk dq p s. exists glibc_strlen. split; [exact (hk_strlen _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  assert (E : call_frame glibc_strlen [WPtr p] =
              Some (mkFrame glibc_strlen [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None))) by reflexivity.
  rewrite E in Hfr. injection Hfr as <-. iIntros "Hs HK".
  iApply (StrlenWord.wp_glibc_strlen_ws glibc_os_registry (os_wi w0) ge with "Hs"). iIntros "Hs".
  iApply "HK". iSplit; [done | iExact "Hs"].
Qed.

(** glibc's `strncmp` of two read-only strings and 3 returns a `c: int`. *)
Lemma libs_strncmp :
  hello_link ge o -> forall p1 p2 s1 s2,
  D.fn_triple w0 ge (TAtom "strncmp") [WPtr p1; WPtr p2; WInt 3]
    (word_string DfracDiscarded p1 s1 ∗ word_string DfracDiscarded p2 s2)
    (fun r => ∃ k, ⌜r = Ret (WInt k) /\ 0 <= k < 2 ^ 32⌝)%I.
Proof.
  intros Hk p1 p2 s1 s2. exists glibc_strncmp. split; [exact (hk_strncmp _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  assert (E : call_frame glibc_strncmp [WPtr p1; WPtr p2; WInt 3] =
              Some (mkFrame glibc_strncmp [(TAtom "v4", WInt 3); (TAtom "v2", WPtr p2); (TAtom "v0", WPtr p1)] []
                      None (Enter (TAtom "start") None))) by reflexivity.
  rewrite E in Hfr. injection Hfr as <-. iIntros "[H1 H2] HK".
  iApply (StrncmpLogic.strncmp_entry glibc_os_registry (os_wi w0) ge DfracDiscarded DfracDiscarded p1 p2 s1 s2 3
    with "H1 H2"); [lia | right; reflexivity |]. iIntros "_ _".
  iApply "HK". iExists _. iPureIntro. split; [reflexivity | apply strcmp_res_range].
Qed.

(** glibc's `__errno_location` returns the pointer to `c: errno`. *)
Lemma libs_errno :
  hello_link ge o ->
  D.fn_triple w0 ge (TAtom "__errno_location") [] True
    (fun r => ⌜r = Ret (WPtr (mkPtr (ho_eb o) (Obj (ho_eb o))))⌝)%I.
Proof.
  intros Hk. exists errno_location_fn. split; [exact (hk_errno _ _ Hk)|].
  split; [eexists; reflexivity|]. intros fr Φ Hfr.
  assert (E : call_frame errno_location_fn [] =
              Some (mkFrame errno_location_fn [] [] None (Enter (TAtom "start") None))) by reflexivity.
  rewrite E in Hfr. injection Hfr as <-. iIntros "_ HK".
  iApply (LeavesLogic.wp_glibc_errno_location glibc_os_registry (os_wi w0) ge); [exact (hk_errno_at _ _ Hk)|].
  iApply "HK". done.
Qed.

End libs.
End HelloGlibcLibsStrOn.
