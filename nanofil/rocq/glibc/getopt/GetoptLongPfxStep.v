(** This file proves one step of glibc's search for long options whose
    names start with a word's name. The step handles an entry that
    matches after a first match was already found. The parser compares
    the two entries, records an ambiguity when they differ, and then
    stands ready to move on to the next entry. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrchrCode StrchrnulLogic StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg GetoptLongUnrec GetoptLongMissOnly
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongDiag GetoptLongExact GetoptLongPfxAlloc GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxSet GetoptLongScan GetoptLongStore GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The search assigns these names in its own blocks. *)
Definition ploop_names : list name := Eval vm_compute in
  List.map TAtom ["chk8"; "v103"; "v104"; "v105"; "v110"; "v112"; "chk10"; "v113"; "v115"; "v116"; "v121"; "v123";
    "pr.40"; "pr.31"; "pr.22"; "pr.14"; "pr.4"; "v225"; "v227"; "pr.42"; "pr.39"; "pr.30"; "pr.21"; "pr.13";
    "pr.8"; "pr.3"]%string.

(** The search keeps these names across the steps that it calls. *)
Definition ploop_keys : list name := Eval vm_compute in
  List.map TAtom ["pr.42"; "pr.8"; "pr.3"; "pr.13"; "pr.9"; "pr.39"; "pr.30"; "pr.21"; "chk8"; "v12"; "chk0"; "v48";
    "v10"; "v14"; "v90"]%string.

(** The search steps to the next entry in this block. *)
Definition plo_blk108 : block := Eval vm_compute in plo_blk "L108".

(** The search reads these values that do not change: the parser's
    private fields b, the length of the word's name in s, the long-only
    mode, whether the parser prints errors, a zero, and the count n of
    the table's entries. *)
Definition pfx_at (e : env) (b : Z) (s : list Z) (lonly pe n : Z) : Prop :=
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) /\
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
  lookup (TAtom "v48") e = Some (WInt (Z.of_nat (eq_len s))) /\ lookup (TAtom "v10") e = Some (WInt lonly) /\
  lookup (TAtom "v14") e = Some (WInt pe) /\ lookup (TAtom "v90") e = Some (WInt 0) /\
  lookup (TAtom "pr.9") e = Some (WInt n).

(** Before entry k, the search has found no option whose name starts
    with the word's name, or it found the first one at an index j below
    k. It holds the first one's pointer p and its index w. *)
Definition pfx_first (lo : ptr) (k : nat) (p : ptr) (w : Z) : Prop :=
  (p = null /\ w = 4294967295) \/ (exists j, (j < k)%nat /\ p = ptr_add lo (32 * Z.of_nat j) /\ w = Z.of_nat j).

(** A first match found before entry k was also found before k + 1. *)
Lemma pfx_first_S lo k p w : pfx_first lo k p w -> pfx_first lo (S k) p w.
Proof. intros [H | (j & Hj & H)]; [left; exact H | right; exists j; split; [lia | exact H]]. Qed.


(** The set module supplies the comparison, the set, the option table and the tactics. *)
Import GetoptLongPfxSet GetoptLongPfxAlloc GetoptLongPfxMark GetoptLongPfxCmp GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic chains the kept names through assignments and the steps that keep them. *)
Ltac ploop_kc := repeat (match goal with H : avoids _ ?Wl = true |- keeps _ _ (put _ _ _) =>
    apply keeps_put_avoid with (W := Wl); [vm_compute; reflexivity | exact H |] end);
  first [apply keeps_refl | assumption |
    lazymatch goal with H : keeps ?ks ?a ?c |- keeps ?ks ?x ?c => eapply keeps_trans; [|exact H]; ploop_kc end].

(** This tactic takes a lookup through assignments and through the steps that keep the name. *)
Ltac ploop_via := first
  [ apply Symbolic.lookup_after_put_same
  | eapply lookup_put_miss; [vm_compute; reflexivity | ploop_via]
  | eassumption
  | lazymatch goal with H : keeps ploop_keys ?a ?c |- lookup ?k ?c = _ =>
      rewrite (keeps_in _ _ _ _ H); [ploop_via | unfold ploop_keys; cbn [In]; repeat first [left; reflexivity | right]] end ].

(** This tactic closes the range of a flag or an index below 2^32. *)
Ltac ploop_rng := first
  [ match goal with H : ?x = 0 \/ ?x = 1 |- 0 <= ?x < _ => destruct H as [-> | ->]; lia end
  | match goal with H : ?x = 0 \/ (?x = 1 /\ _) |- 0 <= ?x < _ => destruct H as [-> | [-> _]]; lia end
  | lia ].

(** This tactic drops the reduction below 2^32 of a value already in range. *)
Ltac ploop_small := repeat match goal with |- context [?x mod 2 ^ 32] =>
  rewrite (Z.mod_small x (2 ^ 32)); [|ploop_rng] end.

Section step.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance step_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance step_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The search has found the entry k whose name starts with the word's
    name. When it has no first match p yet, k becomes the first match.
    Otherwise it compares the two entries and records an ambiguity as
    needed. Then it stands at the step to the next entry, with the first
    match, the two flags a' and m', and the set sp'.
    The flag targets stay the caller's, and the allocator keeps its
    state M. *)
Lemma wp_pfx_step ks e (M : iProp Σ) k lo os F b s lonly pe p w a m sp Φ :
  avoids ks ploop_names = true -> avoids ks pcmp_names = true -> avoids ks pset_names = true ->
  avoids ks palloc_names = true -> avoids ks pmark_names = true ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z -> 0 <= pe < 2 ^ 32 ->
  pfx_at e b s lonly pe (Z.of_nat (List.length os)) ->
  lookup (TAtom "pr.3") e = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) ->
  lookup (TAtom "chk8") e = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) ->
  lookup (TAtom "pr.13") e = Some (WInt (Z.of_nat k)) ->
  lookup (TAtom "pr.8") e = Some (WPtr p) ->
  lookup (TAtom "pr.42") e = Some (WInt w) -> lookup (TAtom "pr.39") e = Some (WInt a) ->
  lookup (TAtom "pr.30") e = Some (WInt m) -> lookup (TAtom "pr.21") e = Some (WPtr sp) ->
  pfx_first lo k p w -> (k < List.length os)%nat -> (a = 0 \/ a = 1) -> (m = 0 \/ (m = 1 /\ sp <> null)) ->
  opt_table lo os -∗ flags_own F -∗ amb_set (Z.of_nat (List.length os)) sp -∗ M -∗
  (∀ e2 p4 w40 a' m' sp', ⌜keeps ks e e2 /\ pfx_at e2 b s lonly pe (Z.of_nat (List.length os)) /\
      lookup (TAtom "pr.3") e2 = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) /\
      lookup (TAtom "pr.13") e2 = Some (WInt (Z.of_nat k)) /\
      lookup (TAtom "pr.4") e2 = Some (WPtr p4) /\
      lookup (TAtom "pr.40") e2 = Some (WInt w40) /\ lookup (TAtom "pr.31") e2 = Some (WInt a') /\
      lookup (TAtom "pr.22") e2 = Some (WInt m') /\ lookup (TAtom "pr.14") e2 = Some (WPtr sp') /\
      pfx_first lo (S k) p4 w40 /\ (a' = 0 \/ a' = 1) /\ (m' = 0 \/ (m' = 1 /\ sp' <> null))⌝ -∗
     flags_own F -∗ amb_set (Z.of_nat (List.length os)) sp' -∗ M -∗
     WP (ERun (mkFrame glibc_process_long_option e2 [] None
       (Exec (TAtom "L108") (b_insts plo_blk108) (b_jump plo_blk108))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L106") (Some (TAtom "L99")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks Hksc Hkss Hksa Hksm Hcut Hmal Hset Hfl Hos Hpe Hat H3 Hc8 H13 H8 H42 H39 H30 H21 Hf Hk Ha Hm.
  assert (Hks2 : avoids (ploop_keys ++ ks) pcmp_names && avoids (ploop_keys ++ ks) pset_names &&
    avoids (ploop_keys ++ ks) palloc_names && avoids (ploop_keys ++ ks) pmark_names = true)
    by (rewrite !avoids_app_l Hksc Hkss Hksa Hksm; reflexivity).
  apply andb_true_iff in Hks2 as [Hks2 Hkm2]. apply andb_true_iff in Hks2 as [Hks2 Hka2].
  apply andb_true_iff in Hks2 as [Hkc2 Hks2].
  pose proof Hat as (H12 & Hc0 & H48 & H10 & H14 & H90 & H9).
  iIntros "#Ht0 HF Hs HM HK". iPoseProof "Ht0" as "Ht".
  iDestruct "Ht" as (tb treg) "(%Ht & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  step. step. step.
  destruct Hf as [(-> & ->) | (j & Hj & -> & ->)].
  { unfold null; cbn [ptr_addr]. iApply wp_branch; [vx | iNext]. close_br.
    step. ploop_small. pcmp_fold "L108" plo_blk108. iApply ("HK" with "[%] HF Hs HM").
    split; [xkeep|]. split; [unfold pfx_at; repeat split; lk_prove|].
    repeat split; try lk_prove; try assumption. right. exists k. split; [lia | split; reflexivity]. }
  destruct (lookup_lt_is_Some_2 os j ltac:(lia)) as [x Hx]. destruct (lookup_lt_is_Some_2 os k Hk) as [y Hy].
  unfold ptr_add at 1; cbn [ptr_addr].
  rewrite (Z.mod_small (ptr_addr lo + 32 * Z.of_nat j) (2 ^ 64)); [|lia].
  rewrite (proj2 (Z.eqb_neq (ptr_addr lo + 32 * Z.of_nat j) 0)); [|lia].
  iApply wp_branch; [vx | iNext]. close_br.
  iApply (wp_long_pfx_cmp w0 registry ge (ploop_keys ++ ks)%list _ lo os j x k y lonly F with "Ht0 HF");
    [exact Hkc2 | lk_prove | lk_prove | lk_prove | lk_prove | exact Hx | exact Hy | exact Hos
    | exact (Forall_lookup_1 _ _ _ _ Hfl Hx) | exact (Forall_lookup_1 _ _ _ _ Hfl Hy) |].
  iSplit.
  + iIntros (e' Hk') "HF". apply keeps_app in Hk' as [Hkt Hk'].
    iApply (wp_pfx_set w0 registry ge (ploop_keys ++ ks)%list _ M (Z.of_nat (List.length os)) j k a m sp pe
      with "Hs HM");
      [exact Hks2 | exact Hka2 | exact Hkm2 | exact Hcut | exact Hmal | exact Hset | ploop_via | ploop_via
      | ploop_via | ploop_via | ploop_via | ploop_via | ploop_via | ploop_via | lia | lia | lia | exact Ha | exact Hm
      | exact Hpe |].
    iIntros (e'' P a' m' sp' (Hk'' & Hout & Ha' & Hm')) "Hs HM". apply keeps_app in Hk'' as [Hkt' Hk''].
    assert (Hq42 : lookup (TAtom "pr.42") e'' = Some (WInt (Z.of_nat j))) by ploop_via.
    assert (Hq8 : lookup (TAtom "pr.8") e'' = Some (WPtr (ptr_add lo (32 * Z.of_nat j)))) by ploop_via.
    assert (Hat'' : pfx_at e'' b s lonly pe (Z.of_nat (List.length os))) by (unfold pfx_at; repeat split; ploop_via).
    assert (Hq3 : lookup (TAtom "pr.3") e'' = Some (WPtr (ptr_add lo (32 * Z.of_nat k)))) by ploop_via.
    assert (Hq13 : lookup (TAtom "pr.13") e'' = Some (WInt (Z.of_nat k))) by ploop_via.
    assert (Hke : keeps ks e e'') by ploop_kc.
    clear Hkt Hkt' Hk' Hk''. pose proof Hat'' as (Hs12 & Hs0 & Hs48 & Hs10 & Hs14 & Hs90 & Hs9).
    destruct Hout as [(-> & H39' & H30' & H21') | ([-> | ->] & H35 & H26 & H18)].
    * step. ploop_small. pcmp_fold "L108" plo_blk108. iApply ("HK" with "[%] HF Hs HM").
      split; [xkeep|]. split; [unfold pfx_at; repeat split; lk_prove|].
      repeat split; first [lk_prove | assumption | right; exists j; split; [lia | split; reflexivity]].
    * step. ploop_small. pcmp_fold "L108" plo_blk108. iApply ("HK" with "[%] HF Hs HM").
      split; [xkeep|]. split; [unfold pfx_at; repeat split; lk_prove|].
      repeat split; first [lk_prove | assumption | right; exists j; split; [lia | split; reflexivity]].
    * step. ploop_small. pcmp_fold "L108" plo_blk108. iApply ("HK" with "[%] HF Hs HM").
      split; [xkeep|]. split; [unfold pfx_at; repeat split; lk_prove|].
      repeat split; first [lk_prove | assumption | right; exists j; split; [lia | split; reflexivity]].
  + iIntros (e' Hk') "HF". apply keeps_app in Hk' as [Hkt Hk'].
    assert (Hq42 : lookup (TAtom "pr.42") e' = Some (WInt (Z.of_nat j))) by ploop_via.
    assert (Hq8 : lookup (TAtom "pr.8") e' = Some (WPtr (ptr_add lo (32 * Z.of_nat j)))) by ploop_via.
    assert (Hq39 : lookup (TAtom "pr.39") e' = Some (WInt a)) by ploop_via.
    assert (Hq30 : lookup (TAtom "pr.30") e' = Some (WInt m)) by ploop_via.
    assert (Hq21 : lookup (TAtom "pr.21") e' = Some (WPtr sp)) by ploop_via.
    step. ploop_small. pcmp_fold "L108" plo_blk108. iApply ("HK" with "[%] HF Hs HM").
    split; [ploop_kc|]. split; [unfold pfx_at; repeat split; ploop_via|].
    repeat split; first [ploop_via | assumption | right; exists j; split; [lia | split; reflexivity]].
Qed.

End step.
