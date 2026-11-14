(** glibc's long-option parser searches the whole table for options
    whose names start with a word's name. The module before this one
    proves one round of that search. This file proves the whole search
    safe by induction over the entries that are left. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongDiag GetoptLongExact GetoptLongPfxAlloc GetoptLongPfxCmp GetoptLongPfxIter GetoptLongPfxMark GetoptLongPfxSet GetoptLongPfxStep GetoptLongScan GetoptLongStore GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


(** The round module supplies one round of the search, the set, the option table and the tactics. *)
Import GetoptLongPfxIter GetoptLongPfxStep GetoptLongPfxSet GetoptLongPfxAlloc GetoptLongPfxMark GetoptLongPfxCmp GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section loop.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance loop_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance loop_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The search stands at entry k of the table lo. It holds the first
    match p and its index w, the flag a that says the word is ambiguous
    without a set, the flag m that says malloc made the set, and the set
    sp. It tests each entry from k on and stops at the table's null name
    with what it holds then. Every flag target stays the caller's, and
    the allocator keeps its state M. *)
Lemma wp_pfx_loop ks e (M : iProp Σ) (k : nat) p w a m sp cur s lo os F b r lonly pe Φ :
  avoids ks ploop_names = true -> avoids ks pcmp_names = true -> avoids ks pset_names = true ->
  avoids ks palloc_names = true -> avoids ks pmark_names = true ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  pfx_at e b s lonly pe (Z.of_nat (List.length os)) ->
  lookup (TAtom "pr.3") e = Some (WPtr (ptr_add lo (32 * Z.of_nat k))) ->
  lookup (TAtom "pr.13") e = Some (WInt (Z.of_nat k)) -> lookup (TAtom "pr.8") e = Some (WPtr p) ->
  lookup (TAtom "pr.42") e = Some (WInt w) -> lookup (TAtom "pr.39") e = Some (WInt a) ->
  lookup (TAtom "pr.30") e = Some (WInt m) -> lookup (TAtom "pr.21") e = Some (WPtr sp) ->
  (k <= List.length os)%nat -> pfx_first lo k p w -> (a = 0 \/ a = 1) -> (m = 0 \/ (m = 1 /\ sp <> null)) ->
  word_string DfracDiscarded cur s -∗ opt_table lo os -∗ live b r -∗ pcell b 32 cur -∗ flags_own F -∗
  amb_set (Z.of_nat (List.length os)) sp -∗ M -∗
  (∀ e' p' w' a' m' sp', ⌜keeps ks e e' /\ lookup (TAtom "pr.8") e' = Some (WPtr p') /\
      lookup (TAtom "pr.42") e' = Some (WInt w') /\ lookup (TAtom "pr.39") e' = Some (WInt a') /\
      lookup (TAtom "pr.30") e' = Some (WInt m') /\ lookup (TAtom "pr.21") e' = Some (WPtr sp') /\
      pfx_first lo (List.length os) p' w' /\ (a' = 0 \/ a' = 1) /\ (m' = 0 \/ (m' = 1 /\ sp' <> null))⌝ -∗
     live b r -∗ pcell b 32 cur -∗ flags_own F -∗ amb_set (Z.of_nat (List.length os)) sp' -∗ M -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L101") (Some (TAtom "L98")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L98") (b_insts plo_blk98) (b_jump plo_blk98))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksc Hkss Hksa Hksm Hcut Hmal Hset Hgn Hfl Hos Hpe Hb Hal Hend Hr.
  remember (List.length os - k)%nat as d eqn:Hd. revert e k p w a m sp Hd.
  induction d as [d IH] using (well_founded_induction lt_wf).
  intros e k p w a m sp Hd Hat H3 H13 H8 H42 H39 H30 H21 Hk Hf Ha Hm.
  iIntros "#Hws #Ht Hl Hcur HF Hs HM HK". iPoseProof "Ht" as "Ht0".
  iDestruct "Ht" as (tb treg) "(%Ht & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iApply (wp_pfx_iter w0 registry ge ks e M k p w a m sp cur s lo os F b r lonly pe
    with "Hws Ht0 Hl Hcur HF Hs HM");
    [exact Hks | exact Hksc | exact Hkss | exact Hksa | exact Hksm | exact Hcut | exact Hmal | exact Hset | exact Hgn
    | exact Hfl | exact Hos | exact Hpe | exact Hb | exact Hal | exact Hend | exact Hr | exact Hat | exact H3 | exact H13
    | exact H8 | exact H42 | exact H39 | exact H30 | exact H21 | exact Hk | exact Hf | exact Ha | exact Hm |].
  iSplit.
  { iIntros (e' (Hk' & Hkn & H8' & H42' & H39' & H30' & H21')) "Hl Hcur HF Hs HM". subst k.
    iApply ("HK" $! e' p w a m sp with "[%] Hl Hcur HF Hs HM"). repeat split; assumption. }
  iIntros (e2 p4 w40 a' m' sp' (Hk2 & Hlt & Hat2 & H32 & H132 & Hq4 & Hq40 & Hq31 & Hq22 & Hq14 & Hf2 & Ha2 & Hm2))
    "Hl Hcur HF Hs HM".
  pose proof Hat2 as (H12' & Hc0' & H48' & H10' & H14' & H90' & H9').
  cbn [b_insts b_jump plo_blk108]. step. step. step. step.
  match goal with |- context [put (TAtom "pr.3") (WPtr ?X) _] =>
    replace X with (ptr_add lo (32 * Z.of_nat (S k))) by
      (unfold ptr_add; cbn [ptr_addr ptr_cap]; f_equal; rewrite (Z.mod_small 32 (2 ^ 64)); [|lia];
       rewrite (Z.mod_small (ptr_addr lo + _) (2 ^ 64)); [|lia]; rewrite Z.mod_small; lia) end.
  match goal with |- context [put (TAtom "pr.13") (WInt ?X) _] =>
    replace X with (Z.of_nat (S k)) by (rewrite (Z.mod_small (Z.of_nat k) (2 ^ 32)); [|lia];
        rewrite (Z.mod_small 1 (2 ^ 32)); [|lia]; rewrite !(Z.mod_small (Z.of_nat k + 1) (2 ^ 32)); lia) end.
  assert (Hw40 : 0 <= w40 < 2 ^ 32) by (destruct Hf2 as [(_ & ->) | (j & Hj & _ & ->)]; lia).
  rewrite (Z.mod_small w40 (2 ^ 32)) // (Z.mod_small a' (2 ^ 32)); [|destruct Ha2 as [-> | ->]; lia].
  rewrite (Z.mod_small m' (2 ^ 32)); [|destruct Hm2 as [-> | [-> _]]; lia].
  pcmp_fold "L98" plo_blk98.
  iApply (IH (List.length os - S k)%nat ltac:(lia) _ (S k) p4 w40 a' m' sp' eq_refl with "Hws Ht0 Hl Hcur HF Hs HM [HK]");
    [unfold pfx_at; repeat split; lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove
    | lk_prove | lia | exact Hf2 | exact Ha2 | exact Hm2 |].
  iIntros (e' p' w' a2 m2 sp2 (Hk' & Hrest)) "Hl Hcur HF Hs HM".
  iApply ("HK" $! e' p' w' a2 m2 sp2 with "[%] Hl Hcur HF Hs HM").
  split; [|exact Hrest]. eapply keeps_trans; [exact Hk2|]. eapply keeps_trans; [|exact Hk']. xkeep. Qed.

End loop.
