(** A word on the command line can name two long options at once, as
    "--ver" names both "--verbose" and "--version". glibc's parser then
    reports the word as ambiguous. Before the report it remembers which
    options the word matched, in a set with one byte per option. This
    file proves safe the step that records one more matching option. The
    parser may skip the step, mark the option in the set it has, or make
    the set first. It writes only bytes of a set that it owns. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongDiag GetoptLongExact GetoptLongPfxAlloc GetoptLongPfxCmp GetoptLongPfxMark GetoptLongScan GetoptLongStore GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The choice assigns these names. *)
Definition pset_names : list name := Eval vm_compute in
  List.map TAtom ["v169"; "v174"; "v179"; "v181"; "pr.35"; "pr.26"; "pr.18"]%string.

(** The next step of the search needs to know what the parser holds.
    It holds a flag that says the word is ambiguous without a set, a
    flag that says malloc made the set, and the set. This relation says
    where it holds them after the choice, by the block P it came from. *)
Definition pfx_out (P : name) (e : env) (a m : Z) (s : ptr) : Prop :=
  (P = TAtom "L126" /\ lookup (TAtom "pr.39") e = Some (WInt a) /\ lookup (TAtom "pr.30") e = Some (WInt m) /\
     lookup (TAtom "pr.21") e = Some (WPtr s)) \/
  ((P = TAtom "L214" \/ P = TAtom "L172") /\ lookup (TAtom "pr.35") e = Some (WInt a) /\
     lookup (TAtom "pr.26") e = Some (WInt m) /\ lookup (TAtom "pr.18") e = Some (WPtr s)).

(** The choice starts in this block. *)
Definition plo_blk126 : block := Eval vm_compute in plo_blk "L126".


(** The allocation module supplies the callee rules, the set, the option table and the tactics. *)
Import GetoptLongPfxAlloc GetoptLongPfxMark GetoptLongPfxCmp GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Section set.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance set_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance set_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser has found the entry k ambiguous with the first match j.
    It holds the flag a, which says the word is ambiguous without a set,
    the flag m, which says the set came from malloc, and the set s of n
    bytes. It records the ambiguity as described above and goes on to
    the next entry. The flags stay 0 or 1, and m is 1 only with a set. *)
Lemma wp_pfx_set ks e (M : iProp Σ) n j k a m s pe Φ :
  avoids ks pset_names = true -> avoids ks palloc_names = true -> avoids ks pmark_names = true ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  lookup (TAtom "pr.9") e = Some (WInt n) -> lookup (TAtom "pr.39") e = Some (WInt a) ->
  lookup (TAtom "pr.30") e = Some (WInt m) -> lookup (TAtom "pr.21") e = Some (WPtr s) ->
  lookup (TAtom "pr.42") e = Some (WInt (Z.of_nat j)) -> lookup (TAtom "pr.13") e = Some (WInt (Z.of_nat k)) ->
  lookup (TAtom "v14") e = Some (WInt pe) -> lookup (TAtom "v90") e = Some (WInt 0) ->
  Z.of_nat j < n -> Z.of_nat k < n -> n < 2 ^ 31 -> (a = 0 \/ a = 1) -> (m = 0 \/ (m = 1 /\ s <> null)) ->
  0 <= pe < 2 ^ 32 ->
  amb_set n s -∗ M -∗
  (∀ e' P a' m' s', ⌜keeps ks e e' /\ pfx_out P e' a' m' s' /\ (a' = 0 \/ a' = 1) /\ (m' = 0 \/ (m' = 1 /\ s' <> null))⌝ -∗
     amb_set n s' -∗ M -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L108") (Some P))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L126") (Some (TAtom "L155")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks Hksa Hksm Hcut Hmal Hset H9 H39 H30 H21 H42 H13 H14 H90 Hj Hk Hn Ha Hm Hpe.
  iIntros "Hs HM HK".
  assert (Ha32 : 0 <= a < 2 ^ 32) by (destruct Ha as [-> | ->]; lia).
  assert (Hm32 : 0 <= m < 2 ^ 32) by (destruct Hm as [-> | [-> _]]; lia).
  assert (Hksk : avoids (palloc_keys ++ ks) pmark_names = true) by (rewrite avoids_app_l Hksm; reflexivity).
  step. step. rewrite (Z.mod_small a (2 ^ 32)) //. change (0 mod 2 ^ 32) with 0.
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec a 0) as [-> | Ha0]; repeat close_br.
  2: { iApply ("HK" with "[%] Hs HM"). split; [xkeep|]. split; [left; repeat split; lk_prove | tauto]. }
  step. step. rewrite (Z.mod_small pe (2 ^ 32)) //. try change (0 mod 2 ^ 32) with 0.
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec pe 0) as [-> | Hpe0]; repeat close_br.
  - step. rewrite (Z.mod_small m (2 ^ 32)) //. pcmp_fold "L172" plo_blk172.
    iApply (wp_pfx_mark w0 registry ge (palloc_keys ++ ks)%list _ n s k with "Hs");
      [exact Hksk | lk_prove | lk_prove | lia | lia |].
    iIntros (e' P (Hk' & HP)) "Hs". apply keeps_app in Hk' as [Hkt Hk'].
    iApply ("HK" $! e' P 1 m s with "[%] Hs HM").
    split; [eapply keeps_trans; [|exact Hk']; xkeep|].
    split; [right; split; [exact HP|]; repeat split; viakeep Hkt | tauto].
  - step. step. step. iDestruct "Hs" as "[-> | (%sb & %sreg & %xs & %Hs & Hl & Hx)]".
    + unfold null; cbn [ptr_addr]. change (0 mod 2 ^ 64) with 0. iApply wp_branch; [vx | iNext]. close_br.
      assert (m = 0) as -> by (destruct Hm as [? | [_ ?]]; [assumption | contradiction]).
      iApply (wp_pfx_alloc w0 registry ge ks _ M n j k with "HM");
        [exact Hksa | exact Hksm | exact Hcut | exact Hmal | exact Hset | lk_prove | lk_prove | lk_prove | lk_prove
        | lk_prove | lk_prove | lia | lia | lia |].
      iIntros (e' P a' m' s' (Hk' & HP & H35 & H26 & H18 & Ha' & Hm')) "Hs HM".
      iApply ("HK" $! e' P a' m' s' with "[%] Hs HM").
      split; [eapply keeps_trans; [|exact Hk']; xkeep|]. split; [right; repeat split; assumption | tauto].
    + pose proof Hs as (-> & Hsk & Hsb & Hse & Hsr & Hlen). cbn [ptr_addr].
      rewrite (Z.mod_small sb (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
      rewrite (proj2 (Z.eqb_neq sb 0)); [|lia]. iApply wp_branch; [vx | iNext]. close_br. step.
      rewrite (Z.mod_small m (2 ^ 32)) //. pcmp_fold "L172" plo_blk172.
      iApply (wp_pfx_mark w0 registry ge (palloc_keys ++ ks)%list _ n (mkPtr sb (Obj sb)) k with "[Hl Hx]");
        [exact Hksk | lk_prove | lk_prove | lia | lia | iRight; iExists sb, sreg, xs; iFrame; done |].
      iIntros (e' P (Hk' & HP)) "Hs". apply keeps_app in Hk' as [Hkt Hk'].
      iApply ("HK" $! e' P 0 m (mkPtr sb (Obj sb)) with "[%] Hs HM").
      split; [eapply keeps_trans; [|exact Hk']; xkeep|].
      split; [right; split; [exact HP|]; repeat split; viakeep Hkt | tauto].
Qed.

End set.
