(** After glibc's long-option parser has searched the table for names
    that start with a word's name, it decides what to do next. A set of
    matching options, or a known ambiguity without a set, makes it report
    the word as ambiguous. Otherwise it goes on with the first match it
    found, or with no option at all. This file proves that decision. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The decision assigns these names. *)
Definition pend_names : list name := Eval vm_compute in
  List.map TAtom ["v232"; "v233"; "v237"; "v238"; "pr.12"; "pr.7"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongPfxEndOn (R : Runtime) (LG0 : LogicSig R).
(** The search module supplies the search, the set, the option table and the tactics. *)
Module LPL := GetoptLongPfxLoopOn R LG0.
Import LPL LPL.LPI LPL.LPI.LPT LPL.LPI.LPT.LPS LPL.LPI.LPT.LPS.LPA LPL.LPI.LPT.LPS.LPA.LPM LPL.LPI.LPT.LPS.LPA.LPM.LPC
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.

Section decide.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance end_stable : SafepointStable (os_wi w0) := LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance end_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The search has ended with the first match p and its index w, the
    flag a that says the word is ambiguous without a set, the flag m
    that says malloc made the set, and the set sp. When the set exists
    or a is set, the parser goes on to report the ambiguity. Otherwise
    there is no set to give back, m is 0, and the parser goes on with p
    and w at the block that handles a found option or none. *)
Lemma wp_pfx_end ks e n p w a m sp Φ :
  avoids ks pend_names = true ->
  lookup (TAtom "pr.8") e = Some (WPtr p) -> lookup (TAtom "pr.42") e = Some (WInt w) ->
  lookup (TAtom "pr.39") e = Some (WInt a) -> lookup (TAtom "pr.30") e = Some (WInt m) ->
  lookup (TAtom "pr.21") e = Some (WPtr sp) -> 0 <= w < 2 ^ 32 -> (a = 0 \/ a = 1) ->
  (m = 0 \/ (m = 1 /\ sp <> null)) ->
  amb_set n sp -∗
  ((∀ e', ⌜keeps ks e e' /\ sp = null /\ a = 0 /\ m = 0 /\ lookup (TAtom "pr.12") e' = Some (WInt w) /\
        lookup (TAtom "pr.7") e' = Some (WPtr p)⌝ -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None
        (Exec (TAtom "L87") (b_insts plo_blk87) (b_jump plo_blk87))) : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ (sp <> null \/ a = 1)⌝ -∗ amb_set n sp -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L228") (Some (TAtom "L235")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L101") (Some (TAtom "L98")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks H8 H42 H39 H30 H21 Hw Ha Hm. iIntros "Hs HK".
  st. st. st. iDestruct "Hs" as "[-> | (%sb & %sreg & %xs & %Hs & Hl & Hx)]".
  - unfold null; cbn [ptr_addr]. change (0 mod 2 ^ 64) with 0.
    iApply wp_branch; [vx | iNext]. close_br. st. st. st. st.
    assert (m = 0) as -> by (destruct Hm as [? | [_ ?]]; [assumption | contradiction]).
    destruct Ha as [-> | ->].
    + iApply wp_branch; [vx | iNext]. close_br. st. pcmp_fold "L87" plo_blk87. iDestruct "HK" as "[HK _]".
      rewrite (Z.mod_small w (2 ^ 32)) //. iApply "HK". iPureIntro. split; [xkeep|].
      repeat split; first [reflexivity | lk_prove].
    + iApply wp_branch; [vx | iNext]. close_br. iDestruct "HK" as "[_ HK]".
      iApply ("HK" with "[%] []"); [split; [xkeep | right; reflexivity] | by iLeft].
  - pose proof Hs as (-> & Hsk & Hsb & Hse & Hsr & Hlen). cbn [ptr_addr].
    rewrite (Z.mod_small sb (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
    rewrite (proj2 (Z.eqb_neq sb 0)); [|lia].
    iApply wp_branch; [vx | iNext]. close_br. st. iApply wp_branch; [vx | iNext]. close_br.
    iDestruct "HK" as "[_ HK]". iApply ("HK" with "[%] [Hl Hx]").
    { split; [xkeep | left; discriminate]. }
    iRight. iExists sb, sreg, xs. iFrame. done.
Qed.

End decide.
End GetoptLongPfxEndOn.
