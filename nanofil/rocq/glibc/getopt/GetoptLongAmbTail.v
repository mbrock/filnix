(** After glibc's long-option parser has reported an ambiguous word, it
    gives back the set of matching options when malloc made it. Then it
    steps the index past the word, moves its cursor to the end of the
    word, clears the bad option and answers '?'. This file proves those
    last steps safe. The parser frees only the set that malloc made, and
    it writes only its own private fields. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The last steps assign these names. *)
Definition atail_names : list name := Eval vm_compute in
  List.map TAtom ["v311"; "chk29"; "v312"; "v315"; "v316"; "v317"; "chk31"; "chk32"; "v319"; "v320"; "chk33";
    "v322"; "chk34"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongAmbTailOn (R : Runtime) (LG0 : LogicSig R).
(** The decision module supplies the set, the option table and the tactics. *)
Module LPE := GetoptLongPfxEndOn R LG0.
Import LPE LPE.LPL LPE.LPL.LPI LPE.LPL.LPI.LPT LPE.LPL.LPI.LPT.LPS LPE.LPL.LPI.LPT.LPS.LPA LPE.LPL.LPI.LPT.LPS.LPA.LPM
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.

Section tail.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance atail_stable : SafepointStable (os_wi w0) := LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance atail_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** An ambiguous option leaves behind memory that the parser must hand
    back. This rule says what freeing it costs: the caller gives up the
    heap object the argument points at, and the rest of the code runs
    on. The stdio proofs state free the same way. Until a caller proves
    it, the rule stays an open premise. *)
Definition getopt_free_rule : Prop := forall f e ls l v rest j b reg Φ,
  arg_x ge e (Arg P v) = Some (WPtr (mkPtr b (Obj b))) -> r_kind reg = Heap -> 0 < b < 2 ^ 64 ->
  ⊢ live b reg -∗ ▷ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }} -∗
    WP (ERun (mkFrame f e ls None (Exec l (Call CVoid (Global (TAtom "free")) [Arg P v] :: rest) j)) : gexpr)
      {{ Φ }}.

(** After it reports an ambiguous option, the parser cleans up and
    skips the word. It frees the set of candidates when malloc made it,
    which the flag m records. It then moves the cursor to the end of
    the word, steps to the next word, clears the bad option and
    answers '?'. *)
Lemma wp_amb_tail ks e fr n m sp cur s i oo b r Φ :
  avoids ks atail_names = true -> getopt_free_rule ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  lookup (TAtom "pr.30") e = Some (WInt m) -> lookup (TAtom "pr.21") e = Some (WPtr sp) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  (m = 0 \/ (m = 1 /\ sp <> null)) -> 0 <= i < 2 ^ 31 - 1 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  word_string DfracDiscarded cur s -∗ amb_set n sp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗
     live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 0 -∗ pcell b 32 (ptr_add cur (Z.of_nat (List.length s))) -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L307") [] (JRet (Const 63)))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L241") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hfree Hgl H30 H21 H12 Hc0 Hm Hi Hb Hal Hend Hr.
  iIntros "#Hws Hs Hl [%Hi0 Hib] [%Hoo Hoob] Hcur HK".
  iDestruct (argv_str_cap with "Hws") as (rc) "[#Hcapc %Hc0']".
  iDestruct (ws_shape with "Hws") as %(Hch & Hcp & Hce).
  iAssert (∀ e1 fr1, ⌜keeps ks e e1 /\ lookup (TAtom "v12") e1 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk0") e1 = Some (WPtr (mkPtr (b + 32) (Obj b)))⌝ -∗ live b r -∗ pcell b 32 cur -∗
    WP (ERun (mkFrame glibc_process_long_option e1 [] None (Enter (TAtom "L307") (Some fr1))) : gexpr) {{ Φ }})%I
    with "[Hib Hoob HK]" as "HL307".
  { iIntros (e1 fr1 (Hk1 & H12' & Hc0'')) "Hl Hcur".
    en. st. chk "Hl".
    iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapc"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
    iNext. iIntros "Hl Hcur _".
    iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapc"); [reflexivity | vx | left; reflexivity | arith | arith | lia |].
    iNext. iIntros "Hl Hcur _".
    iApply (SW.wp_call_glibc_strlen registry (os_wi w0) ge with "Hws"); [vx | exact Hgl | reflexivity |].
    iNext. iIntros "_". cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. st. chk "Hl".
    iApply (wp_raw_store_pointer with "Hl Hcur"); [vx | vx | reflexivity | arith | arith | wi_store |].
    iNext. iIntros "Hl Hcur". chk "Hl". load_int "Hl Hib". st. norm. chk "Hl".
    iApply (wp_raw_store_w with "Hl Hib"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hib". st. chk "Hl".
    iApply (wp_raw_store_w with "Hl Hoob"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hoob".
    rewrite (Z.mod_small (i + 1) (2 ^ 32)); [|lia]. change (0 mod 2 ^ 64) with 0.
    match goal with |- context [pcell b 32 {| ptr_addr := ?X; ptr_cap := ptr_cap cur |}] =>
      replace X with (ptr_addr cur + Z.of_nat (List.length s)) by (rewrite ?Z.mod_small; lia) end.
    iApply ("HK" with "[%] Hl [Hib] [Hoob] Hcur");
      [eapply keeps_trans; [exact Hk1|]; xkeep | iSplit; [iPureIntro; lia | iExact "Hib"]
      | iSplit; [iPureIntro; lia | iExact "Hoob"]]. }
  en. iApply wp_branch; [vx | iNext].
  destruct Hm as [-> | [-> Hsn]]; close_br.
  { iApply ("HL307" with "[%] Hl Hcur"). split; [xkeep|]. split; lk_prove. }
  iDestruct "Hs" as "[-> | (%sb & %sreg & %xs & %Hs & Hsl & _)]"; [contradiction|].
  destruct Hs as (-> & Hsk & Hsb & Hse & Hsr & Hlen).
  en. iApply (Hfree with "Hsl"); [vx | exact Hsk | lia |]. iNext. st.
  iApply ("HL307" with "[%] Hl Hcur"). split; [xkeep|]. split; lk_prove.
Qed.

End tail.
End GetoptLongAmbTailOn.
