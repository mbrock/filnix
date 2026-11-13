(** When glibc's long-option parser finds several options whose names
    start with a word's name, it reports the word as ambiguous when its
    caller lets it print errors. It names the word and, when it built a
    set of the candidates, lists them. Then it gives the set back and
    skips the word. This file proves the whole report safe. The parser
    writes the report only through the rule that its caller supplies,
    and it frees only the set that malloc made. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail GetoptLongAmbPrint GetoptLongAmbItem GetoptLongAmbList
  GetoptLongAmbHead GetoptLongAmbPoss.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The listing and the last steps read these names after the first line. *)
Definition arep_keys : list name := Eval vm_compute in
  List.map TAtom ["pr.30"; "pr.21"; "v12"; "chk0"; "v6"; "v16"; "pr.9"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongAmbRepOn (R : Runtime) (LG0 : LogicSig R).
(** The heading modules supply the report's first line, the listing, the last steps and the set. *)
Module LAO := GetoptLongAmbPossOn R LG0.
Import LAO LAO.LAH LAO.LAH.LAL LAO.LAH.LAL.LAI LAO.LAH.LAL.LAI.LAP LAO.LAH.LAL.LAI.LAP.LAT LAO.LAH.LAL.LAI.LAP.LAT.LPE LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.

Section rep.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance arep_stable : SafepointStable (os_wi w0) := LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance arep_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic takes a lookup through assignments and through the steps that keep the name. *)
Ltac arep_lk := first
  [ apply Symbolic.lookup_after_put_same
  | eapply lookup_put_miss; [vm_compute; reflexivity | arep_lk]
  | eassumption
  | lazymatch goal with H : keeps arep_keys ?a ?c |- lookup ?k ?c = _ =>
      rewrite (keeps_in _ _ _ _ H); [arep_lk | unfold arep_keys; cbn [In]; repeat first [left; reflexivity | right]] end ].

(** The parser reports a word that names more than one option. When it
    may print errors, it first names the word. If it built a set of the
    candidates, it lists them too. Then it frees the set if malloc made
    it, and it skips the word. Last, it clears the bad option and
    answers '?'. The vector stays intact, and G comes back. *)
Lemma wp_amb_report ks e (G : iProp Σ) T fp dom se sereg f138 f139 f140 f141 av ar ps lo os pfx pxs
    cur s pe a m sp i oo b r Φ :
  avoids ks arep_names = true -> avoids ks alist_names = true -> avoids ks atail_names = true ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v14") e = Some (WInt pe) ->
  lookup (TAtom "v16") e = Some (WPtr pfx) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "pr.9") e = Some (WInt (Z.of_nat (List.length os))) ->
  lookup (TAtom "pr.39") e = Some (WInt a) -> lookup (TAtom "pr.30") e = Some (WInt m) ->
  lookup (TAtom "pr.21") e = Some (WPtr sp) ->
  0 <= pe < 2 ^ 32 -> (a = 0 \/ a = 1) -> (sp <> null \/ a = 1) -> (m = 0 \/ (m = 1 /\ sp <> null)) ->
  (List.length os < 2 ^ 31)%Z -> 0 <= i < 2 ^ 31 - 1 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗ amb_set (Z.of_nat (List.length os)) sp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗
     live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 0 -∗ pcell b 32 (ptr_add cur (Z.of_nat (List.length s))) -∗
     live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L307") [] (JRet (Const 63)))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L228") (Some (TAtom "L235")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks Hksl Hkst Hrule Hfree Hgl Hse H138 H139 H140 H141 H2 H6 H12 H14 H16 Hc0 H9 H39 H30 H21
    Hpe Ha Hsa Hm Hos Hi Hb Hal Hend Hr Hav Hala Hda Hra Hps Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hpfx #Hwc #Hsl #Hsc Hs Hl Hib Hoob Hcur Ha Hcl #Hargs HG HK".
  iAssert (∀ e1 fr1, ⌜keeps ks e e1 /\ lookup (TAtom "pr.30") e1 = Some (WInt m) /\
      lookup (TAtom "pr.21") e1 = Some (WPtr sp) /\ lookup (TAtom "v12") e1 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk0") e1 = Some (WPtr (mkPtr (b + 32) (Obj b)))⌝ -∗
    amb_set (Z.of_nat (List.length os)) sp -∗ live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
    live av ar -∗ argv_cells av ps -∗ G -∗
    WP (ERun (mkFrame glibc_process_long_option e1 [] None (Enter (TAtom "L241") (Some fr1))) : gexpr) {{ Φ }})%I
    with "[HK]" as "HL241".
  { iIntros (e1 fr1 (Hk1 & H30' & H21' & H12' & Hc0'')) "Hs Hl Hib Hoob Hcur Ha Hcl HG".
    iApply (wp_amb_tail w0 registry ge ks e1 fr1 _ m sp cur s i oo b r with "Hwc Hs Hl Hib Hoob Hcur");
      [exact Hkst | exact Hfree | exact Hgl | exact H30' | exact H21' | exact H12' | exact Hc0'' | exact Hm | exact Hi
      | exact Hb | exact Hal | exact Hend | exact Hr |].
    iIntros (e' Hk') "Hl Hib Hoob Hcur". iApply ("HK" with "[%] Hl Hib Hoob Hcur Ha Hcl HG").
    eapply keeps_trans; [exact Hk1 | exact Hk']. }
  en. iApply wp_branch; [vx | iNext]. rewrite (Z.mod_small pe (2 ^ 32)); [|lia].
  destruct (Z.eqb_spec pe 0) as [Ep | Ep]; cbn [edge_label].
  { iApply ("HL241" with "[%] Hs Hl Hib Hoob Hcur Ha Hcl HG"). split; [xkeep|]. repeat split; lk_prove. }
  en. iApply wp_branch; [vx | iNext]. destruct Ha as [-> | ->]; close_br.
  - destruct Hsa as [Hsn | ?]; [|lia].
    iApply (wp_amb_head139 w0 registry ge (arep_keys ++ ks)%list e _ G T fp dom se sereg f139 av ar ps pfx pxs cur s b r
      with "Hpfx Hwc Hsl Hsc Hl Hcur Ha Hcl Hargs HG");
      [rewrite avoids_app_l Hks; reflexivity | exact Hrule | exact Hse | exact H139 | lk_prove | lk_prove | lk_prove | lk_prove | exact Hb | exact Hal
      | exact Hend | exact Hr | exact Hav | exact Hala | exact Hda | exact Hra | exact Hps | exact Hse0 | exact Hsea
      | exact Hsee | exact Hser |].
    iIntros (e2 Hk2) "Hl Hcur Ha Hcl HG". apply keeps_app in Hk2 as [Hkt2 Hk2]. st. pcmp_fold "L273" plo_blk273.
    iDestruct "Hs" as "[-> | (%sb & %sreg & %xs & %Hs & Hsetl & Hx)]"; [contradiction|].
    destruct Hs as (-> & Hsk & Hsb & Hsend & Hsr & Hlen).
    iApply (wp_amb_list w0 registry ge (arep_keys ++ ks)%list _ G T fp dom se sereg f140 f141 lo os pfx pxs 0 sb sreg xs
      with "Ht Hpfx Hsl Hsc Hsetl Hx HG");
      [rewrite avoids_app_l Hksl; reflexivity | exact Hrule | exact Hse | exact H140 | exact H141 | arep_lk | arep_lk
      | arep_lk | arep_lk | arep_lk | lia | exact Hos | lia | exact Hsb | exact Hsend | exact Hsr | exact Hse0
      | exact Hsea | exact Hsee | exact Hser |].
    iIntros (e3 Hk3) "Hsetl Hx HG". apply keeps_app in Hk3 as [Hkt Hk3].
    iApply ("HL241" with "[%] [Hsetl Hx] Hl Hib Hoob Hcur Ha Hcl HG").
    + split; [eapply keeps_trans; [exact Hk2|]; eapply keeps_trans; [|exact Hk3]; xkeep|]. repeat split; arep_lk.
    + iRight. iExists sb, sreg, xs. iFrame. done.
  - iApply (wp_amb_head138 w0 registry ge (arep_keys ++ ks)%list e _ G T fp dom se sereg f138 av ar ps pfx pxs cur s b r
      with "Hpfx Hwc Hsl Hsc Hl Hcur Ha Hcl Hargs HG");
      [rewrite avoids_app_l Hks; reflexivity | exact Hrule | exact Hse | exact H138 | lk_prove | lk_prove | lk_prove | lk_prove | exact Hb | exact Hal
      | exact Hend | exact Hr | exact Hav | exact Hala | exact Hda | exact Hra | exact Hps | exact Hse0 | exact Hsea
      | exact Hsee | exact Hser |].
    iIntros (e2 Hk2) "Hl Hcur Ha Hcl HG". apply keeps_app in Hk2 as [Hkt2 Hk2].
    iApply ("HL241" with "[%] Hs Hl Hib Hoob Hcur Ha Hcl HG").
    split; [eapply keeps_trans; [|exact Hk2]; xkeep|]. repeat split; arep_lk.
Qed.

End rep.
End GetoptLongAmbRepOn.
