(** When glibc's long-option parser finds no option whose name equals a
    word's name, it searches the table for names that start with it.
    The search ends with one match, with none, or with an ambiguity. One
    match or none leads to the block that handles a found option or a
    missing one. An ambiguity leads to its report. This file proves
    that path from the end of the exact search. *)

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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The decision and the report read these names after the search. *)
Definition ppath_keys : list name := Eval vm_compute in
  List.map TAtom ["v2"; "v6"; "v12"; "v14"; "v16"; "chk0"; "pr.9"]%string.

(** The report reads these names after the decision. *)
Definition pend_keys : list name := Eval vm_compute in
  List.map TAtom ["pr.39"; "pr.30"; "pr.21"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongPfxPathOn (R : Runtime) (LG0 : LogicSig R).
(** The report module supplies the report, the search, the set and the tactics. *)
Module LAR := GetoptLongAmbRepOn R LG0.
Import LAR LAR.LAO LAR.LAO.LAH LAR.LAO.LAH.LAL LAR.LAO.LAH.LAL.LAI LAR.LAO.LAH.LAL.LAI.LAP LAR.LAO.LAH.LAL.LAI.LAP.LAT LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.


(** This tactic takes a lookup through assignments and through the steps that keep the name. *)
Ltac ppath_lk := first
  [ apply Symbolic.lookup_after_put_same
  | eapply lookup_put_miss; [vm_compute; reflexivity | ppath_lk]
  | eassumption
  | match goal with H : keeps ?KS ?a ?c |- lookup ?k ?c = _ =>
      rewrite (keeps_in KS k a c H);
      [ppath_lk | solve [unfold ppath_keys, pend_keys; cbn [In]; repeat first [left; reflexivity | right]]] end ].

Section path.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance ppath_stable : SafepointStable (os_wi w0) := LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance ppath_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The exact search found no option for the word whose rest s starts
    at the cursor cur. The parser searches the table for names that
    start with the word's name. When at most one entry matches, it goes
    on at the found-option block with the first match p and its index w,
    or with no option at all. Otherwise it reports the ambiguity and
    answers '?'. The flag targets stay the caller's, the allocator keeps
    its state M, and the report gives G back. *)
Lemma wp_long_pfx_path ks e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg f138 f139 f140 f141 av ar ps lo os F
    pfx pxs cur s lonly pe i oo b r Φ :
  avoids ks ploop_names = true -> avoids ks pcmp_names = true -> avoids ks pset_names = true ->
  avoids ks palloc_names = true -> avoids ks pmark_names = true -> avoids ks pend_names = true ->
  avoids ks arep_names = true -> avoids ks alist_names = true -> avoids ks atail_names = true ->
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z -> 0 <= pe < 2 ^ 32 ->
  0 <= i < 2 ^ 31 - 1 ->
  pfx_at e b s lonly pe (Z.of_nat (List.length os)) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v16") e = Some (WPtr pfx) -> lookup (TAtom "pr.6") e = Some (WPtr null) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗
  ((∀ e' p w, ⌜keeps ks e e' /\ pfx_first lo (List.length os) p w /\ lookup (TAtom "pr.12") e' = Some (WInt w) /\
        lookup (TAtom "pr.7") e' = Some (WPtr p)⌝ -∗
      live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None
        (Exec (TAtom "L87") (b_insts plo_blk87) (b_jump plo_blk87))) : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e'⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 0 -∗ pcell b 32 (ptr_add cur (Z.of_nat (List.length s))) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L307") [] (JRet (Const 63)))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L98") (Some (TAtom "L53")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hksl Hksc Hkss Hksa Hksm Hkse Hksr Hksi Hkst Hcut Hmal Hset Hrule Hfree Hgn Hgl Hse H138 H139 H140 H141
    Hfl Hos Hpe Hi Hat H2 H6 H16 H6p Hb Hal Hend Hr Hav Hala Hda Hra Hps Hse0 Hsea Hsee Hser.
  pose proof Hat as (H12 & Hc0 & H48 & H10 & H14 & H90 & H9).
  iIntros "#Ht #Hpfx #Hws #Hsl #Hsc Hl Hib Hoob Hcur Ha Hcl #Hargs HG HF HM HK".
  iPoseProof "Ht" as "Ht0".
  iDestruct "Ht" as (tb treg) "(%Ht & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  assert (Hlo : ptr_add lo (32 * Z.of_nat 0) = lo).
  { destruct lo as [la lc]. unfold ptr_add. cbn [ptr_addr ptr_cap] in *. f_equal.
    rewrite ?Z.add_0_r; first [reflexivity | apply Z.mod_small; lia]. }
  st. pcmp_fold "L98" plo_blk98.
  change (0 mod 2 ^ 32) with 0. change (4294967295 mod 2 ^ 32) with 4294967295. change (0 mod 2 ^ 64) with 0.
  fold null.
  iApply (wp_pfx_loop w0 registry ge (ppath_keys ++ ks)%list _ M 0 null 4294967295 0 0 null cur s lo os F b r lonly pe
    with "Hws Ht0 Hl Hcur HF [] HM");
    [rewrite avoids_app_l Hksl; reflexivity | rewrite avoids_app_l Hksc; reflexivity
    | rewrite avoids_app_l Hkss; reflexivity | rewrite avoids_app_l Hksa; reflexivity
    | rewrite avoids_app_l Hksm; reflexivity | exact Hcut | exact Hmal | exact Hset | exact Hgn | exact Hfl | exact Hos
    | exact Hpe | exact Hb | exact Hal | exact Hend | exact Hr | unfold pfx_at; repeat split; lk_prove
    | rewrite Hlo; lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lia
    | left; split; reflexivity | left; reflexivity | left; reflexivity | by iLeft |].
  iIntros (e1 p w a m sp (Hk1 & H8' & H42' & H39' & H30' & H21' & Hf & Ha & Hm)) "Hl Hcur HF Hs HM".
  apply keeps_app in Hk1 as [Hkt1 Hk1].
  assert (Hk1e : keeps ks e e1) by (eapply keeps_trans; [|exact Hk1]; xkeep).
  assert (Hw : 0 <= w < 2 ^ 32) by (destruct Hf as [(_ & ->) | (j & Hj & _ & ->)]; lia).
  iApply (wp_pfx_end w0 registry ge (ppath_keys ++ pend_keys ++ ks)%list e1 _ p w a m sp with "Hs");
    [rewrite !avoids_app_l Hkse; reflexivity | exact H8' | exact H42' | exact H39' | exact H30' | exact H21'
    | exact Hw | exact Ha | exact Hm |].
  iSplit.
  - iIntros (e2 (Hk2 & -> & -> & -> & H12' & H7')). apply keeps_app in Hk2 as [Hkt2 Hk2].
    apply keeps_app in Hk2 as [Hkp2 Hk2]. iDestruct "HK" as "[HK _]".
    iApply ("HK" $! e2 p w with "[%] Hl Hib Hoob Hcur Ha Hcl HG HF HM").
    split; [eapply keeps_trans; [exact Hk1e | exact Hk2]|]. repeat split; assumption.
  - iIntros (e2 (Hk2 & Hsa)) "Hs". apply keeps_app in Hk2 as [Hkt2 Hk2].
    apply keeps_app in Hk2 as [Hkp2 Hk2].
    iApply (wp_amb_report w0 registry ge ks e2 G T fp dom se sereg f138 f139 f140 f141 av ar ps lo os pfx pxs
      cur s pe a m sp i oo b r with "Ht0 Hpfx Hws Hsl Hsc Hs Hl Hib Hoob Hcur Ha Hcl Hargs HG");
      [exact Hksr | exact Hksi | exact Hkst | exact Hrule | exact Hfree | exact Hgl | exact Hse | exact H138
      | exact H139 | exact H140 | exact H141 | ppath_lk | ppath_lk | ppath_lk | ppath_lk | ppath_lk | ppath_lk
      | ppath_lk | ppath_lk | ppath_lk | ppath_lk | exact Hpe | exact Ha | exact Hsa | exact Hm | exact Hos | exact Hi
      | exact Hb | exact Hal | exact Hend | exact Hr | exact Hav | exact Hala | exact Hda | exact Hra | exact Hps
      | exact Hse0 | exact Hsea | exact Hsee | exact Hser |].
    iIntros (e3 Hk3) "Hl Hib Hoob Hcur Ha Hcl HG". iDestruct "HK" as "[_ HK]".
    iApply ("HK" with "[%] Hl Hib Hoob Hcur Ha Hcl HG HF HM").
    eapply keeps_trans; [exact Hk1e|]. eapply keeps_trans; [exact Hk2 | exact Hk3].
Qed.

End path.
End GetoptLongPfxPathOn.
