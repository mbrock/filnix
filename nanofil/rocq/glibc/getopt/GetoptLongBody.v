(** glibc's long-option parser starts by measuring the name at its
    cursor. Then it searches the caller's table for an option with
    exactly that name, and when it finds none, for options whose names
    start with it. This file proves that start safe from the parser's
    entry up to the block that handles a found option or none, or up to
    the report of an ambiguous word. *)

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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The searches read the parser's parameters after the scan. *)
Definition bparam_keys : list name := Eval vm_compute in
  List.map TAtom ["v2"; "v6"; "v10"; "v12"; "v14"; "v16"]%string.

(** The found-option block reads these results of the scan after the searches. *)
Definition bout_keys : list name := Eval vm_compute in
  List.map TAtom ["pr.1"; "chk0"; "chk1"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongBodyOn (R : Runtime) (LG0 : LogicSig R).
(** The search module supplies both searches, the report, the set and the tactics. *)
Module LPF := GetoptLongFindOn R LG0.
Import LPF LPF.LPP LPF.LPP.LAR LPF.LPP.LAR.LAO LPF.LPP.LAR.LAO.LAH LPF.LPP.LAR.LAO.LAH.LAL LPF.LPP.LAR.LAO.LAH.LAL.LAI LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.


(** This tactic takes a lookup through assignments and through the steps that keep the name. *)
Ltac body_lk := first
  [ apply Symbolic.lookup_after_put_same
  | eapply lookup_put_miss; [vm_compute; reflexivity | body_lk]
  | eassumption
  | match goal with H : keeps ?KS ?a ?c |- lookup ?k ?c = _ =>
      rewrite (keeps_in KS k a c H);
      [body_lk | solve [unfold bparam_keys, bout_keys; cbn [In]; repeat first [left; reflexivity | right]]] end ].

Section body.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance body_stable : SafepointStable (os_wi w0) := LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance body_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser starts on the word whose rest s starts at its cursor
    cur. It measures the name, searches the table at lo for it and then
    for names that start with it. It reaches the found-option block with
    the found entry p and its index w, or with no entry, together with
    the end of the name and the scan's checks. Otherwise it reports the
    word as ambiguous and answers '?'. The flag targets stay the
    caller's, the allocator keeps its state M, and the report gives G
    back. *)
Lemma wp_long_body ks e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg f138 f139 f140 f141 av ar ps lo os F
    pfx pxs cur s lonly pe i oo b r Φ :
  avoids ks scan_names = true -> avoids ks exact_names = true ->
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
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v10") e = Some (WInt lonly) -> lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v14") e = Some (WInt pe) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗
  ((∀ e' p w, ⌜keeps ks e e' /\ pfx_first lo (List.length os) p w /\ lookup (TAtom "pr.12") e' = Some (WInt w) /\
        lookup (TAtom "pr.7") e' = Some (WPtr p) /\ lookup (TAtom "v90") e' = Some (WInt 0) /\
        lookup (TAtom "pr.1") e' = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) /\
        lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
        lookup (TAtom "chk1") e' = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s))))⌝ -∗
      live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None
        (Exec (TAtom "L87") (b_insts plo_blk87) (b_jump plo_blk87))) : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e'⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 0 -∗ pcell b 32 (ptr_add cur (Z.of_nat (List.length s))) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L307") [] (JRet (Const 63)))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hksn Hksx Hksl Hksc Hkss Hksa Hksm Hkse Hksr Hksi Hkst Hcut Hmal Hset Hrule Hfree Hgn Hgl Hse H138 H139
    H140 H141 Hfl Hos Hpe Hi H2 H6 H10 H12 H14 H16 Hb Hal Hend Hr Hav Hala Hda Hra Hps Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hpfx #Hws #Hsl #Hsc Hl Hib Hoob Hcur Ha Hcl #Hargs HG HF HM HK".
  iPoseProof "Ht" as "Ht0".
  iDestruct "Ht" as (tb treg) "(%Ht & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iApply (wp_getopt_long_scan w0 registry ge (bparam_keys ++ ks)%list e cur s b r with "Hws Hl Hcur");
    [rewrite avoids_app_l Hksn; reflexivity | exact H12 | exact Hb | exact Hal | exact Hend | exact Hr |].
  iIntros (e1 (Hk1 & Hp1 & H48 & Hc0 & Hc1)) "Hl Hcur". apply keeps_app in Hk1 as [Hkt1 Hk1].
  assert (H6' : lookup (TAtom "v6") e1 = Some (WPtr lo)) by body_lk.
  assert (Hlo : ptr_add lo (32 * Z.of_nat 0) = lo).
  { destruct lo as [la lc]. unfold ptr_add. cbn [ptr_addr ptr_cap] in *. f_equal.
    rewrite ?Z.add_0_r; first [reflexivity | apply Z.mod_small; lia]. }
  st. change (0 mod 2 ^ 32) with 0. pcmp_fold "L50" plo_blk50.
  iApply (wp_long_find w0 registry ge (bout_keys ++ ks)%list _ G T fp dom M se sereg f138 f139 f140 f141
    av ar ps lo os F pfx pxs cur s lonly pe i oo b r
    with "Ht0 Hpfx Hws Hsl Hsc Hl Hib Hoob Hcur Ha Hcl Hargs HG HF HM");
    [rewrite avoids_app_l Hksx; reflexivity | rewrite avoids_app_l Hksl; reflexivity
    | rewrite avoids_app_l Hksc; reflexivity | rewrite avoids_app_l Hkss; reflexivity
    | rewrite avoids_app_l Hksa; reflexivity | rewrite avoids_app_l Hksm; reflexivity
    | rewrite avoids_app_l Hkse; reflexivity | rewrite avoids_app_l Hksr; reflexivity
    | rewrite avoids_app_l Hksi; reflexivity | rewrite avoids_app_l Hkst; reflexivity | exact Hcut | exact Hmal
    | exact Hset | exact Hrule | exact Hfree | exact Hgn | exact Hgl | exact Hse | exact H138 | exact H139 | exact H140
    | exact H141 | exact Hfl | exact Hos | exact Hpe | exact Hi | body_lk | body_lk | body_lk | body_lk | body_lk
    | body_lk | body_lk | body_lk | rewrite Hlo; lk_prove | lk_prove | exact Hb | exact Hal | exact Hend | exact Hr
    | exact Hav | exact Hala | exact Hda | exact Hra | exact Hps | exact Hse0 | exact Hsea | exact Hsee | exact Hser |].
  iSplit.
  - iIntros (e2 p w (Hk2 & Hf & H12' & H7' & H90)) "Hl Hib Hoob Hcur Ha Hcl HG HF HM".
    apply keeps_app in Hk2 as [Hkt2 Hk2]. iDestruct "HK" as "[HK _]".
    iApply ("HK" $! e2 p w with "[%] Hl Hib Hoob Hcur Ha Hcl HG HF HM").
    split; [eapply keeps_trans; [exact Hk1|]; eapply keeps_trans; [|exact Hk2]; xkeep|].
    repeat split; first [assumption | body_lk].
  - iIntros (e2 Hk2) "Hl Hib Hoob Hcur Ha Hcl HG HF HM". apply keeps_app in Hk2 as [Hkt2 Hk2].
    iDestruct "HK" as "[_ HK]". iApply ("HK" with "[%] Hl Hib Hoob Hcur Ha Hcl HG HF HM").
    eapply keeps_trans; [exact Hk1|]. eapply keeps_trans; [|exact Hk2]. xkeep.
Qed.

End body.
End GetoptLongBodyOn.
