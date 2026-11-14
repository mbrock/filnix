(** glibc's long-option parser measures the name in the current word,
    searches the option table and then reaches one of its returns. This
    file joins the search with the returns of the found and not-found
    blocks, so that every way through the parser from its entry gives
    the caller the value of a return and the state that plo_res
    describes. *)

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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The found and not-found blocks read these parameters, which keep
    their values through the scan and the searches. *)
Definition jparam_keys : list name := Eval vm_compute in
  List.map TAtom ["v0"; "v2"; "v4"; "v6"; "v8"; "v10"; "v12"; "v14"; "v16"]%string.

Module GetoptLongJoinOn (R : Runtime) (LG0 : LogicSig R).
(** The found returns module supplies both kinds of return, the searches and the tactics. *)
Module LJF := GetoptLongJoinFoundOn R LG0.
Import LJF
  LJF.LJM
  LJF.LJM.LPB
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.


(** This tactic takes a parameter's value through the search, or finds a fact as a hypothesis. *)
Ltac jn_lk := first
  [ reflexivity
  | eassumption
  | match goal with H : keeps jparam_keys ?a ?c |- lookup ?k ?c = _ =>
      rewrite (keeps_in jparam_keys k a c H);
      [eassumption | solve [unfold jparam_keys; cbn [In]; repeat first [left; reflexivity | right]]] end ].

(** This tactic proves a pure premise left by an [iApply] and leaves the proof-mode goal alone. *)
Ltac jn_side :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- avoids _ _ = true => vm_compute; reflexivity
  | |- lookup _ _ = _ => jn_lk
  | _ => first [assumption | lia]
  end.

Section join.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance join_stable : SafepointStable (os_wi w0) := LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance join_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A caller needs one rule for the whole parser, whatever the word
    holds. Here the parser starts on the word q at index i, and the
    rest s of that word starts at the cursor cur. The parser may find
    an option or none, and it may take any of its returns. Each way
    gives the caller a return value x and the state that plo_res
    describes. The caller names the allocator, the free, the stack
    check, the memset and the reports as premises. *)
Lemma wp_long_join e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps
    lo os F pfx pxs po so q sq cur s n lonly pe i oo a b r li Φ :
  getopt_cutoff_rule w0 registry ge -> getopt_malloc_rule w0 registry ge M -> getopt_memset_rule w0 registry ge ->
  getopt_ldiag_rule w0 registry ge G T fp dom -> getopt_free_rule w0 registry ge ->
  find_fn ge (TAtom "__GI_strncmp") = Some (Defined glibc_strncmp) ->
  find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen) ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some f138 ->
  lookup (TAtom "glibc_getopt#str.139") (ge_globals ge) = Some f139 ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  Forall (fun x => lo_flag x = null \/ lo_flag x ∈ F) os -> (List.length os < 2 ^ 31)%Z ->
  0 <= pe < 2 ^ 32 -> 0 <= lonly < 2 ^ 32 ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v4") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v14") e = Some (WInt pe) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  ps !! Z.to_nat i = Some q -> (lonly <> 0 -> sbyte sq 0 <> 0) ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  (∀ e' l rv x, ⌜value_x ge e' W rv = Some (WInt x)⌝ -∗
     LJF.LJM.plo_res b r av ar ps li F G M i n cur s a os x -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec l [] (JRet rv))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid Hmid3 Hmid4 Hfl Hos Hpe Hlo
    H0 H2 H4 H6 H8 H10 H12 H14 H16 Hq Hq0 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hws #Hsl #Hsc Hl Hib Hoob Hab Hcur Ha Hcl #Hs HG HF HM Hli HK".
  assert (Hps : ps <> []) by (intros ->; cbn in Hlen; lia).
  iApply (LJF.LJM.LPB.wp_long_body w0 registry ge jparam_keys e G T fp dom M se sereg f138 f139 f140 f141
    av ar ps lo os F pfx pxs cur s lonly pe i oo b r with "Ht Hpfx Hws Hsl Hsc Hl Hib Hoob Hcur Ha Hcl Hs HG HF HM");
    try jn_side.
  iSplit.
  - iIntros (e2 p w (Hk2 & Hf & H12' & H7' & H90 & Hp1 & Hc0 & Hc1)) "Hl Hib Hoob Hcur Ha Hcl HG HF HM".
    destruct Hf as [[-> ->] | (j & Hj & -> & ->)].
    + iApply (LJF.LJM.wp_long_join_miss w0 registry ge [] e2 G T fp dom M se sereg mid av ar ps q sq po so pfx pxs
        cur s i n lonly pe oo a li F b r os
        with "Hwq Hpo Hpfx Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG HF HM Hli"); try jn_side.
      iIntros (e' l rv x [_ Hv]) "Hres". iApply ("HK" $! e' l rv x with "[%] Hres"). exact Hv.
    + destruct (lookup_lt_is_Some_2 os j Hj) as [x Hx].
      pose proof (Forall_lookup_1 _ _ _ _ Hfl Hx) as Hfx.
      iApply (LJF.wp_long_join_found w0 registry ge [] e2 G T fp dom M se sereg mid3 mid4 av ar ps lo os j x
        pfx pxs po so cur s i n pe oo a b r li F
        with "Ht Hpfx Hpo Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG HF HM Hli"); try jn_side.
      iIntros (e' l rv v [_ Hv]) "Hres". iApply ("HK" $! e' l rv v with "[%] Hres"). exact Hv.
  - iIntros (e2 _) "Hl Hib Hoob Hcur Ha Hcl HG HF HM".
    iApply ("HK" $! e2 _ (Const 63) 63 with "[%] [-]"); [reflexivity|].
    iApply (LJF.LJM.plo_res_intro with "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli");
      [lia | right; right; reflexivity | left; reflexivity | lia | intros Hv; lia].
Qed.

End join.
End GetoptLongJoinOn.
