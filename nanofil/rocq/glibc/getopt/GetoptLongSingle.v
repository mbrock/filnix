(** In long-only mode, glibc's getopt sends a word with one dash to its
    long-option parser before it tries the short options. The parser
    answers -1 when no long option matches, and getopt then stores the
    cursor one byte into the word again and goes on to the short
    options. This file joins the call with both continuations, so the
    caller receives either the answer with a session at the new index
    or the short-option state with the cursor past the dash. *)

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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss GetoptLongJoinFound GetoptLongJoin GetoptLongCall GetoptLongOnly GetoptDispatch GetoptLongSite GetoptLongSession.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** A lookup in a list finds the same element as [nth_error]. *)
Lemma single_nth_error (l : list ptr) k x : l !! k = Some x -> nth_error l k = Some x.
Proof. revert k. induction l as [|y l IH]; intros [|k] H; cbn in *; try discriminate; auto. Qed.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongSingleOn (R : Runtime) (LG0 : LogicSig R).
(** The site module proves the long-only call and its test of the answer. *)
Module LSI := GetoptLongSiteOn R LG0.
(** The session module restores the session after a return. *)
Module LSS := GetoptLongSessionOn R LG0.
(** The cursor module proves the store of the cursor before the short options. *)
Module CU := GetoptCursorOn R LG0.
Import LSI LSI.LCL
  LSS
  LSI.LCL.LJN.LJF.LJM.LPB
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.

(** After the store of the cursor, the short options read these names, which keep their values through the store. *)
Definition single_keys : list name := Eval vm_compute in
  List.map TAtom ["v2"; "v12"; "pr.1"; "v80"; "chk2"; "chk20"]%string.

(** A call needs facts about its arguments, such as their values and ranges, and this tactic proves them. *)
Ltac single_side :=
  lazymatch goal with
  | |- environments.envs_entails _ _ => fail
  | |- avoids _ _ = true => vm_compute; reflexivity
  | _ => first [assumption | lia]
  end.

(** A key in the list keeps its value through the store of the cursor. *)
Ltac single_lk Hk :=
  lazymatch goal with |- lookup ?k ?e' = _ =>
    rewrite (keeps_in single_keys k _ e' Hk);
    [|unfold single_keys; cbn [In]; repeat first [left; reflexivity | right]] end.

Section single.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance single_stable : SafepointStable (os_wi w0) := LSI.LCL.LJN.LJF.LJM.LPB.LPF.LPP.LAR.LAO.LAH.LAL.LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance single_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The site and the cursor store describe the same cells through two copies of their modules, and this tactic converts between the copies. *)
Ltac single_conv b r i av ar ps c :=
  iAssert (pcell b 32 c) with "[Hcur]" as "Hcur"; [iExact "Hcur"|];
  iAssert (live b r) with "[Hl]" as "Hl"; [iExact "Hl"|];
  iAssert (int_cell b 0 i) with "[Hib]" as "Hib"; [iExact "Hib"|];
  iAssert (live av ar) with "[Ha]" as "Ha"; [iExact "Ha"|];
  iAssert (argv_cells av ps) with "[Hcl]" as "Hcl"; [iExact "Hcl"|].

(** In long-only mode the word q at index i starts with one dash and
    has a second character, and the cursor points one byte into it. The
    caller receives one of two results. An answer other than -1 comes
    back with a session at the new index. Under the table condition, the
    answer -1 means that no long option matched: getopt stores the same
    cursor again and goes on to the short options with the five fields
    that the parser left alone and the parser's resources. *)
Lemma wp_getopt_single_session e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg
    f138 f139 f140 f141 mid mid3 mid4 av ar ps lo os F pfx pxs po so q sq n lonly pe i oo a b r li er ord fst lst Φ :
  find_fn ge (TAtom "glibc_getopt#process_long_option") = Some (Defined glibc_process_long_option) ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "glibc_getopt#str.147") (ge_globals ge) = Some pfx -> no_neg1_val os ->
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
  ps !! Z.to_nat i = Some q -> sbyte sq 0 = 45 -> sbyte sq 1 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  0 <= ord <= 2 -> 0 <= fst <= lst -> lst <= i ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  opt_table lo os -∗ word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded pfx pxs -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 4 er -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ int_cell b 24 1 -∗
  pcell b 32 (ptr_add q 1) -∗ int_cell b 40 ord -∗ int_cell b 44 fst -∗ int_cell b 48 lst -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  ((∀ x i', ⌜x <> 4294967295 /\ (i <= i' <= i + 1 \/ (i' = i + 2 /\ i + 1 < n))%Z⌝ -∗
      LSS.S.getopt_session b r av ar ps i' -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗ Φ (Ret (WInt x))) ∧
   (∀ e' oo' a', ⌜lookup (TAtom "v2") e' = Some (WPtr (mkPtr av (Obj av))) /\
       lookup (TAtom "v12") e' = Some (WPtr (mkPtr b (Obj b))) /\ lookup (TAtom "pr.1") e' = Some (WPtr po) /\
       lookup (TAtom "v80") e' = lookup (TAtom "v80") e /\ lookup (TAtom "chk2") e' = Some (WPtr (mkPtr b (Obj b))) /\
       lookup (TAtom "chk20") e' = Some (WPtr (mkPtr (b + 32) (Obj b)))⌝ -∗
      live b r -∗ int_cell b 0 i -∗ pcell b 32 (ptr_add q 1) -∗ live av ar -∗ argv_cells av ps -∗
      int_cell b 4 er -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ int_cell b 24 1 -∗ int_cell b 40 ord -∗
      int_cell b 44 fst -∗ int_cell b 48 lst -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L75") (Some (TAtom "L338")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Exec (TAtom "L376") long_only_call long_only_jump)) : gexpr)
    {{ Φ }}.
Proof.
  intros Hgp H0 H2 H1 H6 H8 H10 H12 H3 Hstr Hneg Hcut Hmal Hset Hrule Hfree Hgn Hgl Hg Hgc Hse H138 H139 H140 H141 Hmid
    Hmid3 Hmid4 Hfl Hos Hpe Hlo Hq Hq0 Hq1 Hi Hn Hlen Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser Hord Hfst Hlst
    Hc2 Hc20.
  iIntros "#Ht #Hwq #Hpo #Hpfx #Hsl #Hsc Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla Ha Hcl #Hs HG HF HM Hli HK".
  assert (H1l : (1 < List.length sq)%nat) by (apply sbyte_in_len; lia).
  assert (Hl1 : Z.of_nat (List.length (take 1 sq)) = 1) by (rewrite length_take_le; lia).
  iAssert (word_string DfracDiscarded (ptr_add q 1) (drop 1 sq)) as "#Hws".
  { rewrite -Hl1. iApply word_string_suffix. by rewrite take_drop. }
  assert (Hq0' : sbyte sq 0 <> 0) by lia.
  iApply (wp_getopt_long_only_call w0 registry ge e G T fp dom M se sereg f138 f139 f140 f141 mid mid3 mid4 av ar ps lo
    os F pfx pxs po so q sq (ptr_add q 1) (drop 1 sq) n lonly pe i oo a b r li
    with "Ht Hwq Hpo Hpfx Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG HF HM Hli [-]"); try single_side.
  iSplit.
  - iIntros (x Ex) "Hres". iDestruct "HK" as "[HK _]".
    iDestruct "Hres" as (i' oo' a' c') "(Hl & Hib & Hoob & Hab & Hcur & Ha & Hcl & HG & HF & HM & Hli & %Hp)".
    destruct Hp as (Hi' & Hc' & _ & _ & _).
    iApply ("HK" $! x i' with "[%] [-Ha Hcl HG HF HM Hli] Ha Hcl HG HF HM Hli"); [split; [exact Ex | exact Hi']|].
    set (s0 := mkGetoptState i er oo a 1 (ptr_add q 1) ord fst lst).
    iApply (LSS.long_session b r av ar ps s0 i' oo' a' c' (drop 1 sq)
      with "[] Hws Hl Hib Her Hoob Hab Hini Hcur Hor Hfi Hla");
      try (unfold getopt_bounds; cbn; lia); try (cbn; lia); try reflexivity; try exact Hc'.
    unfold LSS.S.getopt_cursor. unfold s0. cbn [gs_next gs_last gs_ind]. destruct (drop 1 sq) as [|t0 t] eqn:Ht0.
    + iRight. iLeft. iExact "Hws".
    + iRight. iRight. iExists q, (take 1 sq), (drop 1 sq). iSplit; [iPureIntro|].
      * rewrite Ht0. split; [lia|]. split; [by apply single_nth_error|]. split; [discriminate|].
        split; [by rewrite Hl1|lia].
      * by rewrite take_drop.
  - iIntros (e' oo' a' (Hv2 & Hv12 & Hk2 & Hk20 & Hpr & Hv80)) "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli".
    iDestruct "HK" as "[_ HK]". rewrite Hc2 in Hk2. rewrite Hc20 in Hk20.
    assert (Hnq : nth (Z.to_nat i) ps null = q) by (by rewrite (nth_lookup_Some _ _ _ _ Hq)).
    single_conv b r i av ar ps (ptr_add q 1).
    iApply (CU.wp_getopt_short_cursor w0 registry ge single_keys e' (TAtom "L376") i n (ptr_add q 1) b r av ar ps
      with "Hl Hib Hcur Ha Hcl Hs"); try single_side.
    iIntros (e2 Hk) "Hl Hib Hcur Ha Hcl". rewrite Hnq.
    iApply ("HK" $! e2 oo' a' with "[%] Hl Hib Hcur Ha Hcl Her Hoob Hab Hini Hor Hfi Hla HG HF HM Hli").
    repeat split; single_lk Hk; first [assumption | rewrite Hpr; exact H1 | exact Hv80].
Qed.

End single.
End GetoptLongSingleOn.
