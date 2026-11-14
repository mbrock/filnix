From Glibc Require Import GlibcProgram.
(** After glibc's long-option parser has measured the name at its
    cursor, it searches the caller's table for an option with exactly
    that name, and when it finds none, for options whose names start
    with it. This file proves both searches safe up to the block that
    handles a found option or none, or up to the report of an ambiguous
    word. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail GetoptLongAmbPrint GetoptLongAmbItem GetoptLongAmbList
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongAmbHead GetoptLongAmbItem GetoptLongAmbList GetoptLongAmbPoss GetoptLongAmbPrint GetoptLongAmbRep GetoptLongAmbTail GetoptLongDiag GetoptLongExact GetoptLongPfxAlloc GetoptLongPfxCmp GetoptLongPfxEnd GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxMark GetoptLongPfxPath GetoptLongPfxSet GetoptLongPfxStep GetoptLongScan GetoptLongStore GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The prefix search reads these names after the exact search. *)
Definition bscan_keys : list name := Eval vm_compute in
  List.map TAtom ["v2"; "v6"; "v10"; "v12"; "v14"; "v16"; "pr.1"; "chk0"; "chk1"; "v48"]%string.

(** The decision reads these names after the prefix search. *)
Definition bpath_keys : list name := Eval vm_compute in
  List.map TAtom ["v2"; "v6"; "v10"; "v12"; "v14"; "v16"; "pr.1"; "chk0"; "chk1"; "v48"; "v90"]%string.


(** The prefix path module supplies both searches, the report, the set and the tactics. *)
Import GetoptLongPfxPath GetoptLongAmbRep GetoptLongAmbPoss GetoptLongAmbHead GetoptLongAmbList GetoptLongAmbItem GetoptLongAmbPrint GetoptLongAmbTail GetoptLongPfxEnd GetoptLongPfxLoop GetoptLongPfxIter GetoptLongPfxStep GetoptLongPfxSet GetoptLongPfxAlloc GetoptLongPfxMark GetoptLongPfxCmp GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.


(** This tactic takes a lookup through assignments and through the steps that keep the name. *)
Ltac find_lk := first
  [ apply Symbolic.lookup_after_put_same
  | eapply lookup_put_miss; [vm_compute; reflexivity | find_lk]
  | eassumption
  | match goal with H : keeps ?KS ?a ?c |- lookup ?k ?c = _ =>
      rewrite (keeps_in KS k a c H);
      [find_lk | solve [unfold bscan_keys, bpath_keys; cbn [In];
                        repeat first [left; reflexivity | right]]] end ].

Import ProgramAbbreviations.
Section find.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance find_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser has measured the name of the word whose rest s starts at
    its cursor cur. It searches the table at lo for the name and then
    for names that start with it. It reaches the found-option block with
    the found entry p and its index w, or with no entry. Otherwise it
    reports the word as ambiguous and answers '?'. The flag targets stay the
    caller's, the allocator keeps its state M, and the report gives G
    back. *)
Lemma wp_long_find ks e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg f138 f139 f140 f141 av ar ps lo os F
    pfx pxs cur s lonly pe i oo b r Φ :
  avoids ks exact_names = true ->
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
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "v48") e = Some (WInt (Z.of_nat (eq_len s))) ->
  lookup (TAtom "pr.2") e = Some (WPtr (ptr_add lo (32 * Z.of_nat 0))) -> lookup (TAtom "pr.9") e = Some (WInt 0) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗
  ((∀ e' p w, ⌜keeps ks e e' /\ pfx_first lo (List.length os) p w /\ lookup (TAtom "pr.12") e' = Some (WInt w) /\
        lookup (TAtom "pr.7") e' = Some (WPtr p) /\ lookup (TAtom "v90") e' = Some (WInt 0)⌝ -∗
      live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None
        (Exec (TAtom "L87") (b_insts plo_blk87) (b_jump plo_blk87))) : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e'⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 0 -∗ pcell b 32 (ptr_add cur (Z.of_nat (List.length s))) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L307") [] (JRet (Const 63)))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L50") (b_insts plo_blk50) (b_jump plo_blk50))) : gexpr) {{ Φ }}.
Proof.
  intros Hksx Hksl Hksc Hkss Hksa Hksm Hkse Hksr Hksi Hkst Hcut Hmal Hset Hrule Hfree Hgn Hgl Hse H138 H139
    H140 H141 Hfl Hos Hpe Hi H2 H6 H10 H12 H14 H16 Hc0 H48 Hp2 Hp9 Hb Hal Hend Hr Hav Hala Hda Hra Hps
    Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hpfx #Hws #Hsl #Hsc Hl Hib Hoob Hcur Ha Hcl #Hargs HG HF HM HK".
  iApply (wp_long_exact_loop (bscan_keys ++ ks)%list e 0 cur s lo os b r with "Hws Ht Hl Hcur");
    [rewrite avoids_app_l Hksx; reflexivity | exact Hgn | exact Hgl | exact H12 | exact Hc0 | exact H48 | exact Hp2
    | exact Hp9 | lia | exact Hos | exact Hb | exact Hal | exact Hend | exact Hr |].
  iSplit.
  - iIntros (e2 (Hk2 & H90 & H6p & H9)) "Hl Hcur". apply keeps_app in Hk2 as [Hkt2 Hk2].
    iApply (wp_long_pfx_path (bpath_keys ++ ks)%list e2 G T fp dom M se sereg f138 f139 f140 f141
      av ar ps lo os F pfx pxs cur s lonly pe i oo b r
      with "Ht Hpfx Hws Hsl Hsc Hl Hib Hoob Hcur Ha Hcl Hargs HG HF HM");
      [rewrite avoids_app_l Hksl; reflexivity | rewrite avoids_app_l Hksc; reflexivity
      | rewrite avoids_app_l Hkss; reflexivity | rewrite avoids_app_l Hksa; reflexivity
      | rewrite avoids_app_l Hksm; reflexivity | rewrite avoids_app_l Hkse; reflexivity
      | rewrite avoids_app_l Hksr; reflexivity | rewrite avoids_app_l Hksi; reflexivity
      | rewrite avoids_app_l Hkst; reflexivity | exact Hcut | exact Hmal | exact Hset | exact Hrule | exact Hfree
      | exact Hgn | exact Hgl | exact Hse | exact H138 | exact H139 | exact H140 | exact H141 | exact Hfl | exact Hos
      | exact Hpe | exact Hi | unfold pfx_at; repeat split; find_lk | find_lk | find_lk | find_lk | exact H6p
      | exact Hb | exact Hal | exact Hend | exact Hr | exact Hav | exact Hala | exact Hda | exact Hra | exact Hps
      | exact Hse0 | exact Hsea | exact Hsee | exact Hser |].
    iSplit.
    + iIntros (e3 p w (Hk3 & Hf & H12' & H7')) "Hl Hib Hoob Hcur Ha Hcl HG HF HM".
      apply keeps_app in Hk3 as [Hkt3 Hk3]. iDestruct "HK" as "[HK _]".
      iApply ("HK" $! e3 p w with "[%] Hl Hib Hoob Hcur Ha Hcl HG HF HM").
      split; [eapply keeps_trans; [exact Hk2 | exact Hk3]|]. repeat split; first [assumption | find_lk].
    + iIntros (e3 Hk3) "Hl Hib Hoob Hcur Ha Hcl HG HF HM". apply keeps_app in Hk3 as [Hkt3 Hk3].
      iDestruct "HK" as "[_ HK]". iApply ("HK" with "[%] Hl Hib Hoob Hcur Ha Hcl HG HF HM").
      eapply keeps_trans; [exact Hk2 | exact Hk3].
  - iIntros (e2 j (Hk2 & Hj & H90 & H6p & H11)) "Hl Hcur". apply keeps_app in Hk2 as [Hkt2 Hk2].
    step. rewrite (Z.mod_small (Z.of_nat j) (2 ^ 32)); [|lia]. pcmp_fold "L87" plo_blk87.
    iDestruct "HK" as "[HK _]".
    iApply ("HK" $! _ (ptr_add lo (32 * Z.of_nat j)) (Z.of_nat j) with "[%] Hl Hib Hoob Hcur Ha Hcl HG HF HM").
    split; [eapply keeps_trans; [exact Hk2|]; xkeep|]. split; [right; exists j; repeat split; lia|].
    repeat split; lk_prove.
Qed.

End find.
