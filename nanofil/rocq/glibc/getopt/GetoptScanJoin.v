From Glibc Require Import GlibcProgram.
(** The scanner of glibc's getopt either returns early or reaches the
    option parser. This file joins the scanner's proof with the
    sessions that its early returns leave behind. A caller that starts
    the scan with the private object set up and the saved position null
    or at a terminator gets, at every early return, a session at the new
    index over the permuted argument vector. At the option parser it
    gets the scanner's facts together with the untouched fields. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrcmpCode
  GetoptModule GetoptState GetoptBytes GetoptArgv GetoptExchange GetoptReturn GetoptIdlePath GetoptScanEnd
  GetoptScan GetoptScanSession.
From Glibc Require FileInv GetoptArgv GetoptExchange GetoptInitialize GetoptScan GetoptScanSession GetoptState OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.


(** The scan module proves the scanner. *)
(** The session module packs the fields after an early return. *)
Import GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L GetoptArgv.

Import ProgramAbbreviations.
Section scan_join.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance sj_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A program that calls getopt in a loop needs a session after every
    early return, because it will call getopt again. Before the scan, the
    caller holds the nine fields of the set-up object, and it knows that
    the saved position is null or points at a terminator. Each early
    return hands back -1 or 1, a permuted vector and a session at the new
    index. When the scan reaches the option parser instead, the caller
    receives the word that starts with a dash and all nine fields. *)
Lemma wp_getopt_scan_session ks e fr0 n i o f l a err oo c b r av ar ps pdd sdd Φ :
  avoids ks idle_names = true -> avoids ks scan_end_names = true ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  getopt_bounds n i (mkGetoptState i err oo a 1 c o f l) -> Z.of_nat (List.length ps) = n -> 0 <= o <= 2 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * (n + 1) <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ int_cell b 4 err -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ int_cell b 24 1 -∗
  pcell b 32 c -∗ int_cell b 40 o -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  (⌜c = null⌝ ∨ word_string DfracDiscarded c []) -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  ((∀ x ps' i', ⌜Permutation ps ps' /\ (x = 4294967295 \/ x = 1 /\ o <> 0)⌝ -∗
      getopt_session b r av ar ps' i' -∗ live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
      Φ (Ret (WInt x))) ∧
   (∀ e' s ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' /\
        i <= i' < n /\ sbyte s 0 = 45 /\ sbyte s 1 <> 0 /\
        lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) s -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 4 err -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ int_cell b 24 1 -∗
      pcell b 32 c -∗ int_cell b 40 o -∗ int_cell b 44 f' -∗ int_cell b 48 l' -∗
      (⌜c = null⌝ ∨ word_string DfracDiscarded c []) -∗
      live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L291") (Some (TAtom "L303")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L73") (Some fr0))) : gexpr) {{ Φ }}.
Proof.
  intros Hki Hks Hg Hdd Hv0 Hv2 Hv12 Hc0 Hc1 Hc2 Hbd Hlen Ho Hb Hal Hend Hr Hav Hala Hda Hra.
  unfold getopt_bounds in Hbd. cbn in Hbd.
  iIntros "Hl Hi He Hoo Ha Hin Hcur Ho Hf Hla #Hc Hva Hvc Hvs #Hdd HK".
  iApply (GetoptScan.wp_getopt_scan ks e fr0 n i o f l a b r av ar ps pdd sdd
            with "Hl Hi Ha Ho Hf Hla Hva Hvc Hvs Hdd [He Hoo Hin Hcur HK]");
    try (assumption || lia).
  iSplit; [|iSplit; [|iSplit]].
  - iDestruct "HK" as "[HK _]".
    iDestruct (GetoptScanSession.scan_exits_session ks e n i o err oo c a b r av ar ps Φ
                 with "He Hoo Hin Hcur Hc HK") as "[H _]"; first [lia | iExact "H"].
  - iDestruct "HK" as "[HK _]".
    iDestruct (GetoptScanSession.scan_exits_session ks e n i o err oo c a b r av ar ps Φ
                 with "He Hoo Hin Hcur Hc HK") as "(_ & H & _)"; first [lia | iExact "H"].
  - iDestruct "HK" as "[HK _]".
    iDestruct (GetoptScanSession.scan_exits_session ks e n i o err oo c a b r av ar ps Φ
                 with "He Hoo Hin Hcur Hc HK") as "(_ & _ & H)"; first [lia | iExact "H"].
  - iDestruct "HK" as "[_ HK]".
    iIntros (e' s ps' i' f' l' Hp) "Hws Hl Hi Ha Ho Hf Hla Hva Hvc Hvs".
    iApply ("HK" with "[%] Hws Hl Hi He Hoo Ha Hin Hcur Ho Hf Hla Hc Hva Hvc Hvs"). exact Hp.
Qed.

End scan_join.
