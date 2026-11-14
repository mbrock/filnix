From Glibc Require Import GlibcProgram.
(** Each call of glibc's scanner first tidies the argument vector, which
    only the permuting order rearranges, and then decides what the
    argument at the public index is. This file joins the two proofs. The call either returns
    early, because no argument is left or because it met a nonoption, or
    it reaches the option parser with an argument that starts with a
    dash and has a second character. *)

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
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange
  GetoptExchangeTwo GetoptIdlePath GetoptReturn GetoptScanEnd.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptIdlePath GetoptInitialize GetoptScanEnd GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** These names hold what the decision reads after the tidying. *)
Definition scan_keys : list name := List.map TAtom ["v0"; "v2"; "v12"; "chk0"; "chk1"; "chk2"]%string.


(** The path module proves the tidying of the argument vector. *)
(** The decision module proves the decision and the early returns. *)
Import GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section scan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance scan_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic proves a lookup that the kept names Hk carry over. *)
Ltac kin Hk H := rewrite (keeps_in _ _ _ _ Hk); [exact H | cbn; tauto].

(** The call must stay inside the argument vector and its own state
    whatever the arguments are. It starts with the positions in order,
    and each outcome ends with them still in order, with a permuted
    vector and a bounded index. With no argument left,
    the index points at the first pending nonoption, if any. A
    nonoption either leaves everything as it is, in strict order, or
    becomes the private option argument. An option reaches the parser
    with its string. *)
Lemma wp_getopt_scan ks e fr0 n i o f l a b r av ar ps pdd sdd Φ :
  avoids ks idle_names = true -> avoids ks scan_end_names = true ->
  find_fn ge (TAtom "__GI_strcmp") = Some (Defined glibc_strcmp) ->
  lookup (TAtom "glibc_getopt#str.146") (ge_globals ge) = Some pdd ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 <= f <= l -> l <= n -> f <= i -> i <= n < 2 ^ 31 -> Z.of_nat (List.length ps) = n ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 i -∗ pcell b 16 a -∗ int_cell b 40 o -∗ int_cell b 44 f -∗ int_cell b 48 l -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ word_string DfracDiscarded pdd sdd -∗
  ((∀ e' fr ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' /\ i' = n⌝ -∗
      live b r -∗ int_cell b 0 (if f' =? l' then i' else f') -∗ pcell b 16 a -∗ int_cell b 40 o -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L275") (Some fr))) : gexpr) {{ Φ }}) ∧
   (∀ e' ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' /\
        i <= i' < n /\ o = 0⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ pcell b 16 a -∗ int_cell b 40 o -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L316") (Some (TAtom "L289")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' /\
        i <= i' < n /\ o <> 0⌝ -∗
      live b r -∗ int_cell b 0 (i' + 1) -∗ pcell b 16 (nth (Z.to_nat i') ps' null) -∗ int_cell b 40 o -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Exec (TAtom "L318") [] (b_jump getopt_blk318))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' s ps' i' f' l', ⌜Permutation ps ps' /\ keeps ks e e' /\ 0 <= f' <= l' /\ l' <= i' /\
        i <= i' < n /\ sbyte s 0 = 45 /\ sbyte s 1 <> 0 /\
        lookup (TAtom "chk100") e' = Some (WPtr (mkPtr b (Obj b)))⌝ -∗
      word_string DfracDiscarded (nth (Z.to_nat i') ps' null) s -∗
      live b r -∗ int_cell b 0 i' -∗ pcell b 16 a -∗ int_cell b 40 o -∗
      int_cell b 44 f' -∗ int_cell b 48 l' -∗ live av ar -∗ argv_cells av ps' -∗ argv_strs ps' -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L291") (Some (TAtom "L303")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L73") (Some fr0))) : gexpr) {{ Φ }}.
Proof.
  intros Hki Hks Hg Hdd Hv0 Hv2 Hv12 Hc0 Hc1 Hc2 Hfl Hln Hfi Hin Hlen Hb Hal Hend Hr Hav Hala Hda Hra.
  iIntros "Hl Hi Hab Ho Hf Hla Ha Hc #Hs #Hdd HK".
  iApply (GetoptIdlePath.wp_getopt_idle (ks ++ scan_keys) e fr0 n i o f l b r av ar ps pdd sdd
            with "Hl Hi Ho Hf Hla Ha Hc Hs Hdd [Hab HK]");
    [ apply avoids_app_r; [exact Hki | vm_compute; reflexivity] | exact Hg | exact Hdd
    | exact Hv0 | exact Hv2 | exact Hv12 | exact Hc0 | exact Hc2
    | lia | lia | lia | lia | exact Hlen | lia | lia | lia | lia | lia | lia | lia | lia |].
  iIntros (e1 ps1 i1 f1 l1 (Hp & Hk & Hfl1 & Hli1 & Hii & H23)) "Hl Hi Ho Hf Hla Ha Hc #Hs1".
  apply keeps_app in Hk as [Hk Hk'].
  assert (Hlen1 : Z.of_nat (List.length ps1) = n) by (rewrite -(Permutation_length Hp); exact Hlen).
  iApply (GetoptScanEnd.wp_getopt_scan_end ks e1 i1 n o f1 l1 a b r av ar ps1
            with "Hl Hi Hab Ho Hf Hla Ha Hc Hs1 [HK]");
    [ exact Hks | kin Hk' Hv0 | kin Hk' Hv2 | kin Hk' Hv12 | kin Hk' Hc0 | kin Hk' Hc1 | kin Hk' Hc2 | exact H23
    | lia | lia | lia | lia | exact Hlen1 | lia | lia | lia | lia | lia | lia | lia | lia |].
  iSplit; [|iSplit; [|iSplit]].
  - iIntros (e' fr (Hk2 & Hi1)) "Hl Hi Hab Ho Hf Hla Ha Hc". iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[%] Hl Hi Hab Ho Hf Hla Ha Hc Hs1").
    split; [exact Hp|]. split; [eapply keeps_trans; [exact Hk | exact Hk2]|]. lia.
  - iIntros (e' (Hk2 & Hi1 & Ho0)) "Hl Hi Hab Ho Hf Hla Ha Hc". iDestruct "HK" as "(_ & HK & _)".
    iApply ("HK" with "[%] Hl Hi Hab Ho Hf Hla Ha Hc Hs1").
    split; [exact Hp|]. split; [eapply keeps_trans; [exact Hk | exact Hk2]|]. lia.
  - iIntros (e' (Hk2 & Hi1 & Ho0)) "Hl Hi Hab Ho Hf Hla Ha Hc". iDestruct "HK" as "(_ & _ & HK & _)".
    iApply ("HK" with "[%] Hl Hi Hab Ho Hf Hla Ha Hc Hs1").
    split; [exact Hp|]. split; [eapply keeps_trans; [exact Hk | exact Hk2]|]. lia.
  - iIntros (e' s (Hk2 & Hi1 & H0 & H1 & H100)) "Hws Hl Hi Hab Ho Hf Hla Ha Hc". iDestruct "HK" as "(_ & _ & _ & HK)".
    iApply ("HK" with "[%] Hws Hl Hi Hab Ho Hf Hla Ha Hc Hs1").
    split; [exact Hp|]. split; [eapply keeps_trans; [exact Hk | exact Hk2]|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact H0|]. split; [exact H1 | exact H100].
Qed.

End scan.
