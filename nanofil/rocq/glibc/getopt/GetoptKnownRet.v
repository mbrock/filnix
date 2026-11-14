From Glibc Require Import GlibcProgram.
(** A short option ends glibc's scanner with a return. A known option
    answers with a byte that the option blocks chose, and an unknown
    option answers '?'. The getopt wrapper then copies the private index,
    the bad-option field and the argument into the public variables, so
    each return must hand over those fields and the evidence that the
    argument is usable. This file finishes those returns: it runs the
    known option's blocks and its return block up to the value returned,
    and it does the same for an unknown option. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor GetoptDiag GetoptReqTail GetoptReqNext
  GetoptShort GetoptOptArg GetoptReqArg GetoptShortOpt GetoptShortRet GetoptShortCap GetoptKnownCap.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptKnownCap
  GetoptShortCap GetoptShortRet GetoptState OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Transparent glibc_getopt_internal_r.

(** ## The returned byte

    The return block reads its value back as a signed byte and returns
    it as a 32-bit word. The controls below check that the answers ':'
    and '?' come back unchanged, and that a byte above 127 comes back
    sign-extended, as C's char conversion requires. *)

(** The answers ':' and '?' are ASCII, so they come back unchanged. *)
Lemma known_ret_ctl_ascii : chr_w 58 = 58 /\ chr_w 63 = 63.
Proof. split; reflexivity. Qed.

(** The byte 200 is negative as a signed char, so it returns as 2^32 - 56. *)
Lemma known_ret_ctl_high : chr_w 200 = 4294967240.
Proof. reflexivity. Qed.

Import GetoptShortCap GetoptKnownCap GetoptReqNext GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize
  GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section known_ret.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance knownret_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The return block returns the byte that the blocks before it stored. *)
Lemma wp_known_ret_value ks e fr v Φ :
  avoids ks ret_names = true ->
  ((fr = TAtom "L510" \/ fr = TAtom "L619") /\ lookup (TAtom "v455") e = Some (WInt v) \/
   fr = TAtom "L639" /\ lookup (TAtom "pr.7") e = Some (WInt v)) ->
  ▷ Φ (Ret (WInt (chr_w v))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L605") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hv. iIntros "HK".
  iApply (GetoptShortRet.wp_getopt_short_ret ks e fr v Φ with "[HK]"); [exact Hks | exact Hv |].
  iIntros (e' (_ & H696)). iApply wp_ret; [reflexivity | |].
  - unfold value_x. rewrite H696. cbn [word_at_class]. rewrite (Z.mod_small (chr_w v)); [reflexivity | apply chr_w_range].
  - iExact "HK".
Qed.

(** ## Returns of a known option

    The rule below runs a known option from its first test to its
    return. Only the W form leaves the choice before the return, and it
    keeps its own exit. Every other path returns, and the caller learns
    the returned value, the fields the wrapper copies, and the evidence
    for the argument. *)

(** A known option x at index k of the option string answers with the
    byte of its character c, except when a required argument is missing,
    where it answers ':' or '?' as the option string asks. Each return
    hands back the private index, the bad-option field and the argument
    with its evidence, together with every other resource the caller
    lent. The W form ends at its own block, as before. *)
Lemma wp_getopt_known_ret ks e i n c pe cur t po so k a lo oo b r av ar ps (G : iProp Σ) T fp dom se sereg mid Φ :
  avoids ks opt_names = true -> avoids ks req_names = true -> avoids ks diag_names = true ->
  avoids ks ret_names = true -> incl known_req_keys ks ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.149") (ge_globals ge) = Some mid ->
  lookup (TAtom "v0") e = Some (WInt n) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v80") e = Some (WInt 0) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "v459") e = Some (WPtr (ptr_add po (Z.of_nat k))) ->
  lookup (TAtom "pr.1") e = Some (WPtr po) ->
  lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk19") e = Some (WPtr po) ->
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk137") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  (k < List.length so)%nat -> 0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n -> sbyte t 0 <> 0 ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded cur t -∗ word_string DfracDiscarded po so -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
  pcell b 32 (ptr_add cur 1) -∗ live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ arg_cap a -∗
  ((∀ e', ⌜keeps ks e e' /\ sbyte so k = 87 /\ sbyte so (S k) = 59 /\ ptr_addr lo mod 2 ^ 64 <> 0⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L508") (Some (TAtom "L524")))) : gexpr)
        {{ Φ }}) ∧
   (⌜sbyte so (S k) <> 58⌝ -∗
      live b r -∗ int_cell b 0 (if sbyte t 1 =? 0 then i + 1 else i) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
      pcell b 32 (ptr_add cur 1) -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a -∗
      Φ (Ret (WInt (chr_w c)))) ∧
   (⌜sbyte so (S k) = 58 /\ sbyte so (S (S k)) = 58⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 oo -∗
      pcell b 16 (if sbyte t 1 =? 0 then null else ptr_add cur 1) -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap (if sbyte t 1 =? 0 then null else ptr_add cur 1) -∗
      Φ (Ret (WInt (chr_w c)))) ∧
   (⌜sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58 /\ sbyte t 1 <> 0⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 oo -∗ pcell b 16 (ptr_add cur 1) -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap (ptr_add cur 1) -∗
      Φ (Ret (WInt (chr_w c)))) ∧
   (⌜sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58 /\ sbyte t 1 = 0 /\ i + 1 < n⌝ -∗
      live b r -∗ int_cell b 0 (i + 2) -∗ int_cell b 8 oo -∗ pcell b 16 (nth (Z.to_nat (i + 1)) ps null) -∗
      pcell b 32 null -∗ live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap (nth (Z.to_nat (i + 1)) ps null) -∗
      Φ (Ret (WInt (chr_w c)))) ∧
   (⌜sbyte so (S k) = 58 /\ sbyte so (S (S k)) <> 58 /\ sbyte t 1 = 0 /\ (i + 1)%Z = n⌝ -∗
      live b r -∗ int_cell b 0 n -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a -∗
      Φ (Ret (WInt (chr_w (if sbyte so 0 =? 58 then 58 else 63)))))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L473") (Some (TAtom "L485")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hop Hrq Hdg Hrt Hinc Hdiag Hse Hmid H0 H2 H6 H12 H80 H455 H459 Hpr1 Hpr3 Hc0 Hc1 Hc2 Hc19 Hc20 H137
    Hk Hi Hn Hlen Ht0 Hc Hpe Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Hws #Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl #Hs HG Hca HK".
  assert (Hv455 : forall e', keeps ks e e' -> lookup (TAtom "v455") e' = Some (WInt c)).
  { intros e' Hk'. apply keeps_in with ks e; [exact Hk' | apply Hinc; cbn; repeat (first [left; reflexivity | right]) | exact H455]. }
  iApply (GetoptKnownCap.wp_getopt_known_cap ks e i n c pe cur t po so k a lo oo b r av ar ps G T fp dom se sereg mid Φ
            with "Hws Hpo Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG Hca [HK]"); try (assumption || lia).
  iSplit; [iDestruct "HK" as "[HK _]"; iExact "HK" |].
  iSplit; [|iSplit; [|iSplit; [|iSplit]]].
  - iDestruct "HK" as "[_ [HK _]]". iIntros (e' (Hk' & Hp)) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
    iApply (wp_known_ret_value ks e' (TAtom "L510") c); [exact Hrt | left; split; [left; reflexivity | exact (Hv455 e' Hk')] |].
    iNext. iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca"). exact Hp.
  - iDestruct "HK" as "[_ [_ [HK _]]]". iIntros (e' (Hk' & Hp)) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
    iApply (wp_known_ret_value ks e' (TAtom "L619") c); [exact Hrt | left; split; [right; reflexivity | exact (Hv455 e' Hk')] |].
    iNext. iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca"). exact Hp.
  - iDestruct "HK" as "[_ [_ [_ [HK _]]]]". iIntros (e' (H58 & H58' & Hk' & Ht1 & Hp7)) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
    iApply (wp_known_ret_value ks e' (TAtom "L639") c); [exact Hrt | right; split; [reflexivity | exact Hp7] |].
    iNext. iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca"). auto.
  - iDestruct "HK" as "[_ [_ [_ [_ [HK _]]]]]". iIntros (e' (H58 & H58' & Hk' & Ht1 & Hin & Hp7)) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
    iApply (wp_known_ret_value ks e' (TAtom "L639") c); [exact Hrt | right; split; [reflexivity | exact Hp7] |].
    iNext. iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca"). auto.
  - iDestruct "HK" as "[_ [_ [_ [_ [_ HK]]]]]". iIntros (e' (H58 & H58' & Hk' & Ht1 & Hin & Hp7)) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hca".
    iApply (wp_known_ret_value ks e' (TAtom "L639") (if sbyte so 0 =? 58 then 58 else 63));
      [exact Hrt | right; split; [reflexivity | exact Hp7] |].
    iNext. iApply ("HK" with "[%] Hl Hib Hoob Hab Hcur Ha Hcl HG Hca"). auto.
Qed.

(** ## The return of an unknown option

    An unknown option leaves the index, the argument and the cursor as
    they were, so the caller keeps those fields and the evidence for the
    argument. The report goes through the caller's rule, and the scanner
    returns '?'. *)

(** An unknown option c becomes the bad option and the scanner returns
    63, the code of '?'. The caller gets back the fields it kept and the
    evidence for the argument a, which the scanner did not touch. *)
Lemma wp_getopt_unknown_ret ks e fr c pe ix a cx oo b r av ar ps (G : iProp Σ) T fp dom se sereg mid Φ :
  avoids ks ret_names = true -> avoids ks diag_names = true ->
  getopt_diag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.148") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v455") e = Some (WInt c) ->
  lookup (TAtom "pr.3") e = Some (WInt pe) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  0 <= c < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 ix -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ pcell b 32 cx -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ arg_cap a -∗
  (live b r -∗ int_cell b 0 ix -∗ int_cell b 8 c -∗ pcell b 16 a -∗ pcell b 32 cx -∗
     live av ar -∗ argv_cells av ps -∗ G -∗ arg_cap a -∗ Φ (Ret (WInt 63))) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None (Enter (TAtom "L471") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksd Hrule Hse Hmid H2 H12 H455 Hpe Hc0 Hc Hper Hb Hal Hend Hr Hav Hala Hda Hra Hps
    Hse0 Hsea Hsee Hser.
  iIntros "Hsl Hsc Hl Hi Hoo Hab Hcur Ha Hcl Hs HG Hca HK".
  iApply (GetoptShortRet.wp_getopt_unknown ks e fr c pe oo b r av ar ps G T fp dom se sereg mid Φ
            with "Hsl Hsc Hl Hoo Ha Hcl Hs HG [Hi Hab Hcur Hca HK]"); try assumption.
  iIntros (e' _) "Hl Hoo Ha Hcl HG". iApply wp_ret; [reflexivity | reflexivity |].
  iNext. iApply ("HK" with "Hl Hi Hoo Hab Hcur Ha Hcl HG Hca").
Qed.

End known_ret.
