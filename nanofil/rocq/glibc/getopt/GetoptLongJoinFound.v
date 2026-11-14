From Glibc Require Import GlibcProgram.
(** When glibc's long-option parser finds an option for a word, it
    takes the option's argument, stores the option's index and returns
    the option's value, or it reports a misused option. Every way ends
    in a return. This file proves that those returns reach the state
    that the parser's caller expects after any return. *)

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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody GetoptLongJoinMiss.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongArg GetoptLongBody GetoptLongDiag GetoptLongExact GetoptLongJoinMiss GetoptLongPfxAlloc GetoptLongStore GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


(** The not-found returns module supplies the state after a return, the searches and the tactics. *)
Import GetoptLongJoinMiss GetoptLongBody GetoptLongAmbTail GetoptLongPfxAlloc GetoptLongStore GetoptLongDiag GetoptLongExact GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.


Import ProgramAbbreviations.
Section found_values.
Lemma long_arg_res s has i n cur a ps i' a' :
  long_arg s has i n cur a ps i' a' ->
  (i <= i' <= i + 1 \/ (i' = i + 2 /\ i + 1 < n)) /\
  (a' = a \/ a' = ptr_add cur (Z.of_nat (eq_len s) + 1) \/ a' = nth (Z.to_nat (i + 1)) ps null).
Proof.
  intros [(_ & _ & -> & ->) | [(_ & _ & -> & ->) | (_ & _ & Hlt & -> & ->)]].
  - split; [lia | right; left; reflexivity].
  - split; [lia | left; reflexivity].
  - split; [right; lia | right; right; reflexivity].
Qed.
End found_values.
Section found.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance jfound_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** When the parser takes an argument, it moves the index by at most
    two words and points the argument at the word or at the next word. *)

(** The parser found the entry x at index j for the word whose rest s
    starts at the cursor cur. Each of its four returns gives the caller
    the value v of the return and the state that plo_res describes. The
    value is -1 only when the entry has no flag and the value -1. *)
Lemma wp_long_join_found ks e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid3 mid4 av ar ps lo os j x pfx sp
    po so cur s i n pe oo a b r li F Φ :
  avoids ks larg_names = true -> avoids ks lreq_names = true -> avoids ks leq_names = true ->
  avoids ks lstore_names = true -> avoids ks ldiag_names = true -> getopt_ldiag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.143") (ge_globals ge) = Some mid3 ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid4 ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v4") e = Some (WPtr po) -> lookup (TAtom "v8") e = Some (WPtr li) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v14") e = Some (WInt pe) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "v90") e = Some (WInt 0) -> lookup (TAtom "pr.12") e = Some (WInt (Z.of_nat j)) ->
  lookup (TAtom "pr.7") e = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) ->
  lookup (TAtom "pr.1") e = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk1") e = Some (WPtr (ptr_add cur (Z.of_nat (eq_len s)))) ->
  os !! j = Some x -> (List.length os < 2 ^ 31)%Z -> lo_flag x = null \/ lo_flag x ∈ F ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx sp -∗ word_string DfracDiscarded po so -∗
  word_string DfracDiscarded cur s -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  (∀ e' l rv v, ⌜keeps ks e e' /\ value_x ge e' W rv = Some (WInt v)⌝ -∗
     plo_res b r av ar ps li F G M i n cur s a os v -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec l [] (JRet rv))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L87") (b_insts plo_blk87) (b_jump plo_blk87))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksq Hkse Hkst Hksd Hrule Hse Hmid3 Hmid4 H0 H2 H4 H8 H12 H14 H16 H90 Hp12 H7 Hp1 Hc0 Hc1 Hx Hos Hf
    Hi Hn Hlen Hpe Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hpfx #Hpo #Hws #Hsl #Hsc Hl Hib Hoob Hab Hcur Ha Hcl #Hs HG HF HM Hli HK".
  iApply (GetoptLongArg.wp_long_found ks e G T fp dom se sereg mid3 mid4 av ar ps lo os j x pfx sp po so cur s cur
    i n pe oo a b r li F with "Ht Hpfx Hpo Hws Hsl Hsc Hl Hib Hoob Hab Hcur Ha Hcl Hs HG Hli HF"); try assumption.
  iSplit; [|iSplit; [|iSplit]].
  - iIntros (e' i' a' (Hk' & Hla & _)) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hli HF".
    destruct (long_arg_res _ _ _ _ _ _ _ _ _ Hla) as [Hi' Ha'].
    iApply ("HK" $! e' _ (Const 0) 0 with "[%] [-]"); [split; [exact Hk' | reflexivity]|].
    iApply (plo_res_intro with "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM [Hli]");
      [exact Hi' | left; reflexivity | exact Ha' | lia | intros Hv; lia |].
    iDestruct "Hli" as "[%Hn0 | Hli]"; [by iLeft | iRight; iExists _; iExact "Hli"].
  - iIntros (e' i' a' (Hk' & Hla & Hfn & H511)) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hli HF".
    destruct (long_arg_res _ _ _ _ _ _ _ _ _ Hla) as [Hi' Ha'].
    iApply ("HK" $! e' _ (Tmp (TAtom "v511")) (lo_val x mod 2 ^ 32) with "[%] [-]");
      [split; [exact Hk' | cbn; rewrite H511; reflexivity]|].
    iApply (plo_res_intro with "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM [Hli]");
      [exact Hi' | left; reflexivity | exact Ha' | apply Z.mod_pos_bound; lia | intros Hv; right; exists x; split; [eapply list_elem_of_lookup_2; exact Hx | split; assumption] |].
    iDestruct "Hli" as "[%Hn0 | Hli]"; [by iLeft | iRight; iExists _; iExact "Hli"].
  - iIntros (e' (Hk' & _ & _)) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hli HF".
    iApply ("HK" $! e' _ (Const 63) 63 with "[%] [-]"); [split; [exact Hk' | reflexivity]|].
    iApply (plo_res_intro with "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli");
      [lia | left; reflexivity | left; reflexivity | lia | intros Hv; lia].
  - iIntros (e' (Hk' & _ & _ & _ & H484)) "Hl Hib Hoob Hab Hcur Ha Hcl HG Hli HF".
    iApply ("HK" $! e' _ (Tmp (TAtom "v484")) ((if sbyte so 0 =? 58 then 58 else 63) mod 2 ^ 32) with "[%] [-]");
      [split; [exact Hk' | cbn; rewrite H484; reflexivity]|].
    iApply (plo_res_intro with "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli");
      [lia | left; reflexivity | left; reflexivity | apply Z.mod_pos_bound; lia | intros Hv; exfalso; destruct (sbyte so 0 =? 58); vm_compute in Hv; discriminate Hv].
Qed.

End found.
