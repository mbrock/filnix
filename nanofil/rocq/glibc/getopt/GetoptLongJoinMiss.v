(** When glibc's long-option parser finds no option for a word, it
    either reports the word as unrecognized and skips it, or, in
    long-only mode, leaves the word to the short options. Both ways end
    in a return. This file states what the parser holds after any of its
    returns, and it proves that the not-found returns reach that state. *)

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
  GetoptLongAmbHead GetoptLongAmbPoss GetoptLongAmbRep GetoptLongPfxPath GetoptLongFind GetoptLongBody.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptExchange GetoptInitialize GetoptLongAmbTail GetoptLongBody GetoptLongDiag GetoptLongExact GetoptLongMiss GetoptLongPfxAlloc GetoptLongStore GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


(** The entry module supplies the searches, the reports, the set and the tactics. *)
Import GetoptLongBody GetoptLongAmbTail GetoptLongPfxAlloc GetoptLongStore GetoptLongDiag GetoptLongExact GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.


Section res.
Context `{!gen_heapGS piece pval Σ}.

(** The caller of the parser must know what it holds after a return,
    whichever return the parser took. It gets back everything it lent:
    the parser's private object, the vector, the report resource, the
    flag targets, the allocator state and the longind target. The index
    moves forward by at most two words, and by two only when a word
    remains for an argument. The cursor is null, or it stays with the
    index, or it points at the end of the word. The argument stays,
    points after the equals sign, or points at the next word. The return
    value x lies below 2^32. A value of -1 means that the parser left
    the word to the short options, with the cursor and the index
    unchanged, unless an entry of the table os has no flag and the
    value -1. *)
Definition plo_res (b : Z) (r : region) (av : Z) (ar : region) (ps : list ptr) (li : ptr) (F : list ptr)
    (G M : iProp Σ) (i n : Z) (cur : ptr) (s : list Z) (a : ptr) (os : list lopt) (x : Z) : iProp Σ :=
  ∃ i' oo' a' c', live b r ∗ int_cell b 0 i' ∗ int_cell b 8 oo' ∗ pcell b 16 a' ∗ pcell b 32 c' ∗
    live av ar ∗ argv_cells av ps ∗ G ∗ flags_own F ∗ M ∗ longind_own li ∗
    ⌜((i <= i' <= i + 1 \/ (i' = i + 2 /\ i + 1 < n)) /\
      (c' = null \/ (c' = cur /\ i' = i) \/ c' = ptr_add cur (Z.of_nat (List.length s))) /\
      (a' = a \/ a' = ptr_add cur (Z.of_nat (eq_len s) + 1) \/ a' = nth (Z.to_nat (i + 1)) ps null) /\
      0 <= x < 2 ^ 32 /\ (x = 4294967295 -> (c' = cur /\ i' = i) \/
        exists y, y ∈ os /\ lo_flag y = null /\ lo_val y mod 2 ^ 32 = 4294967295))%Z⌝.

(** The pieces that a return leaves, with the three facts about the new
    index, cursor and argument, make up that state. *)
Lemma plo_res_intro b r av ar ps li F (G M : iProp Σ) i n cur s a os x i' oo' a' c' :
  (i <= i' <= i + 1 \/ (i' = i + 2 /\ i + 1 < n))%Z ->
  c' = null \/ (c' = cur /\ i' = i) \/ c' = ptr_add cur (Z.of_nat (List.length s)) ->
  a' = a \/ a' = ptr_add cur (Z.of_nat (eq_len s) + 1) \/ a' = nth (Z.to_nat (i + 1)) ps null ->
  (0 <= x < 2 ^ 32)%Z -> (x = 4294967295 -> (c' = cur /\ i' = i) \/
    exists y, y ∈ os /\ lo_flag y = null /\ lo_val y mod 2 ^ 32 = 4294967295)%Z ->
  live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo' -∗ pcell b 16 a' -∗ pcell b 32 c' -∗
  live av ar -∗ argv_cells av ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  plo_res b r av ar ps li F G M i n cur s a os x.
Proof.
  intros Hi Hc Ha Hr Hx. iIntros "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli".
  iExists i', oo', a', c'. iFrame. iPureIntro. auto.
Qed.

End res.

Section miss.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance jmiss_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance jmiss_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser found no option for the word q at index i. Each of its
    two returns gives the caller the value x of the return and the state
    that plo_res describes. *)
Lemma wp_long_join_miss ks e (G : iProp Σ) T fp dom (M : iProp Σ) se sereg mid av ar ps q sq po so pfx sp cur s
    i n lonly pe oo a li F b r os Φ :
  avoids ks lmiss_names = true -> avoids ks lonly_names = true -> avoids ks lunrec_names = true ->
  getopt_ldiag_rule w0 registry ge G T fp dom ->
  find_fn ge (TAtom "__GI_strchr") = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup (TAtom "v4") e = Some (WPtr po) ->
  lookup (TAtom "v10") e = Some (WInt lonly) -> lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v14") e = Some (WInt pe) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "v90") e = Some (WInt 0) -> lookup (TAtom "pr.7") e = Some (WPtr null) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  ps !! Z.to_nat i = Some q -> sbyte sq 0 <> 0 ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n -> 0 <= lonly < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗ word_string DfracDiscarded pfx sp -∗
  word_string DfracDiscarded cur s -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ flags_own F -∗ M -∗ longind_own li -∗
  (∀ e' l rv x, ⌜keeps ks e e' /\ value_x ge e' W rv = Some (WInt x)⌝ -∗
     plo_res b r av ar ps li F G M i n cur s a os x -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec l [] (JRet rv))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L87") (b_insts plo_blk87) (b_jump plo_blk87))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hkso Hksu Hrule Hg Hgn Hse Hmid H2 H4 H10 H12 H14 H16 H90 H7 Hc0 Hq Hq0 Hi Hn Hlen Hlo Hpe
    Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Hwq #Hpo #Hpfx #Hws #Hsl #Hsc Hl Hib Hoob Hab Hcur Ha Hcl #Hs HG HF HM Hli HK".
  iApply (GetoptLongMiss.wp_long_miss w0 registry ge ks e G T fp dom se sereg mid av ar ps q sq po so pfx sp cur s i n lonly pe oo b r
    with "Hwq Hpo Hpfx Hws Hsl Hsc Hl Hib Hoob Hcur Ha Hcl Hs HG"); try assumption.
  iSplit.
  - iIntros (e' Hk') "Hl Hib Hoob Hcur Ha Hcl HG".
    iApply ("HK" $! e' _ (Const 63) 63 with "[%] [-]"); [split; [exact Hk' | reflexivity]|].
    iApply (plo_res_intro with "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli"); [lia | left; reflexivity | left; reflexivity | lia | intros Hx; lia].
  - iIntros (e' (Hk' & Hlo')) "Hl Hib Hoob Hcur Ha Hcl HG".
    iApply ("HK" $! e' _ (Const 4294967295) 4294967295 with "[%] [-]"); [split; [exact Hk' | reflexivity]|].
    iApply (plo_res_intro with "Hl Hib Hoob Hab Hcur Ha Hcl HG HF HM Hli");
      [lia | right; left; split; reflexivity | left; reflexivity | lia | intros _; left; split; reflexivity].
Qed.

End miss.
