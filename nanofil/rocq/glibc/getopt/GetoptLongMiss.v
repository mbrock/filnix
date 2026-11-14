From Glibc Require Import GlibcProgram.
(** When glibc's long-option parser finds no option for a word, it
    still has two ways out. In long-only mode a word such as "-x" may be
    a short option, so the parser returns -1 and lets the caller try the
    short options when the first character of the name is one of them.
    Otherwise the parser reports an unrecognized option on stderr, steps
    the index past the word, clears its cursor, stores 0 as the bad
    option and answers '?'. This file proves that path safe: it reads
    the word, the option string and the vector only inside them, and it
    writes only the parser's own private fields. *)

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
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg GetoptLongUnrec GetoptLongMissOnly.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongArg GetoptLongDiag GetoptLongEq GetoptLongExact GetoptLongMissOnly GetoptLongPre GetoptLongReq GetoptLongScan GetoptLongStore GetoptLongTail GetoptLongUnrec GetoptReqTail GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The not-found test assigns these names before the long-only test. *)
Definition lmiss_names : list name := Eval vm_compute in
  List.map TAtom ["v329"; "v331"; "v336"; "v350"; "v363"]%string.

(** The long-only test keeps these names for the report after it. *)
Definition lmiss_keys : list name := Eval vm_compute in
  List.map TAtom ["v2"; "v12"; "v14"; "v16"; "chk0"]%string.

(** The parser reads the second byte of the word at the index only in
    long-only mode, so the word needs a first byte only in that mode. The
    W option calls the parser with long-only mode off, and the next word
    that it passes may be empty. These three controls show what the
    condition allows. With long-only mode off, an empty word meets it. *)
Lemma miss_word_ctl_off : (0 <> 0 -> sbyte [] 0 <> 0)%Z.
Proof. lia. Qed.

(** In long-only mode an empty word fails the condition. *)
Lemma miss_word_ctl_empty : ~ (1 <> 0 -> sbyte [] 0 <> 0)%Z.
Proof. unfold sbyte. cbn. lia. Qed.

(** In long-only mode a word that starts with a dash meets the condition. *)
Lemma miss_word_ctl_dash : (1 <> 0 -> sbyte [45] 0 <> 0)%Z.
Proof. unfold sbyte. cbn. lia. Qed.


(** The long-only module supplies the long-only test, the report, the option table and the tactics. *)
Import GetoptLongMissOnly GetoptLongUnrec GetoptLongArg GetoptLongPre GetoptLongEq GetoptLongReq GetoptLongTail GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

Import ProgramAbbreviations.
Section miss.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance miss_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser found no entry for the name at the cursor cur. The name
    lies in the word q at index i. In long-only mode the parser may
    return -1 without a write and leave the word to the short options.
    Otherwise it reports the word as unrecognized. Then it steps the
    index past the word and clears its cursor. It stores 0 as the bad
    option and answers '?'. The report keeps G. The parser reads the
    word q only in long-only mode, so q needs a first byte only then. *)
Lemma wp_long_miss ks e (G : iProp Σ) T fp dom se sereg mid av ar ps q sq po so pfx sp cur s i n lonly pe oo b r Φ :
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
  ps !! Z.to_nat i = Some q -> (lonly <> 0 -> sbyte sq 0 <> 0) ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n -> 0 <= lonly < 2 ^ 32 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded q sq -∗ word_string DfracDiscarded po so -∗ word_string DfracDiscarded pfx sp -∗
  word_string DfracDiscarded cur s -∗ liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  ((∀ e', ⌜keeps ks e e'⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 0 -∗ pcell b 32 null -∗ live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L366") [] (JRet (Const 63)))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ lonly <> 0⌝ -∗
      live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗ live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L334") [] (JRet (Const 4294967295))))
        : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L87") (b_insts plo_blk87) (b_jump plo_blk87))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hkso Hksu Hrule Hg Hgn Hse Hmid H2 H4 H10 H12 H14 H16 H90 H7 Hc0 Hq Hq0 Hi Hn Hlen Hlo Hpe
    Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  iIntros "#Hwq #Hpo #Hpfx #Hws #Hsl #Hsc Hl Hib Hoo Hcur Ha Hcl #Hs HG HK".
  assert (Hps : ps <> []) by (intros ->; cbn in Hlen; lia).
  let K := lazymatch iTypeOf "HK" with Some (_, ?P) => P end in
  iAssert (∀ e1 fr1, ⌜keeps ks e e1 /\ lookup (TAtom "v2") e1 = Some (WPtr (mkPtr av (Obj av))) /\
      lookup (TAtom "v12") e1 = Some (WPtr (mkPtr b (Obj b))) /\ lookup (TAtom "v14") e1 = Some (WInt pe) /\
      lookup (TAtom "v16") e1 = Some (WPtr pfx) /\ lookup (TAtom "chk0") e1 = Some (WPtr (mkPtr (b + 32) (Obj b)))⌝ -∗
    live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗ live av ar -∗ argv_cells av ps -∗ G -∗ K -∗
    WP (ERun (mkFrame glibc_process_long_option e1 [] None (Enter (TAtom "L332") (Some fr1))) : gexpr) {{ Φ }})%I
    as "HL332".
  { iIntros (e1 fr1 (Hk1 & H2' & H12' & H14' & H16' & Hc0'')) "Hl Hib Hoo Hcur Ha Hcl HG HK".
    iApply (wp_long_unrec ks e1 fr1 G T fp dom se sereg mid av ar ps pfx sp cur s i pe oo b r
      with "Hpfx Hws Hsl Hsc Hl Hib Hoo Hcur Ha Hcl Hs HG");
      [exact Hksu | exact Hrule | exact Hse | exact Hmid | exact H2' | exact H12' | exact H14' | exact H16' | exact Hc0''
      | lia | exact Hpe | exact Hb | exact Hal | exact Hend | exact Hr | exact Hav | exact Hala | lia | exact Hra
      | exact Hps | exact Hse0 | exact Hsea | exact Hsee | exact Hser |].
    iIntros (e2 Hk2) "Hl Hib Hoo Hcur Ha Hcl HG". iDestruct "HK" as "[HK _]".
    iApply ("HK" with "[%] Hl Hib Hoo Hcur Ha Hcl HG"). eapply keeps_trans; [exact Hk1 | exact Hk2]. }
  cbn [b_insts b_jump plo_blk87]. step. step. unfold null; cbn [ptr_addr].
  iApply wp_branch; [vx | iNext]. close_br.
  step. step. iApply wp_branch; [vx | iNext]. rewrite (Z.mod_small lonly (2 ^ 32)); [|lia]. change (0 mod 2 ^ 32) with 0.
  destruct (Z.eqb_spec lonly 0) as [El | El]; cbn [edge_label].
  { step. iApply wp_branch; [vx | iNext]. close_br. step. iApply wp_branch; [vx | iNext]. close_br.
    iApply ("HL332" with "[%] Hl Hib Hoo Hcur Ha Hcl HG HK"). split; [xkeep|]. repeat split; lk_prove. }
  iApply (wp_long_miss_only (lmiss_keys ++ ks) _ cur s q sq po so i n b r av ar ps with "Hwq Hpo Hws Hl Hib Hcur Ha Hcl");
    [rewrite avoids_app_l; rewrite Hkso; vm_compute; reflexivity | exact Hg | exact Hgn | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | exact Hq | exact (Hq0 El) | exact Hi
    | exact Hn | exact Hlen | exact Hb | exact Hal | exact Hend | exact Hr | exact Hav | exact Hala | exact Hda
    | exact Hra |].
  iSplit.
  - iIntros (e1 fr1 Hk1) "Hl Hib Hcur Ha Hcl". apply keeps_app in Hk1 as [Hkt Hk1].
    iApply ("HL332" with "[%] Hl Hib Hoo Hcur Ha Hcl HG HK"). split; [eapply keeps_trans; [|exact Hk1]; xkeep|].
    repeat split; viakeep Hkt.
  - iIntros (e1 Hk1) "Hl Hib Hcur Ha Hcl". apply keeps_app in Hk1 as [_ Hk1]. iDestruct "HK" as "[_ HK]".
    iApply ("HK" with "[%] Hl Hib Hoo Hcur Ha Hcl HG"). split; [eapply keeps_trans; [|exact Hk1]; xkeep | exact El].
Qed.

End miss.
