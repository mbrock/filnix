From Glibc Require Import GlibcProgram.
(** When glibc's long-option parser finds no option for a word and
    may not leave the word to the short options, it reports the word as
    unrecognized on stderr when its caller lets it print errors. Then it
    steps the index past the word, clears its cursor, stores 0 as the
    bad option and answers '?'. This file proves that report and those
    stores safe. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From stdpp Require Import list.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString StrlenBits StrlenLogic StrlenLoop StrlenWord
  StrncmpCode StrcmpBits StrcmpLoop StrncmpBits StrncmpLoop StrncmpWords StrncmpLogic
  GetoptModule GetoptState GetoptBytes GetoptInitialize GetoptEntry GetoptArgv GetoptExchange GetoptCursor
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre GetoptLongArg.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongArg GetoptLongDiag GetoptLongEq GetoptLongExact GetoptLongPre GetoptLongReq GetoptLongScan GetoptLongStore GetoptLongTail GetoptReqTail GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The report and its stores assign these names. *)
Definition lunrec_names : list name := Eval vm_compute in
  List.map TAtom ["v368"; "chk40"; "v369"; "v370"; "v371"; "v372"; "chk41"; "v375"; "v378"; "chk42"; "v379"; "v380";
    "v382"; "chk43"; "chk44"; "v384"; "v385"; "chk45"; "v387"; "chk46"]%string.


(** The found-option module supplies the option table, the report rule and the tactics. *)
Import GetoptLongArg GetoptLongPre GetoptLongEq GetoptLongReq GetoptLongTail GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic shows that the message of a report is one of the five. *)
Ltac lmsg := unfold ldiag_msg; repeat first [apply List.Exists_cons_hd; eassumption | apply List.Exists_cons_tl].

Import ProgramAbbreviations.
Section unrec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance unrec_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser reports the word whose name starts at the cursor cur as
    unrecognized when it prints errors. The report reads the stream
    pointer from the global stderr, the program name from the first
    entry of the vector and the cursor from the parser's own field, and
    it writes the message str.142 with the prefix pfx and the rest of
    the word. Then the parser steps the index from i to i + 1, clears
    the cursor and stores 0 as the bad option. The report keeps G. *)
Lemma wp_long_unrec ks e fr (G : iProp Σ) T fp dom se sereg mid av ar ps pfx sp cur s i pe oo b r Φ :
  avoids ks lunrec_names = true -> getopt_ldiag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.142") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v14") e = Some (WInt pe) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 <= i < 2 ^ 31 - 1 -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded pfx sp -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗
     live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 0 -∗ pcell b 32 null -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L366") [] (JRet (Const 63)))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L332") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hrule Hse Hmid H2 H12 H14 H16 Hc0 Hi Hpe Hb Hal Hend Hr Hav Hala Hda Hra Hps Hse0 Hsea Hsee Hser.
  iIntros "#Hpfx #Hwc #Hsl #Hsc Hl [%Hi0 Hib] [%Hoo Hoob] Hcur Ha Hcl #Hs HG HK".
  iDestruct (argv_str_cap with "Hwc") as (rc) "[#Hcapc %Hc0']".
  iAssert (∀ e1 fr1, ⌜keeps ks e e1 /\ lookup (TAtom "v12") e1 = Some (WPtr (mkPtr b (Obj b))) /\
      lookup (TAtom "chk0") e1 = Some (WPtr (mkPtr (b + 32) (Obj b)))⌝ -∗
    live b r -∗ pcell b 32 cur -∗ live av ar -∗ argv_cells av ps -∗ G -∗
    WP (ERun (mkFrame glibc_process_long_option e1 [] None (Enter (TAtom "L366") (Some fr1))) : gexpr) {{ Φ }})%I
    with "[Hib Hoob HK]" as "HL366".
  { iIntros (e1 fr1 (Hk1 & H12' & Hc0'')) "Hl Hcur Ha Hcl HG".
    step. step. check "Hl".
    store_pointer "Hl Hcur" by (StrlenLoop.arith) preserving wi_store.
    iNext. iIntros "Hl Hcur". check "Hl". load_s32_using ltac:(arith) "Hl Hib". step. norm. check "Hl".
    store_word "Hl Hib" by (StrlenLoop.arith) preserving wi_store.
    iNext. iIntros "Hl Hib". step. check "Hl".
    store_word "Hl Hoob" by (StrlenLoop.arith) preserving wi_store.
    iNext. iIntros "Hl Hoob".
    rewrite (Z.mod_small (i + 1) (2 ^ 32)); [|lia]. change (0 mod 2 ^ 64) with 0. fold null.
    iApply ("HK" with "[%] Hl [Hib] [Hoob] Hcur Ha Hcl HG");
      [eapply keeps_trans; [exact Hk1|]; xkeep | iSplit; [iPureIntro; lia | iExact "Hib"]
      | iSplit; [iPureIntro; lia | iExact "Hoob"]]. }
  step. iApply wp_branch; [vx | iNext]. rewrite (Z.mod_small pe (2 ^ 32)); [|lia].
  destruct (Z.eqb_spec pe 0) as [Ep | Ep]; cbn [edge_label].
  { iApply ("HL366" with "[%] Hl Hcur Ha Hcl HG"). split; [xkeep|]. split; lk_prove. }
  destruct Hrule as (Hdom & Hfp & Hlend & Hgt & Hfx & _).
  destruct ps as [|q0 ps']; [congruence|].
  iAssert (∃ s0, word_string DfracDiscarded q0 s0)%I as (s0) "#Hw0";
    [unfold argv_strs; rewrite big_sepL_cons; iDestruct "Hs" as "[H _]"; iExact "H"|].
  iDestruct (argv_str_cap with "Hw0") as (rq) "[#Hcapq %Hq0]".
  step. step.
  check_read_dq "Hsl" by StrlenLoop.arith.
  iNext; iIntros "_".
  iDestruct (Hlend with "HG") as (dq freg) "[Hcf HG]".
  load_pointer_dq "Hsl Hsc Hcf" by StrlenLoop.arith.
  iNext; iIntros "_ _ Hcf"; iSpecialize ("HG" with "Hcf"). step. step.
  iApply (Hgt with "HG"); [lmsg | vx |]. iNext; iIntros (q) "HT".
  check_read_dq "Ha" by StrlenLoop.arith.
  iNext; iIntros "Ha"; iDestruct "Hcl" as "[Hc0 Hcl]".
  load_pointer_dq "Ha Hc0 Hcapq" by StrlenLoop.arith.
  iNext; iIntros "Ha Hc0 _". step. check "Hl".
  load_pointer_dq "Hl Hcur Hcapc" by StrlenLoop.arith.
  iNext. iIntros "Hl Hcur _".
  iApply (Hfx with "HT Hw0 Hpfx Hwc"); [lmsg | vx |].
  iNext; iIntros (r0) "HG". step.
  iApply ("HL366" with "[%] Hl Hcur Ha [Hc0 Hcl] HG"); [split; [xkeep|]; split; lk_prove | iFrame].
Qed.

End unrec.
