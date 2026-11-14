From Glibc Require Import GlibcProgram.
(** When glibc's long-option parser finds a word ambiguous without a set
    of the candidates, and its caller lets it print errors, its report
    is a single line that names the word. This file proves that line
    safe: the parser reads stderr, the program name and its cursor, and
    it writes the line only through the rule that its caller supplies.
    The tactic that writes the line also serves the line that announces
    a listing. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail GetoptLongAmbPrint GetoptLongAmbItem GetoptLongAmbList.
From Glibc Require FileInv GetoptArgv GetoptBytes GetoptDiag GetoptExchange GetoptInitialize GetoptLongAmbItem GetoptLongAmbList GetoptLongAmbPrint GetoptLongAmbTail GetoptLongDiag GetoptLongExact GetoptLongPfxAlloc GetoptLongPfxCmp GetoptLongPfxEnd GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxMark GetoptLongPfxSet GetoptLongPfxStep GetoptLongScan GetoptLongStore GetoptReqTail GetoptState LibioLogic OsWorld StrlenLoop.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The first line of the report assigns these names. *)
Definition arep_names : list name := Eval vm_compute in
  List.map TAtom ["v247"; "chk19"; "v248"; "v249"; "v250"; "v251"; "chk20"; "v254"; "v257"; "chk21"; "v258"; "v259";
    "v260"; "chk22"; "v261"; "v262"; "v263"; "v264"; "chk23"; "v267"; "v270"; "chk24"; "v271"; "v272"]%string.


(** The listing module supplies the listing, the last steps, the set and the tactics. *)
Import GetoptLongAmbList GetoptLongAmbItem GetoptLongAmbPrint GetoptLongAmbTail GetoptLongPfxEnd GetoptLongPfxLoop GetoptLongPfxIter GetoptLongPfxStep GetoptLongPfxSet GetoptLongPfxAlloc GetoptLongPfxMark GetoptLongPfxCmp GetoptLongStore GetoptLongDiag GetoptLongExact GetoptLongScan GetoptReqTail GetoptDiag GetoptExchange GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes GetoptArgv.

(** This tactic shows that the message of a report is one of the five. *)
Ltac arep_msg := unfold ldiag_msg; repeat first [apply List.Exists_cons_hd; eassumption | apply List.Exists_cons_tl].

(** This tactic writes the report's first line: it reads stderr,
    translates the message, reads the program name and the cursor, and
    writes the translation with the prefix and the rest of the word. *)
Ltac arep_head w0 registry ge Hlend Hfp Hgt Hfx M :=
  step; step;
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hsl");
    [reflexivity | vx | left; reflexivity | StrlenLoop.arith | StrlenLoop.arith | StrlenLoop.arith |];
  iNext; iIntros "_";
  iDestruct (Hlend with "HG") as (dq freg) "[Hcf HG]";
  iApply (wp_raw_load_pointer_dq with "Hsl Hsc Hcf"); [reflexivity | vx | left; reflexivity | StrlenLoop.arith | StrlenLoop.arith | exact Hfp |];
  iNext; iIntros "_ _ Hcf"; iSpecialize ("HG" with "Hcf"); step; step;
  iApply (Hgt _ _ _ _ _ _ _ _ M with "HG"); [arep_msg | vx |]; iNext; iIntros (q) "HT";
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Ha");
    [reflexivity | vx | left; reflexivity | StrlenLoop.arith | StrlenLoop.arith | StrlenLoop.arith |];
  iNext; iIntros "Ha"; iDestruct "Hcl" as "[Hc0 Hcl]";
  iApply (wp_raw_load_pointer_dq with "Ha Hc0 Hcapq"); [reflexivity | vx | left; reflexivity | StrlenLoop.arith | StrlenLoop.arith | lia |];
  iNext; iIntros "Ha Hc0 _"; step; check "Hl";
  iApply (wp_raw_load_pointer_dq with "Hl Hcur Hcapc"); [reflexivity | vx | left; reflexivity | StrlenLoop.arith | StrlenLoop.arith | lia |];
  iNext; iIntros "Hl Hcur _";
  iApply (Hfx _ _ _ _ _ _ _ _ M with "HT Hw0 Hpfx Hwc"); [arep_msg | vx |];
  iNext; iIntros (r0) "HG"; step.

Import ProgramAbbreviations.
Section head.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the parser's safepoints. *)
Local Instance ahead_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This line tells the user that the word is ambiguous. The parser
    reads the program name and the rest of the word, and it writes them
    with the prefix through the message str.138. Then it goes on to give
    the set back. The line keeps the vector and the cursor, and it gives
    G back. *)
Lemma wp_amb_head138 ks e fr (G : iProp Σ) T fp dom se sereg mid av ar ps pfx pxs cur s b r Φ :
  avoids ks arep_names = true -> getopt_ldiag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.138") (ge_globals ge) = Some mid ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) -> lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v16") e = Some (WPtr pfx) -> lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 <= r_end ar -> r_end ar <= 2 ^ 48 -> ps <> [] ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  word_string DfracDiscarded pfx pxs -∗ word_string DfracDiscarded cur s -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗ live b r -∗ pcell b 32 cur -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗ live b r -∗ pcell b 32 cur -∗ live av ar -∗ argv_cells av ps -∗ G -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L241") (Some (TAtom "L243")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L243") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hrule Hse Hmid H2 H12 H16 Hc0 Hb Hal Hend Hr Hav Hala Hda Hra Hps Hse0 Hsea Hsee Hser.
  pose proof Hrule as (Hdom & Hfp & Hlend & Hgt & Hfx & _).
  iIntros "#Hpfx #Hwc #Hsl #Hsc Hl Hcur Ha Hcl #Hargs HG HK".
  iDestruct (argv_str_cap with "Hwc") as (rc) "[#Hcapc %Hc0']".
  destruct ps as [|q0 ps']; [congruence|].
  iAssert (∃ s0, word_string DfracDiscarded q0 s0)%I as (s0) "#Hw0";
    [unfold argv_strs; rewrite big_sepL_cons; iDestruct "Hargs" as "[H _]"; iExact "H"|].
  iDestruct (argv_str_cap with "Hw0") as (rq) "[#Hcapq %Hq0]".
  arep_head w0 registry ge Hlend Hfp Hgt Hfx mid.
  iApply ("HK" with "[%] Hl Hcur Ha [Hc0 Hcl] HG"); [xkeep | iFrame].
Qed.

End head.
