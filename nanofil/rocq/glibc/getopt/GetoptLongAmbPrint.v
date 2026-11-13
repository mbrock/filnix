(** When glibc's long-option parser lists the candidates of an
    ambiguous word, it writes the name of each marked entry on stderr.
    This file proves one such write safe: the parser reads the stream
    pointer and the entry's name, and it writes them only through the
    report rule that its caller supplies. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The write of one candidate assigns these names. *)
Definition aprint_names : list name := Eval vm_compute in
  List.map TAtom ["v288"; "chk26"; "v289"; "v290"; "v295"; "v296"; "chk27"; "v297"; "v298"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongAmbPrintOn (R : Runtime) (LG0 : LogicSig R).
(** The tail module supplies the set, the option table, the report rule and the tactics. *)
Module LAT := GetoptLongAmbTailOn R LG0.
Import LAT LAT.LPE LAT.LPE.LPL LAT.LPE.LPL.LPI LAT.LPE.LPL.LPI.LPT LAT.LPE.LPL.LPI.LPT.LPS LAT.LPE.LPL.LPI.LPT.LPS.LPA LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.


Section print.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance aprint_stable : SafepointStable (os_wi w0) := LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance aprint_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser writes the name of the entry y at index k with the
    prefix pfx through the format str.140. It reads the stream pointer
    from the global stderr and the name from the option table, which the
    caller shares. The write gives G back. *)
Lemma wp_amb_print ks e fr (G : iProp Σ) T fp dom se sereg f140 lo os pfx ps (k : nat) y Φ :
  avoids ks aprint_names = true -> getopt_ldiag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "v6") e = Some (WPtr lo) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "v285") e = Some (WInt (Z.of_nat k)) -> os !! k = Some y -> (List.length os < 2 ^ 31)%Z ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx ps -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗ G -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L275") (Some (TAtom "L280")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L280") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hrule Hse H140 H6 H16 H285 Hy Hos Hse0 Hsea Hsee Hser.
  pose proof Hrule as (Hdom & Hfp & Hlend & Hgt & Hfx & Hf4 & Hf5).
  pose proof (lookup_lt_Some _ _ _ Hy) as Hk.
  iIntros "#Ht #Hpfx #Hsl #Hsc HG HK".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & #Hnul)".
  destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iDestruct (big_sepL_lookup with "Hes") as "(#Hn & #Hnws & _)"; [exact Hy|].
  iDestruct (argv_str_cap with "Hnws") as (rn) "[#Hcapn %Hn0]".
  en. st.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hsl");
    [reflexivity | vx | left; reflexivity | arith | arith | arith |].
  iNext; iIntros "_".
  iDestruct (Hlend with "HG") as (dq freg) "[Hcf HG]".
  iApply (wp_raw_load_pointer_dq with "Hsl Hsc Hcf"); [reflexivity | vx | left; reflexivity | arith | arith | exact Hfp |].
  iNext; iIntros "_ _ Hcf"; iSpecialize ("HG" with "Hcf"). st. st. st. norm.
  change (2 ^ (5 mod 64)) with 32.
  match goal with |- context [put (TAtom "v296") (WPtr {| ptr_addr := ?X; ptr_cap := ptr_cap lo |})] =>
    replace X with (ptr_addr lo + 32 * Z.of_nat k) by (rewrite !Z.mod_small; lia) end.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Htl");
    [reflexivity | vx | exact Htc | rawa | rawa | al8 |]; iNext; iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Htl Hn Hcapn");
    [reflexivity | vx | exact Htc | rawa | al8 | exact Hn0 |].
  iNext. iIntros "_ _ _".
  iApply (Hf4 with "HG Hpfx Hnws"); [exact H140 | vx |]. iNext. iIntros (r0) "HG". st.
  iApply ("HK" with "[%] HG"). xkeep.
Unshelve. all: first [exact treg | exact DfracDiscarded | idtac].
Qed.

End print.
End GetoptLongAmbPrintOn.
