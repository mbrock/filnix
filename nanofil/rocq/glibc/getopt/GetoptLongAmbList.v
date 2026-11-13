(** When glibc's long-option parser finds several options whose names
    start with a word's name, it reports the word as ambiguous and lists
    the candidates on stderr. The set that the prefix search built marks
    each candidate with a nonzero byte. This file proves the listing
    safe: the parser reads each byte of the set and the name of each
    marked entry of the option table, and it writes them only through
    the report rule that its caller supplies. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail GetoptLongAmbPrint GetoptLongAmbItem.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongAmbListOn (R : Runtime) (LG0 : LogicSig R).
(** The step module supplies one step of the listing, the set, the option table and the tactics. *)
Module LAI := GetoptLongAmbItemOn R LG0.
Import LAI LAI.LAP LAI.LAP.LAT LAI.LAP.LAT.LPE LAI.LAP.LAT.LPE.LPL LAI.LAP.LAT.LPE.LPL.LPI LAI.LAP.LAT.LPE.LPL.LPI.LPT LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.


Section list.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance alist_stable : SafepointStable (os_wi w0) := LAI.LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance alist_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser lists the candidates from entry k on. It reads the byte
    of each entry in the set sb and, when the byte is not 0, writes the
    entry's name with the prefix pfx through the format str.140. After
    the last entry it ends the line with the format str.141 and goes on
    to give the set back. The listing keeps the set's bytes, and every
    write gives G back. *)
Lemma wp_amb_list ks e (G : iProp Σ) T fp dom se sereg f140 f141 lo os pfx ps (k : nat) sb sreg xs Φ :
  avoids ks alist_names = true -> getopt_ldiag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "glibc_getopt#str.141") (ge_globals ge) = Some f141 ->
  lookup (TAtom "v6") e = Some (WPtr lo) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "pr.9") e = Some (WInt (Z.of_nat (List.length os))) ->
  lookup (TAtom "pr.10") e = Some (WInt (Z.of_nat k)) ->
  lookup (TAtom "pr.21") e = Some (WPtr (mkPtr sb (Obj sb))) ->
  (k <= List.length os)%nat -> (List.length os < 2 ^ 31)%Z -> List.length xs = List.length os ->
  0 < sb -> sb + Z.of_nat (List.length os) <= r_end sreg -> r_end sreg <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx ps -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live sb sreg -∗ bytes sb 0 xs -∗ G -∗
  (∀ e', ⌜keeps ks e e'⌝ -∗ live sb sreg -∗ bytes sb 0 xs -∗ G -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L241") (Some (TAtom "L276")))) : gexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L273") (b_insts plo_blk273) (b_jump plo_blk273))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hrule Hse H140 H141.
  remember (List.length os - k)%nat as d eqn:Hd. revert e k Hd.
  induction d as [d IH] using (well_founded_induction lt_wf).
  intros e k Hd H6 H16 H9 H10 H21 Hk Hos Hxs Hsb Hse' Hsr Hse0 Hsea Hsee Hser.
  pose proof Hrule as (Hdom & Hfp & Hlend & Hgt & Hfx & Hf4 & Hf5).
  iIntros "#Ht #Hpfx #Hsl #Hsc Hl Hx HG HK".
  destruct (Nat.lt_ge_cases k (List.length os)) as [Hlt | Hge].
  { iApply (wp_amb_item w0 registry ge ks e G T fp dom se sereg f140 lo os pfx ps k sb sreg xs
      with "Ht Hpfx Hsl Hsc Hl Hx HG");
      [exact Hks | exact Hrule | exact Hse | exact H140 | exact H6 | exact H16 | exact H9 | exact H10 | exact H21
      | exact Hlt | exact Hos | exact Hxs | exact Hsb | exact Hse' | exact Hsr | exact Hse0 | exact Hsea | exact Hsee
      | exact Hser |].
    iIntros (e1 (Hk1 & H6' & H16' & H9' & H10' & H21')) "Hl Hx HG".
    iApply (IH (List.length os - S k)%nat ltac:(lia) e1 (S k) eq_refl with "Ht Hpfx Hsl Hsc Hl Hx HG [HK]");
      [exact H6' | exact H16' | exact H9' | exact H10' | exact H21' | lia | exact Hos | exact Hxs | exact Hsb
      | exact Hse' | exact Hsr | exact Hse0 | exact Hsea | exact Hsee | exact Hser |].
    iIntros (e' Hk') "Hl Hx HG". iApply ("HK" with "[%] Hl Hx HG"). eapply keeps_trans; [exact Hk1 | exact Hk']. }
  assert (k = List.length os) as -> by lia.
  cbn [b_insts b_jump plo_blk273]. st.
  rewrite (Z.mod_small (Z.of_nat (List.length os)) (2 ^ 32)); [|lia].
  rewrite (sx_nonneg (Z.of_nat (List.length os))); [|lia].
  rewrite Z.ltb_irrefl. iApply wp_branch; [vx | iNext]. close_br.
  en. st.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hsl");
    [reflexivity | vx | left; reflexivity | arith | arith | arith |].
  iNext; iIntros "_".
  iDestruct (Hlend with "HG") as (dq freg) "[Hcf HG]".
  iApply (wp_raw_load_pointer_dq with "Hsl Hsc Hcf"); [reflexivity | vx | left; reflexivity | arith | arith | exact Hfp |].
  iNext; iIntros "_ _ Hcf"; iSpecialize ("HG" with "Hcf"). st.
  iApply (Hf5 with "HG"); [exact H141 | vx |]. iNext. iIntros (r0) "HG". st.
  iApply ("HK" with "[%] Hl Hx HG"). xkeep.
Qed.

End list.
End GetoptLongAmbListOn.
