(** When glibc's long-option parser reports an ambiguous word, it lists
    the candidates that its set marks. This file proves one step of that
    listing safe: the parser reads the byte of one entry in the set, and
    when the byte is not 0 it reads the entry's name from the option
    table and writes it through the report rule that its caller
    supplies. *)

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
  GetoptLongMiss GetoptLongPfxCmp GetoptLongPfxMark GetoptLongPfxAlloc GetoptLongPfxSet GetoptLongPfxStep GetoptLongPfxIter GetoptLongPfxLoop GetoptLongPfxEnd GetoptLongAmbTail GetoptLongAmbPrint.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The listing of the matching options assigns these names. *)
Definition alist_names : list name := Eval vm_compute in
  List.map TAtom ["pr.10"; "v279"; "v285"; "v286"; "chk25"; "v287"; "v288"; "chk26"; "v289"; "v290"; "v295";
    "v296"; "chk27"; "v297"; "v298"; "v300"; "v301"; "chk28"; "v302"; "v303"; "v304"]%string.

(** One step of the listing keeps these names for the next step. *)
Definition alist_keys : list name := Eval vm_compute in
  List.map TAtom ["v6"; "v16"; "pr.9"; "pr.10"; "pr.21"]%string.

(** A write of one candidate assigns only names that the whole listing
    assigns, so a name the listing keeps survives the write. *)
Lemma alist_avoids_print ks : avoids ks alist_names = true -> avoids ks aprint_names = true.
Proof.
  unfold avoids. intros H. apply forallb_forall. intros k Hk.
  pose proof (proj1 (forallb_forall _ _) H k Hk) as Hk'. cbv beta in Hk'.
  apply forallb_forall. intros w Hw. apply (proj1 (forallb_forall _ _) Hk'). revert Hw.
  unfold aprint_names, alist_names. cbn [In]. tauto.
Qed.

(** The parser tests here whether entries are left to list. *)
Definition plo_blk273 : block := Eval vm_compute in plo_blk "L273".

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongAmbItemOn (R : Runtime) (LG0 : LogicSig R).
(** The write module supplies the write of one candidate, the set, the option table and the tactics. *)
Module LAP := GetoptLongAmbPrintOn R LG0.
Import LAP LAP.LAT LAP.LAT.LPE LAP.LAT.LPE.LPL LAP.LAT.LPE.LPL.LPI LAP.LAT.LPE.LPL.LPI.LPT LAP.LAT.LPE.LPL.LPI.LPT.LPS LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.


Section item.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance aitem_stable : SafepointStable (os_wi w0) := LAP.LAT.LPE.LPL.LPI.LPT.LPS.LPA.LPM.LPC.LM.LOM.LU.LA.LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance aitem_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** One step of the listing handles one entry of the table. The
    parser looks at the entry's byte in the set. If the byte is not 0,
    the entry is a candidate, and the parser writes its name with the
    prefix through the format str.140. Then it moves on to the next
    entry. The step leaves the set as it was and gives G back. *)
Lemma wp_amb_item ks e (G : iProp Σ) T fp dom se sereg f140 lo os pfx ps (k : nat) sb sreg xs Φ :
  avoids ks alist_names = true -> getopt_ldiag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.140") (ge_globals ge) = Some f140 ->
  lookup (TAtom "v6") e = Some (WPtr lo) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "pr.9") e = Some (WInt (Z.of_nat (List.length os))) ->
  lookup (TAtom "pr.10") e = Some (WInt (Z.of_nat k)) ->
  lookup (TAtom "pr.21") e = Some (WPtr (mkPtr sb (Obj sb))) ->
  (k < List.length os)%nat -> (List.length os < 2 ^ 31)%Z -> List.length xs = List.length os ->
  0 < sb -> sb + Z.of_nat (List.length os) <= r_end sreg -> r_end sreg <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx ps -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live sb sreg -∗ bytes sb 0 xs -∗ G -∗
  (∀ e', ⌜keeps ks e e' /\ lookup (TAtom "v6") e' = Some (WPtr lo) /\ lookup (TAtom "v16") e' = Some (WPtr pfx) /\
      lookup (TAtom "pr.9") e' = Some (WInt (Z.of_nat (List.length os))) /\
      lookup (TAtom "pr.10") e' = Some (WInt (Z.of_nat (S k))) /\
      lookup (TAtom "pr.21") e' = Some (WPtr (mkPtr sb (Obj sb)))⌝ -∗ live sb sreg -∗ bytes sb 0 xs -∗ G -∗
     WP (ERun (mkFrame glibc_process_long_option e' [] None
       (Exec (TAtom "L273") (b_insts plo_blk273) (b_jump plo_blk273))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L273") (b_insts plo_blk273) (b_jump plo_blk273))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hrule Hse H140 H6 H16 H9 H10 H21 Hk Hos Hxs Hsb Hse' Hsr Hse0 Hsea Hsee Hser.
  iIntros "#Ht #Hpfx #Hsl #Hsc Hl Hx HG HK".
  iAssert (∀ e1 fr1, ⌜keeps ks e e1 /\ lookup (TAtom "v6") e1 = Some (WPtr lo) /\
      lookup (TAtom "v16") e1 = Some (WPtr pfx) /\ lookup (TAtom "pr.9") e1 = Some (WInt (Z.of_nat (List.length os))) /\
      lookup (TAtom "pr.10") e1 = Some (WInt (Z.of_nat k)) /\
      lookup (TAtom "pr.21") e1 = Some (WPtr (mkPtr sb (Obj sb)))⌝ -∗ live sb sreg -∗ bytes sb 0 xs -∗ G -∗
    WP (ERun (mkFrame glibc_process_long_option e1 [] None (Enter (TAtom "L275") (Some fr1))) : gexpr) {{ Φ }})%I
    with "[HK]" as "HL275".
  { iIntros (e1 fr1 (Hk1 & H6' & H16' & H9' & H10' & H21')) "Hl Hx HG".
    en. st. st. st. match goal with |- context [put (TAtom "pr.10") (WInt ?X) _] =>
      replace X with (Z.of_nat (S k)) by (rewrite (Z.mod_small (Z.of_nat k) (2 ^ 32)); [|lia];
        rewrite (Z.mod_small 1 (2 ^ 32)); [|lia]; rewrite !(Z.mod_small (Z.of_nat k + 1) (2 ^ 32)); lia) end.
    pcmp_fold "L273" plo_blk273.
    iApply ("HK" with "[%] Hl Hx HG"). split; [eapply keeps_trans; [exact Hk1|]; xkeep|]. repeat split; lk_prove. }
  cbn [b_insts b_jump plo_blk273]. st.
  rewrite (Z.mod_small (Z.of_nat k) (2 ^ 32)); [|lia]. rewrite (Z.mod_small (Z.of_nat (List.length os)) (2 ^ 32)); [|lia].
  rewrite (sx_nonneg (Z.of_nat k)); [|lia]. rewrite (sx_nonneg (Z.of_nat (List.length os))); [|lia].
  rewrite (proj2 (Z.ltb_lt _ _)); [|lia]. iApply wp_branch; [vx | iNext]. close_br.
  destruct (lookup_lt_is_Some_2 xs k ltac:(lia)) as [x Hx].
  en. st. st. norm. rewrite (Z.mod_small (Z.of_nat k) (2 ^ 32)); [|lia]. rewrite (sx_nonneg (Z.of_nat k)); [|lia].
  rewrite (Z.mod_small (Z.of_nat k) (2 ^ 64)); [|lia].
  match goal with |- context [put (TAtom "v286") (WPtr {| ptr_addr := ?X; ptr_cap := Obj sb |})] =>
    replace X with (sb + Z.of_nat k) by (rewrite !Z.mod_small; lia) end.
  iApply (wp_check with "Hl"); [reflexivity | vx | reflexivity | arith | arith | apply Z.mod_1_r |].
  iNext. iIntros "Hl". iDestruct (bytes_at sb xs k x Hx with "Hx") as "(Hx0 & Hb & Hx1)".
  iApply (wp_raw_load_byte with "Hl Hb"); [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | arith |].
  iNext. iIntros "Hl Hb". iDestruct (bytes_at sb xs k x Hx with "[$Hx0 $Hb $Hx1]") as "Hx".
  iApply wp_branch; [vx | iNext].
  destruct (Z.eqb ((extension Ub x mod 2 ^ 32) mod 2 ^ 32) 0); cbn [edge_label].
  - iApply ("HL275" with "[%] Hl Hx HG"). split; [xkeep|]. repeat split; lk_prove.
  - destruct (lookup_lt_is_Some_2 os k ltac:(lia)) as [y Hy].
    iApply (wp_amb_print w0 registry ge (alist_keys ++ ks)%list _ _ G T fp dom se sereg f140 lo os pfx ps k y
      with "Ht Hpfx Hsl Hsc HG"); [rewrite avoids_app_l (alist_avoids_print _ Hks); reflexivity | exact Hrule | exact Hse
      | exact H140 | lk_prove | lk_prove | lk_prove | exact Hy | exact Hos | exact Hse0 | exact Hsea | exact Hsee
      | exact Hser |].
    iIntros (e' Hk') "HG". apply keeps_app in Hk' as [Hkt Hk'].
    iApply ("HL275" with "[%] Hl Hx HG"). split; [eapply keeps_trans; [|exact Hk']; xkeep|].
    repeat split; (rewrite (keeps_in _ _ _ _ Hkt); [lk_prove | unfold alist_keys; cbn [In]; repeat first [left; reflexivity | right]]).
Qed.

End item.
End GetoptLongAmbItemOn.
