(** A long option written without an equals sign may still require an
    argument. glibc's long-option parser then takes the next element of
    the argument vector as the argument and steps the index past it.
    When no element is left, it reports the missing argument, stores the
    option's value as the bad option, and answers ':' or '?' as the
    option string asks. This file proves that part of the parser safe:
    it reads only the found table entry, the vector below its count and
    the first byte of the option string, and it writes only the parser's
    own private fields. *)

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
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The missing-argument report keeps these names for the blocks after it. *)
Definition lreq_keys : list name := Eval vm_compute in
  List.map TAtom ["v12"; "v4"; "pr.7"; "chk0"; "chk58"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongReqOn (R : Runtime) (LG0 : LogicSig R).
(** The tail module supplies both ends of the path, the option table, the report rule and the tactics. *)
Module LL := GetoptLongTailOn R LG0.
Import LL LL.LT LL.LT.LD LL.LT.LD.LE LL.LT.LD.LE.LS LL.LT.LD.LE.LS.RT LL.LT.LD.LE.LS.RT.D LL.LT.LD.LE.LS.RT.D.X
  LL.LT.LD.LE.LS.RT.D.X.I LL.LT.LD.LE.LS.RT.D.X.I.S LL.LT.LD.LE.LS.RT.D.X.I.S.FI LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML
  LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L LL.LT.LD.LE.LS.RT.D.X.I.ST LL.LT.LD.LE.LS.RT.D.X.I.GB
  LL.LT.LD.LE.LS.RT.D.X.A.

Section req.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance req_stable : SafepointStable (os_wi w0) := LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance req_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** An option without an equals sign may require another command-line word.
    The parser consumes that word when one remains and advances its index.
    Otherwise it reports the missing argument and records the option's value
    as the bad option. The option string chooses ':' or '?' for the return.
    Options that do not require an argument leave the fields unchanged. *)
Lemma wp_long_req ks e (G : iProp Σ) T fp dom se sereg mid av ar ps lo os j x pfx sp po so i n pe oo a b r Φ :
  avoids ks lreq_names = true -> avoids ks ldiag_names = true -> getopt_ldiag_rule w0 registry ge G T fp dom ->
  lookup (TAtom "stderr") (ge_globals ge) = Some (mkPtr se (Obj se)) ->
  lookup (TAtom "glibc_getopt#str.144") (ge_globals ge) = Some mid ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v4") e = Some (WPtr po) -> lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v14") e = Some (WInt pe) -> lookup (TAtom "v16") e = Some (WPtr pfx) ->
  lookup (TAtom "pr.7") e = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 32) (Obj b))) ->
  lookup (TAtom "chk47") e = Some (WPtr (mkPtr b (Obj b))) ->
  os !! j = Some x -> (List.length os < 2 ^ 31)%Z ->
  0 <= i < n -> n < 2 ^ 31 - 1 -> Z.of_nat (List.length ps) = n -> 0 <= pe < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  0 < av -> av mod 8 = 0 -> av + 8 * n <= r_end ar -> r_end ar <= 2 ^ 48 ->
  0 < se -> se mod 8 = 0 -> se + 8 <= r_end sereg -> r_end sereg <= 2 ^ 48 ->
  opt_table lo os -∗ word_string DfracDiscarded pfx sp -∗ word_string DfracDiscarded po so -∗
  liveq DfracDiscarded se sereg -∗ pcellq DfracDiscarded se 0 fp -∗
  live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗
  ((∀ e', ⌜keeps ks e e' /\ lo_has x <> 1⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L398") (Some (TAtom "L397"))))
        : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ lo_has x = 1 /\ i + 1 < n⌝ -∗
      live b r -∗ int_cell b 0 (i + 2) -∗ int_cell b 8 oo -∗ pcell b 16 (nth (Z.to_nat (i + 1)) ps null) -∗
      live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Enter (TAtom "L398") (Some (TAtom "L439"))))
        : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ lo_has x = 1 /\ (i + 1)%Z = n /\
        lookup (TAtom "v484") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 (lo_val x) -∗ pcell b 16 a -∗
      live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L479") [] (JRet (Tmp (TAtom "v484")))))
        : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L397") (Some (TAtom "L327")))) : gexpr)
    {{ Φ }}.
Proof.
  intros Hks Hksd Hrule Hse Hmid H0 H2 H4 H12 H14 H16 H7 Hc0 Hc47 Hx Hos Hi Hn Hlen Hpe
    Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  pose proof (lookup_lt_Some _ _ _ Hx) as Hjl.
  iIntros "#Ht #Hpfx #Hpo #Hsl #Hsc Hl [%Hi0 Hib] Hoo Hab Ha Hcl #Hs HG HK".
  iPoseProof "Ht" as "Ht0".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iDestruct (big_sepL_lookup with "Hes") as "(_ & _ & #Hhl & _ & #Hvl)"; [exact Hx|].
  iDestruct "Hhl" as "[%Hh0 Hhb]". iDestruct "Hvl" as "[%Hv0 Hvb]".
  en. st.
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Htl");
    [reflexivity | vx | exact Htc | rawa | rawa | apply Z.mod_1_r |]; iNext; iIntros "_".
  iApply (wp_raw_load_sub_bytes_dq with "Htl Hhb");
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | exact Htc | rawa |].
  iNext; iIntros "_ _". st. rewrite (Z.mod_small (lo_has x) (2 ^ 32)); [|lia].
  change (1 mod 2 ^ 32) with 1.
  iApply wp_branch; [vx | iNext]. destruct (Z.eqb_spec (lo_has x) 1) as [E1 | E1]; close_br.
  2: { iDestruct "HK" as "[HK _]". iApply ("HK" with "[%] Hl [Hib] Hoo Hab Ha Hcl HG"); [split; [xkeep | exact E1] | by iSplit]. }
  en. chk "Hl". load_int "Hl Hib". st.
  destruct (Z.lt_ge_cases (i + 1) n) as [Hlt | Hge].
  - brz. iDestruct "HK" as "[_ [HK _]]".
    iApply (wp_long_next w0 registry ge _ _ _ i n with "Hl [Hib] Hab Ha Hcl Hs");
      [exact Hks | lk_prove | lk_prove | lk_prove | lk_prove | lk_prove | lia | exact Hlt | exact Hn | exact Hlen
      | exact Hb | exact Hal | exact Hend | exact Hr | exact Hav | exact Hala | exact Hda | exact Hra | by iSplit |].
    iIntros (e1) "%Hk1 Hl Hib Hab Ha Hcl".
    iApply ("HK" with "[%] Hl Hib Hoo Hab Ha Hcl HG"). split; [eapply keeps_trans; [|exact Hk1]; xkeep | auto].
  - assert (Hn1 : (i + 1)%Z = n) by lia. brz.
    iDestruct "HK" as "[_ [_ HK]]".
    iAssert (∀ e1 fr1, ⌜keeps ks e e1 /\ lookup (TAtom "v12") e1 = Some (WPtr (mkPtr b (Obj b))) /\
        lookup (TAtom "v4") e1 = Some (WPtr po) /\
        lookup (TAtom "pr.7") e1 = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) /\
        lookup (TAtom "chk0") e1 = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
        lookup (TAtom "chk58") e1 = Some (WPtr (mkPtr ((ptr_addr (ptr_add lo (32 * Z.of_nat j)) mod 2 ^ 64 + 8 mod 2 ^ 64)
          mod 2 ^ 64) (ptr_cap (ptr_add lo (32 * Z.of_nat j)))))⌝ -∗
      live av ar -∗ argv_cells av ps -∗ G -∗
      WP (ERun (mkFrame glibc_process_long_option e1 [] None (Enter (TAtom "L458") (Some fr1))) : gexpr) {{ Φ }})%I
      with "[Hl Hoo Hib Hab HK]" as "HL458".
    { iIntros (e1 fr1 (Hk1 & H12' & H4' & H7' & Hc0' & Hc58')) "Ha Hcl HG".
      iApply (wp_long_miss_tail w0 registry ge with "Ht0 Hpo Hl Hoo");
        [exact Hks | exact H4' | exact H12' | exact H7' | exact Hc0' | exact Hc58' | reflexivity | exact Hx
        | exact Hb | exact Hal | exact Hend | exact Hr |].
      iIntros (e2 (Hk2 & H484)) "Hl Hoo".
      iApply ("HK" with "[%] Hl [Hib] Hoo Hab Ha Hcl HG"); [|by iSplit].
      split; [eapply keeps_trans; [exact Hk1 | exact Hk2]|]. repeat split; first [exact E1 | exact Hn1 | exact H484]. }
    en. iApply wp_branch; [vx | iNext]. rewrite (Z.mod_small pe (2 ^ 32)); [|lia].
    destruct (Z.eqb_spec pe 0) as [Ep | Ep]; cbn [edge_label].
    + iApply ("HL458" with "[%] Ha Hcl HG"). split; [xkeep|]. repeat split; lk_prove.
    + iApply (wp_getopt_ldiag_missing w0 registry ge (lreq_keys ++ ks) with "Ht0 Hpfx Hsl Hsc Ha Hcl Hs HG [HL458]");
        [rewrite avoids_app_l; rewrite Hksd; vm_compute; reflexivity | exact Hrule | exact Hse | exact Hmid | lk_prove
        | lk_prove | lk_prove | lk_prove | reflexivity | exact Hx | exact Hse0 | exact Hsea | exact Hsee | exact Hser
        | exact Hav | exact Hala | lia | exact Hra | intros ->; cbn in Hlen; lia |].
      iIntros (e1) "%Hk1 Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
      iApply ("HL458" with "[%] Ha Hcl HG"). split; [(eapply keeps_trans; [|exact Hk1]; xkeep)|].
      repeat split; viakeep Hkt.
Qed.

End req.
End GetoptLongReqOn.
