(** When glibc's long-option parser has found the option that a word
    names in the caller's table, it steps the index past the word,
    clears its cursor and looks at the option's argument. The argument
    may follow an equals sign, may be the next word, or may be missing.
    Then the parser reports the option through the caller's longind and
    flag targets, or it reports a misuse on stderr. This file composes
    the proofs of those steps into one rule for a found option, from
    the block that tests the found entry to each of the parser's
    returns. *)

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
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag GetoptLongStore GetoptLongTail GetoptLongReq GetoptLongEq GetoptLongPre.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The argument paths keep these names for the final stores. *)
Definition larg_keys : list name := Eval vm_compute in
  List.map TAtom ["v8"; "v90"; "pr.12"; "pr.7"]%string.

(** The first blocks keep these names for the steps after them. *)
Definition lpre_keys : list name := Eval vm_compute in
  List.map TAtom ["v8"; "v90"; "pr.12"; "pr.7"; "v0"; "v2"; "v4"; "v12"; "v14"; "v16"; "pr.1"; "chk0"]%string.

(** The first blocks' names begin with the names of the final stores. *)
Lemma lpre_keys_app :
  lpre_keys = (larg_keys ++ List.map TAtom ["v0"; "v2"; "v4"; "v12"; "v14"; "v16"; "pr.1"; "chk0"]%string)%list.
Proof. reflexivity. Qed.

(** A found option leaves the index at i' and the argument at a' in one
    of three ways. An equals sign ends the name in the word s at the
    cursor cur, and the option takes an argument: the rest of the word
    is the argument. The name ends the word, and the option does not
    require an argument: the argument stays a. The name ends the word,
    the option requires an argument, and another word is left below the
    count n: that word is the argument, and the index steps past it. *)
Definition long_arg (s : list Z) (has i n : Z) (cur a : ptr) (ps : list ptr) (i' : Z) (a' : ptr) : Prop :=
  (sbyte s (eq_len s) = 61 /\ has <> 0 /\ i' = i + 1 /\ a' = ptr_add cur (Z.of_nat (eq_len s) + 1)) \/
  (sbyte s (eq_len s) = 0 /\ has <> 1 /\ i' = i + 1 /\ a' = a) \/
  (sbyte s (eq_len s) = 0 /\ has = 1 /\ i + 1 < n /\ i' = i + 2 /\ a' = nth (Z.to_nat (i + 1)) ps null).

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongArgOn (R : Runtime) (LG0 : LogicSig R).
(** The first-blocks module supplies the steps that this file composes. *)
Module LP := GetoptLongPreOn R LG0.
Import LP LP.LQE LP.LQE.LQ LP.LQE.LQ.LL LP.LQE.LQ.LL.LT LP.LQE.LQ.LL.LT.LD LP.LQE.LQ.LL.LT.LD.LE LP.LQE.LQ.LL.LT.LD.LE.LS
  LP.LQE.LQ.LL.LT.LD.LE.LS.RT LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X
  LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI
  LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.ML LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.LG
  LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.S.FI.L LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.ST LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.GB
  LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.A.

Section arg.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance arg_stable : SafepointStable (os_wi w0) := LP.LQE.LQ.LL.LT.LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance arg_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The parser has found the entry x of the caller's table for the word
    at index i. It steps the index, clears its cursor and takes the
    argument as long_arg says. Then it stores the entry's index through
    longind and returns. When the entry's flag pointer is not null, the
    parser stores the entry's value there and returns 0. Otherwise it
    returns the value. A misused option becomes the bad option instead.
    An argument given to an option that takes none makes the parser
    answer '?'. A missing argument makes it answer ':' or '?'. Each
    report keeps G, and the caller's targets stay as they were. *)
Lemma wp_long_found ks e (G : iProp Σ) T fp dom se sereg mid3 mid4 av ar ps lo os j x pfx sp po so cur s c0
    i n pe oo a b r li F Φ :
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
  live b r -∗ int_cell b 0 i -∗ int_cell b 8 oo -∗ pcell b 16 a -∗ pcell b 32 c0 -∗
  live av ar -∗ argv_cells av ps -∗ argv_strs ps -∗ G -∗ longind_own li -∗ flags_own F -∗
  ((∀ e' i' a', ⌜keeps ks e e' /\ long_arg s (lo_has x) i n cur a ps i' a' /\ lo_flag x <> null⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo -∗ pcell b 16 a' -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ (⌜li = null⌝ ∨ int_at li (Z.of_nat j)) -∗ flags_own F -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L494") [] (JRet (Const 0)))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' i' a', ⌜keeps ks e e' /\ long_arg s (lo_has x) i n cur a ps i' a' /\ lo_flag x = null /\
        lookup (TAtom "v511") e' = Some (WInt (lo_val x))⌝ -∗
      live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo -∗ pcell b 16 a' -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ (⌜li = null⌝ ∨ int_at li (Z.of_nat j)) -∗ flags_own F -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L496") [] (JRet (Tmp (TAtom "v511")))))
        : gexpr) {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ sbyte s (eq_len s) = 61 /\ lo_has x = 0⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 (lo_val x) -∗ pcell b 16 a -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ longind_own li -∗ flags_own F -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L413") [] (JRet (Const 63)))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ sbyte s (eq_len s) = 0 /\ lo_has x = 1 /\ (i + 1)%Z = n /\
        lookup (TAtom "v484") e' = Some (WInt (if sbyte so 0 =? 58 then 58 else 63))⌝ -∗
      live b r -∗ int_cell b 0 (i + 1) -∗ int_cell b 8 (lo_val x) -∗ pcell b 16 a -∗ pcell b 32 null -∗
      live av ar -∗ argv_cells av ps -∗ G -∗ longind_own li -∗ flags_own F -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L479") [] (JRet (Tmp (TAtom "v484")))))
        : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None
              (Exec (TAtom "L87") (b_insts plo_blk87) (b_jump plo_blk87))) : gexpr) {{ Φ }}.
Proof.
  intros Hks Hksq Hkse Hkst Hksd Hrule Hse Hmid3 Hmid4 H0 H2 H4 H8 H12 H14 H16 H90 Hp12 H7 Hp1 Hc0 Hc1 Hx Hos Hf
    Hi Hn Hlen Hpe Hb Hal Hend Hr Hav Hala Hda Hra Hse0 Hsea Hsee Hser.
  pose proof (lookup_lt_Some _ _ _ Hx) as Hjl.
  iIntros "#Hws0 #Hpfx #Hpo #Hws #Hsl #Hsc Hl Hib Hoo Hab Hcur Ha Hcl #Hs HG Hli HF HK".
  iRename "Hws0" into "Ht".
  iPoseProof "Ht" as "Ht0".
  iDestruct "Ht" as (tb treg) "(%Ht & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  let K := lazymatch iTypeOf "HK" with Some (_, ?P) => P end in
  iAssert (∀ e1 fr1 i' a', ⌜keeps ks e e1 /\ long_arg s (lo_has x) i n cur a ps i' a' /\
      lookup (TAtom "v8") e1 = Some (WPtr li) /\ lookup (TAtom "v90") e1 = Some (WInt 0) /\
      lookup (TAtom "pr.12") e1 = Some (WInt (Z.of_nat j)) /\
      lookup (TAtom "pr.7") e1 = Some (WPtr (ptr_add lo (32 * Z.of_nat j)))⌝ -∗
    live b r -∗ int_cell b 0 i' -∗ int_cell b 8 oo -∗ pcell b 16 a' -∗ pcell b 32 null -∗
    live av ar -∗ argv_cells av ps -∗ G -∗ longind_own li -∗ flags_own F -∗ K -∗
    WP (ERun (mkFrame glibc_process_long_option e1 [] None (Enter (TAtom "L398") (Some fr1))) : gexpr) {{ Φ }})%I
    as "HL398".
  { iIntros (e1 fr1 i' a' (Hk1 & Ha' & H8' & H90' & Hp12' & H7')) "Hl Hib Hoo Hab Hcur Ha Hcl HG Hli HF HK".
    iApply (wp_long_store w0 registry ge ks e1 fr1 li F lo os j x with "Ht0 Hli HF");
      [exact Hkst | exact H8' | exact H90' | exact Hp12' | exact H7' | exact Hx | exact Hos | exact Hf |].
    iSplit.
    - iIntros (e2 (Hk2 & Hnn)) "Hli HF". iDestruct "HK" as "[HK _]".
      iApply ("HK" $! e2 i' a' with "[%] Hl Hib Hoo Hab Hcur Ha Hcl HG Hli HF").
      split; [eapply keeps_trans; [exact Hk1 | exact Hk2] | split; assumption].
    - iIntros (e2 (Hk2 & Hnl & H511)) "Hli HF". iDestruct "HK" as "[_ [HK _]]".
      iApply ("HK" $! e2 i' a' with "[%] Hl Hib Hoo Hab Hcur Ha Hcl HG Hli HF").
      split; [eapply keeps_trans; [exact Hk1 | exact Hk2] | repeat split; assumption]. }
  iApply (wp_long_pre w0 registry ge (lpre_keys ++ ks) e lo j cur s c0 i b r with "Hws Hl Hib Hcur");
    [rewrite avoids_app_l; rewrite Hks; vm_compute; reflexivity | exact H12 | exact H90 | exact H7 | exact Hp1
    | exact Hc0 | exact Hc1 | lia | lia | lia | exact Hb | exact Hal | exact Hend | exact Hr |].
  iSplit.
  - iIntros (e0 (Hk0 & E0 & H47)) "Hl Hib Hcur". apply keeps_app in Hk0 as [Hkt0 Hk0].
    pose proof Hkt0 as Hka. rewrite lpre_keys_app in Hka. apply keeps_app in Hka as [Hka _].
    iApply (wp_long_req w0 registry ge (larg_keys ++ ks) _ G T fp dom se sereg mid4 av ar ps lo os j x pfx sp po so
      i n pe oo a b r with "Ht0 Hpfx Hpo Hsl Hsc Hl Hib Hoo Hab Ha Hcl Hs HG");
      [rewrite avoids_app_l; rewrite Hksq; vm_compute; reflexivity | rewrite avoids_app_l; rewrite Hksd; vm_compute; reflexivity
      | exact Hrule | exact Hse | exact Hmid4 | viakeep Hkt0 | viakeep Hkt0 | viakeep Hkt0 | viakeep Hkt0 | viakeep Hkt0
      | viakeep Hkt0 | viakeep Hkt0 | viakeep Hkt0 | exact H47 | exact Hx | exact Hos | exact Hi | exact Hn | exact Hlen | exact Hpe | exact Hb | exact Hal
      | exact Hend | exact Hr | exact Hav | exact Hala | exact Hda | exact Hra | exact Hse0 | exact Hsea | exact Hsee
      | exact Hser |].
    iSplit; [|iSplit].
    + iIntros (e1 (Hk1 & Eh)) "Hl Hib Hoo Hab Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
      iApply ("HL398" $! e1 _ (i + 1) a with "[%] Hl Hib Hoo Hab Hcur Ha Hcl HG Hli HF HK").
      split; [eapply keeps_trans; [exact Hk0 | exact Hk1]|]. split; [right; left; repeat split; auto|].
      pose proof (keeps_trans _ _ _ _ Hka Hkt) as Hkb. repeat split; viakeep Hkb.
    + iIntros (e1 (Hk1 & Eh & Hlt)) "Hl Hib Hoo Hab Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
      iApply ("HL398" $! e1 _ (i + 2) _ with "[%] Hl Hib Hoo Hab Hcur Ha Hcl HG Hli HF HK").
      split; [eapply keeps_trans; [exact Hk0 | exact Hk1]|]. split; [right; right; repeat split; auto|].
      pose proof (keeps_trans _ _ _ _ Hka Hkt) as Hkb. repeat split; viakeep Hkb.
    + iIntros (e1 (Hk1 & Eh & Hn1 & H484)) "Hl Hib Hoo Hab Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
      iDestruct "HK" as "[_ [_ [_ HK]]]".
      iApply ("HK" with "[%] Hl Hib Hoo Hab Hcur Ha Hcl HG Hli HF").
      split; [eapply keeps_trans; [exact Hk0 | exact Hk1]|]. repeat split; auto.
  - iIntros (e0 (Hk0 & E61)) "Hl Hib Hcur". apply keeps_app in Hk0 as [Hkt0 Hk0].
    pose proof Hkt0 as Hka. rewrite lpre_keys_app in Hka. apply keeps_app in Hka as [Hka _].
    iApply (wp_long_eq w0 registry ge (larg_keys ++ ks) _ _ G T fp dom se sereg mid3 av ar ps lo os j x pfx sp cur s
      pe oo a b r with "Ht0 Hpfx Hws Hsl Hsc Hl Hoo Hab Ha Hcl Hs HG");
      [rewrite avoids_app_l; rewrite Hkse; vm_compute; reflexivity | rewrite avoids_app_l; rewrite Hksd; vm_compute; reflexivity
      | exact Hrule | exact Hse | exact Hmid3 | viakeep Hkt0 | viakeep Hkt0 | viakeep Hkt0 | viakeep Hkt0 | viakeep Hkt0
      | viakeep Hkt0 | viakeep Hkt0 | exact Hx | exact Hpe | exact Hb | exact Hal | exact Hend | exact Hr | exact Hav | exact Hala | lia | exact Hra
      | intros ->; cbn in Hlen; lia | exact Hse0 | exact Hsea | exact Hsee | exact Hser |].
    iSplit.
    + iIntros (e1 (Hk1 & Eh)) "Hl Hoo Hab Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
      iApply ("HL398" $! e1 _ (i + 1) _ with "[%] Hl Hib Hoo Hab Hcur Ha Hcl HG Hli HF HK").
      split; [eapply keeps_trans; [exact Hk0 | exact Hk1]|]. split; [left; repeat split; auto|].
      pose proof (keeps_trans _ _ _ _ Hka Hkt) as Hkb. repeat split; viakeep Hkb.
    + iIntros (e1 (Hk1 & Eh)) "Hl Hoo Hab Ha Hcl HG". apply keeps_app in Hk1 as [Hkt Hk1].
      iDestruct "HK" as "[_ [_ [HK _]]]".
      iApply ("HK" with "[%] Hl Hib Hoo Hab Hcur Ha Hcl HG Hli HF").
      split; [eapply keeps_trans; [exact Hk0 | exact Hk1]|]. repeat split; auto.
Qed.

End arg.
End GetoptLongArgOn.
