(** After glibc's long-option parser has accepted an option and its
    argument, it reports which option it found. It stores the option's
    index through the caller's longind pointer when that pointer is not
    null. Then it stores the option's value through the option's flag
    pointer and returns 0, or, when the flag pointer is null, it returns
    the value itself. This file states what the caller owns of these
    targets and proves the final stores safe: every store goes to an
    integer cell that the caller owns, inside its object. *)

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
  GetoptDiag GetoptReqTail GetoptLongScan GetoptLongExact GetoptLongDiag.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The final stores assign these names. *)
Definition lstore_names : list name := Eval vm_compute in
  List.map TAtom ["v489"; "v491"; "chk70"; "v498"; "chk71"; "v499"; "v500"; "v501"; "v503"; "v504"; "v506";
    "chk73"; "v507"; "chk74"; "v510"; "chk75"; "v511"]%string.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptLongStoreOn (R : Runtime) (LG0 : LogicSig R).
(** The report module supplies the option table and the tactics. *)
Module LD := GetoptLongDiagOn R LG0.
Import LD LD.LE LD.LE.LS LD.LE.LS.RT LD.LE.LS.RT.D LD.LE.LS.RT.D.X LD.LE.LS.RT.D.X.I LD.LE.LS.RT.D.X.I.S
  LD.LE.LS.RT.D.X.I.S.FI LD.LE.LS.RT.D.X.I.S.FI.ML LD.LE.LS.RT.D.X.I.S.FI.LG LD.LE.LS.RT.D.X.I.S.FI.L
  LD.LE.LS.RT.D.X.I.ST LD.LE.LS.RT.D.X.I.GB LD.LE.LS.RT.D.X.A.

Section targets.
Context `{!gen_heapGS piece pval Σ}.

(** The caller owns the integer v at p. The four bytes at p lie inside
    the object of p's capability, at a four-byte boundary below 2^48,
    and the caller owns that object's whole lifetime, so it may store
    there. *)
Definition int_at (p : ptr) (v : Z) : iProp Σ :=
  ∃ tb treg, ⌜ptr_cap p = Obj tb /\ 0 < tb <= ptr_addr p /\ ptr_addr p mod 4 = 0 /\
     ptr_addr p + 4 <= r_end treg /\ r_end treg <= 2 ^ 48⌝ ∗
   live tb treg ∗ int_cell tb (ptr_addr p - tb) v.

(** The flag targets F are distinct integers that the caller owns. *)
Definition flags_own (F : list ptr) : iProp Σ := ⌜NoDup F⌝ ∗ [∗ list] f ∈ F, ∃ v, int_at f v.

(** The caller's longind pointer li is null or points at an integer that
    the caller owns. *)
Definition longind_own (li : ptr) : iProp Σ := ⌜li = null⌝ ∨ ∃ v, int_at li v.

End targets.

Section store.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the parser's safepoints. *)
Local Instance store_stable : SafepointStable (os_wi w0) := LD.LE.LS.RT.D.X.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance store_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** An owned integer accepts a store of any 32-bit value. *)
Lemma int_at_store f e ls l v a rest jp p w w' Φ :
  value_x ge e W v = Some (WInt w') -> value_x ge e A a = Some (WPtr p) -> 0 <= w' < 2 ^ 32 ->
  int_at p w -∗
  ▷ (int_at p w' -∗ WP (ERun (mkFrame f e ls None (Exec l rest jp)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Ww 0 v a :: rest) jp)) : gexpr) {{ Φ }}.
Proof.
  intros Hv Ha Hw. iIntros "Hp HK". iDestruct "Hp" as (tb treg) "(%Hp & Hl & [%Hw0 Hb])".
  destruct Hp as (Hc & Htb & Hal & Hend & Hr).
  iApply (wp_raw_store_w with "Hl Hb"); [exact Hv | exact Ha | exact Hc | unfold raw_address; rewrite Z.mod_small; lia | reflexivity | wi_store |].
  iNext. iIntros "Hl Hb". iApply "HK". iExists tb, treg. iFrame. iPureIntro. repeat split; try assumption; try lia.
Qed.

(** The parser stands after the argument with the found entry x at index
    j of the table lo. It stores j through longind when longind li is not
    null. It then reads the flag pointer of x. A flag that is not null is
    one of the caller's targets F, and it receives the value of x before
    the parser returns 0. A null flag makes the parser return the value
    of x at v511. *)
Lemma wp_long_store ks e fr li F lo os j x Φ :
  avoids ks lstore_names = true ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v90") e = Some (WInt 0) ->
  lookup (TAtom "pr.12") e = Some (WInt (Z.of_nat j)) ->
  lookup (TAtom "pr.7") e = Some (WPtr (ptr_add lo (32 * Z.of_nat j))) ->
  os !! j = Some x -> (List.length os < 2 ^ 31)%Z -> lo_flag x = null \/ lo_flag x ∈ F ->
  opt_table lo os -∗ longind_own li -∗ flags_own F -∗
  ((∀ e', ⌜keeps ks e e' /\ lo_flag x <> null⌝ -∗ (⌜li = null⌝ ∨ int_at li (Z.of_nat j)) -∗ flags_own F -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L494") [] (JRet (Const 0)))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜keeps ks e e' /\ lo_flag x = null /\ lookup (TAtom "v511") e' = Some (WInt (lo_val x))⌝ -∗
      (⌜li = null⌝ ∨ int_at li (Z.of_nat j)) -∗ flags_own F -∗
      WP (ERun (mkFrame glibc_process_long_option e' [] None (Exec (TAtom "L496") [] (JRet (Tmp (TAtom "v511")))))
        : gexpr) {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_process_long_option e [] None (Enter (TAtom "L398") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hks H8 H90 H12 H7 Hx Hos Hf. pose proof (lookup_lt_Some _ _ _ Hx) as Hjl.
  iIntros "#Ht Hli [%Hnd HF] HK".
  iDestruct "Ht" as (tb treg) "(%Ht & #Htl & #Hes & _)". destruct Ht as (Htc & Htb & Htlo & Hta & Hte & Htr).
  iDestruct (big_sepL_lookup with "Hes") as "(_ & _ & _ & #Hfl & #Hvl)"; [exact Hx|].
  iAssert (∀ e1 fr1, ⌜keeps ks e e1 /\ lookup (TAtom "pr.7") e1 = Some (WPtr (ptr_add lo (32 * Z.of_nat j)))⌝ -∗
      (⌜li = null⌝ ∨ int_at li (Z.of_nat j)) -∗
      WP (ERun (mkFrame glibc_process_long_option e1 [] None (Enter (TAtom "L487") (Some fr1))) : gexpr)
        {{ Φ }})%I with "[HF HK]" as "HL487".
  { iIntros (e1 fr1 (Hk1 & H71)) "Hli". en. st.
    iApply (wp_check_read_dq registry (os_wi w0) ge with "Htl");
      [reflexivity | vx | exact Htc | rawa | rawa | al8 |]; iNext; iIntros "_".
    destruct Hf as [Hnull | Hin].
    - iApply (wp_raw_load_pointer_dq with "Htl Hfl []");
        [reflexivity | vx | exact Htc | rawa | al8 | rewrite Hnull; cbn; lia | rewrite Hnull; unfold live_capq; cbn; done |].
      iNext. iIntros "_ _ _". st. st. rewrite Hnull. unfold null; cbn [ptr_addr].
      iApply wp_branch; [vx | iNext]. close_br. en. st.
      iApply (wp_half_check_read_dq w0 registry ge with "Htl");
        [reflexivity | vx | reflexivity | exact Htc | al8 | al8 | lia | lia | apply Z.mod_1_r |].
      iNext; iIntros "_". iDestruct "Hvl" as "[%Hv0 Hvb]".
      iApply (wp_raw_load_sub_bytes_dq with "Htl Hvb");
        [reflexivity | vx | reflexivity | apply load_sw_int; assumption | exact Htc | rawa |].
      iNext; iIntros "_ _". iDestruct "HK" as "[_ HK]".
      iApply ("HK" with "[%] Hli [HF]"); [split; [|split]; [xkeep | reflexivity | lk_prove] | iFrame; done].
    - apply list_elem_of_lookup_1 in Hin as [k Hk].
      iDestruct (big_sepL_lookup_acc with "HF") as "[Hfc HF]"; [exact Hk|].
      iDestruct "Hfc" as (fv fb freg) "(%Hfp & Hfll & Hfcell)". destruct Hfp as (Hfc0 & Hfb & Hfa & Hfe & Hfr).
      assert (Hnn : lo_flag x <> null) by (intros Heq; rewrite Heq in Hfb; unfold null in Hfb; cbn in Hfb; lia).
      iAssert (live_capq (DfracOwn 1) (ptr_cap (lo_flag x)) freg) with "[Hfll]" as "Hfcap";
        [rewrite Hfc0; iExact "Hfll"|].
      iApply (wp_raw_load_pointer_dq with "Htl Hfl Hfcap"); [reflexivity | vx | exact Htc | rawa | al8 | lia |].
      iNext. iIntros "_ _ Hfcap". st. st.
      rewrite (Z.mod_small (ptr_addr (lo_flag x)) (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
      rewrite (proj2 (Z.eqb_neq (ptr_addr (lo_flag x)) 0)); [|lia].
      iApply wp_branch; [vx | iNext]. close_br. en. st.
      iApply (wp_raw_load_pointer_dq with "Htl Hfl Hfcap"); [reflexivity | vx | exact Htc | rawa | al8 | lia |].
      iNext. iIntros "_ _ Hfcap". st.
      iApply (wp_half_check_read_dq w0 registry ge with "Htl");
        [reflexivity | vx | reflexivity | exact Htc | al8 | al8 | lia | lia | apply Z.mod_1_r |].
      iNext; iIntros "_". iDestruct "Hvl" as "[%Hv0 Hvb]".
      iApply (wp_raw_load_sub_bytes_dq with "Htl Hvb");
        [reflexivity | vx | reflexivity | apply load_sw_int; assumption | exact Htc | rawa |].
      iNext; iIntros "_ _".
      iAssert (live fb freg) with "[Hfcap]" as "Hfll"; [rewrite Hfc0; iExact "Hfcap"|].
      iApply (wp_check with "Hfll"); [reflexivity | vx | exact Hfc0 | unfold raw_address; rewrite Z.mod_small; lia
        | unfold raw_address; rewrite Z.mod_small; lia | apply Z.mod_1_r |].
      iNext. iIntros "Hfll".
      iApply (int_at_store with "[Hfll Hfcell]"); [vx | vx | apply Z.mod_pos_bound; lia
        | iExists fb, freg; iFrame; iPureIntro; repeat split; first [assumption | lia] |].
      iNext. iIntros "Hfc". iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[%] Hli [HF Hfc]"); [split; [xkeep | exact Hnn] |].
      iSplit; [iPureIntro; exact Hnd|]. iApply "HF". iExists _. iExact "Hfc". }
  en. st. st. iDestruct "Hli" as "[%Hn | Hli]".
  - subst li. unfold null; cbn [ptr_addr]. iApply wp_branch; [vx | iNext]. close_br.
    iApply ("HL487" with "[%] []"); [split; [xkeep | lk_prove] | iLeft; done].
  - iDestruct "Hli" as (v lb lreg) "(%Hp & Hll & Hlc)". destruct Hp as (Hlc0 & Hlb & Hla & Hle & Hlr).
    rewrite (Z.mod_small (ptr_addr li) (2 ^ 64)); [|lia]. change (0 mod 2 ^ 64) with 0.
    rewrite (proj2 (Z.eqb_neq (ptr_addr li) 0)); [|lia].
    iApply wp_branch; [vx | iNext]. close_br. en.
    iApply (wp_check with "Hll"); [reflexivity | vx | exact Hlc0 | unfold raw_address; rewrite Z.mod_small; lia
      | unfold raw_address; rewrite Z.mod_small; lia | apply Z.mod_1_r |].
    iNext. iIntros "Hll".
    iApply (int_at_store with "[Hll Hlc]"); [vx | vx | apply Z.mod_pos_bound; lia
      | iExists lb, lreg; iFrame; iPureIntro; repeat split; first [assumption | lia] |].
    iNext. iIntros "Hli". st. rewrite (Z.mod_small (Z.of_nat j) (2 ^ 32)); [|lia].
    iApply ("HL487" with "[%] [Hli]"); [split; [xkeep | lk_prove] | iRight; iExact "Hli"].
Unshelve. exact treg. exact DfracDiscarded.
Qed.

End store.
End GetoptLongStoreOn.
