(** A caller that calls glibc's getopt again holds the session that the
    previous call left behind. The first blocks of the next call set up
    the private object and then either look for the next argument or go
    on with a group of short options. This file runs those first blocks
    from the caller's session. The caller learns, at each of the two
    places where the blocks end, the exact fields of the object and what
    is known about the saved position in the current word. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptColon GetoptEntry GetoptLongSession GetoptEntryBridge.
Import ListNotations.
Open Scope Z_scope.

(** These controls show which calls start over. A set-up object whose
    index the caller reset to 0 starts over at index 1. *)
Lemma entry_session_ctl_zero : needs_init (mkGetoptState 0 1 0 null 1 null 0 0 0) /\ (if 0 =? 0 then 1 else 0) = 1.
Proof. split; [left; reflexivity | reflexivity]. Qed.

(** A set-up object at index 3 does not start over and keeps index 3. *)
Lemma entry_session_ctl_pos : ~ needs_init (mkGetoptState 3 1 0 null 1 null 0 0 3) /\ (if 3 =? 0 then 1 else 3) = 3.
Proof. unfold needs_init. cbn. split; [lia | reflexivity]. Qed.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptEntrySessionOn (R : Runtime) (LG0 : LogicSig R).
(** The entry module proves the first blocks of the call. *)
Module EN := GetoptEntryOn R LG0.
(** The bridge module turns the session into the object and back into fields. *)
Module BR := GetoptEntryBridgeOn R LG0.
Import BR BR.LSS BR.LSS.S BR.LSS.S.FI BR.LSS.S.FI.ML BR.LSS.S.FI.LG BR.LSS.S.FI.L.

Section entry_session.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance es_stable : SafepointStable (os_wi w0) := EN.C.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance es_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The cursor relation holds only shared strings and pure facts, so it may be used twice. *)
Local Instance es_cursor_persistent ps i s : Persistent (getopt_cursor ps i s).
Proof. unfold getopt_cursor. apply _. Qed.

(** A caller that calls getopt again must know where the first blocks
    of the call leave it. These blocks read the environment when they
    start over, so the caller supplies its rule for that. The call then
    goes one of two ways. If it looks for the next argument, the caller
    gets every field of the object. The object is set up and its limits
    hold. Its index is 1 if the caller had set the index to 0, and it is
    unchanged otherwise. The saved position is null or at the end of a
    string. If the call goes on with short options, the caller gets the
    fields of its own object and the current word. It also learns how
    far into that word the saved position lies, and that the byte there
    is not the end. *)
Lemma wp_getopt_entry_session e n av ar p os lo li lonly pc penv b r ps i (G : iProp Σ) Φ :
  EN.C.I.getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr (mkPtr av (Obj av))) ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v14") e = Some (WInt pc) ->
  Z.of_nat (length ps) = n ->
  getopt_session b r av ar ps i -∗ word_string DfracDiscarded p os -∗ G -∗
  ((∀ e' s s', ⌜entry_state s s' /\
        entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b (print_errors os (gs_err s)) /\
        getopt_bounds n i s /\ gs_initialized s' = 1 /\ 0 <= gs_order s' <= 2 /\ getopt_bounds n (gs_ind s') s' /\
        gs_arg s' = null /\ gs_ind s' = (if i =? 0 then 1 else i) /\
        0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
        0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48⌝ -∗
      live b r -∗ int_cell b 0 (gs_ind s') -∗ int_cell b 4 (gs_err s') -∗ int_cell b 8 (gs_opt s') -∗
      pcell b 16 (gs_arg s') -∗ int_cell b 24 (gs_initialized s') -∗ pcell b 32 (gs_next s') -∗
      int_cell b 40 (gs_order s') -∗ int_cell b 44 (gs_first s') -∗ int_cell b 48 (gs_last s') -∗
      (⌜gs_next s' = null⌝ ∨ word_string DfracDiscarded (gs_next s') []) -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L73") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' s q sq k0, ⌜entry_env e' n (mkPtr av (Obj av)) (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b
          (print_errors os (gs_err s)) /\
        ~ needs_init s /\ gs_ind s = i /\ gs_initialized s = 1 /\ 0 <= gs_order s <= 2 /\ getopt_bounds n i s /\
        0 <= i < n /\ ps !! Z.to_nat i = Some q /\ (k0 < length sq)%nat /\ sbyte sq k0 <> 0 /\
        gs_next s = ptr_add q (Z.of_nat k0) /\ gs_last s <= i /\
        0 < b /\ b mod 8 = 0 /\ b + 56 <= r_end r /\ r_end r <= 2 ^ 48 /\
        0 < av /\ av mod 8 = 0 /\ av + 8 * (n + 1) <= r_end ar /\ r_end ar <= 2 ^ 48⌝ -∗
      word_string DfracDiscarded q sq -∗ word_string DfracDiscarded (gs_next s) (drop k0 sq) -∗
      live b r -∗ int_cell b 0 i -∗ int_cell b 4 (gs_err s) -∗ int_cell b 8 (gs_opt s) -∗ pcell b 16 null -∗
      int_cell b 24 1 -∗ pcell b 32 (gs_next s) -∗ int_cell b 40 (gs_order s) -∗ int_cell b 44 (gs_first s) -∗
      int_cell b 48 (gs_last s) -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L75") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "start") (b_insts getopt_blk_start) (b_jump getopt_blk_start))) : gexpr) {{ Φ }}.
Proof.
  intros Hget Hpenv H0 H2 H4 H6 H8 H10 H12 H14 Hlen.
  iIntros "Hss #Hos HG HK".
  iDestruct (entry_pre with "Hss") as (s tail) "(%Hav & Hs & [%Hbd %Hi0] & #Hk & #Hc)".
  rewrite Hlen in Hav Hbd Hi0.
  iAssert (⌜s = getopt_zero /\ i = 1 \/ gs_initialized s = 1 /\ gs_ind s = i /\ 0 <= gs_order s <= 2⌝)%I as %Hkp.
  { iDestruct "Hk" as "[%H | [%H _]]"; iPureIntro; [left | right]; exact H. }
  iApply (EN.wp_getopt_entry w0 registry ge e n (mkPtr av (Obj av)) p os lo li lonly pc penv b r s tail G
    with "Hs Hos Hc HG"); try (assumption || (unfold getopt_bounds in Hbd; lia)).
  iSplit.
  - iIntros (e' s' (Hst & Henv & Hnt)) "Hs' HG".
    iDestruct (entry_select b r ps i s s' tail with "Hc Hs'") as
      "(%Hp & Hl & Hi & He & Ho & Ha & Hn & Hx & Hr & Hf & Hla & Hcur)";
      [rewrite Hlen; exact Hbd | exact Hkp | exact Hst | exact Hnt |].
    rewrite Hlen in Hp. iDestruct "HK" as "[HK _]".
    iApply ("HK" $! e' s s' with "[%] Hl Hi He Ho Ha Hn Hx Hr Hf Hla Hcur HG").
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat (split; [first [assumption | lia] |]). first [assumption | lia].
  - iIntros (e' s' (Hst & Henv & Hni & Hnn & Htn)) "Hs' HG".
    iDestruct "Hc" as "[%Hn | #Hw]".
    { exfalso. destruct Hst as [(Hn' & _) | (_ & ->)]; [contradiction|]. apply Hnn. exact Hn. }
    iDestruct (entry_cluster b r ps i s s' tail with "Hk Hw Hs'") as (q sq k0)
      "(%Hp & Hwq & Hwd & Hl & Hi & He & Ho & Ha & Hn & Hx & Hr & Hf & Hla)";
      [rewrite Hlen; exact Hbd | exact Hst | exact Hni | exact Hnn | exact Htn |].
    rewrite Hlen in Hp. iDestruct "HK" as "[_ HK]".
    iApply ("HK" $! e' s q sq k0 with "[%] Hwq Hwd Hl Hi He Ho Ha Hn Hx Hr Hf Hla HG").
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
    repeat (split; [first [assumption | lia] |]). first [assumption | lia].
Qed.

End entry_session.
End GetoptEntrySessionOn.
