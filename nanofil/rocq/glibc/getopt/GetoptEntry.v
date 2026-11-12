(** Each call of glibc's reentrant option scanner begins with the same
    fixed sequence of blocks. The call reads the private diagnostic flag,
    clears the returned argument, and decides whether to initialize the
    private object or resume the previous call. It then skips the
    ordering prefix of the option string, checks for a leading colon, and
    tests the saved cursor. This file composes those blocks of the
    captured [_getopt_internal_r] from the function's first block, for
    any argument count of at least one.

    The result names the scanner state at either exit. An idle cursor
    sends the call to argument selection, and an active cursor sends it
    to option reading. Only a resumed call can have an active cursor,
    because initialization clears the cursor. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize GetoptColon.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.
Local Transparent glibc_getopt_internal_r.

(** ## The scanner state after the first blocks *)

(** Every call clears the returned argument before it scans. *)
Definition clear_arg (s : getopt_state) : getopt_state :=
  mkGetoptState (gs_ind s) (gs_err s) (gs_opt s) null (gs_initialized s) (gs_next s)
    (gs_order s) (gs_first s) (gs_last s).

(** Initialization starts the scan at the public index, or at one when the
    caller reset that index to zero, with no pending nonoptions. *)
Definition init_state (s : getopt_state) (o : Z) : getopt_state :=
  let i := if gs_ind s =? 0 then 1 else gs_ind s in
  mkGetoptState i (gs_err s) (gs_opt s) null 1 null o i i.

(** A fresh object, or an index reset to zero, makes the call initialize. *)
Definition needs_init (s : getopt_state) : Prop := gs_ind s = 0 \/ gs_initialized s = 0.

(** The scanner state after its first blocks is either the initialized
    state or the caller's state with the returned argument cleared. *)
Definition entry_state (s s' : getopt_state) : Prop :=
  (needs_init s /\ exists o, 0 <= o <= 2 /\ s' = init_state s o) \/
  (~ needs_init s /\ s' = clear_arg s).

(** Later blocks read the call's arguments and several values that the
    first blocks computed. This predicate records those values at either
    exit: the option string after its prefix, the diagnostic flag, and
    the checked pointers into the private object. *)
Definition entry_env (e : env) (n : Z) (av p lo li : ptr) (lonly b pe : Z) : Prop :=
  lookup (TAtom "v0") e = Some (WInt n) /\ lookup (TAtom "v2") e = Some (WPtr av) /\
  lookup (TAtom "v6") e = Some (WPtr lo) /\ lookup (TAtom "v8") e = Some (WPtr li) /\
  lookup (TAtom "v10") e = Some (WInt lonly) /\
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) /\
  lookup (TAtom "pr.1") e = Some (WPtr p) /\ lookup (TAtom "pr.3") e = Some (WInt pe) /\
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) /\
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) /\
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) /\
  lookup (TAtom "chk19") e = Some (WPtr p) /\
  lookup (TAtom "chk20") e = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
  lookup (TAtom "v80") e = Some (WInt 0).

(** Signed comparison of a nonnegative 32-bit integer reads its value. *)
Lemma sx_small x : 0 <= x < 2 ^ 31 -> sign_extension (2 ^ 32) (2 ^ 31) (x mod 2 ^ 32) = x.
Proof.
  intros H. unfold sign_extension. rewrite !Z.mod_small; try lia.
  rewrite (proj2 (Z.leb_gt _ _)); lia.
Qed.

(** The function's first block reads the diagnostic flag. *)
Definition getopt_blk_start : block := Eval vm_compute in
  match find_block (TAtom "start") (fn_blocks glibc_getopt_internal_r) with
  | Some b => b | None => mkBlock (TAtom "start") [] [] JUnreachable end.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptEntryOn (R : Runtime) (LG0 : LogicSig R).
(** The colon module supplies initialization, resume and the colon check. *)
Module C := GetoptColonOn R LG0.
Import C C.I C.I.S C.I.S.FI C.I.S.FI.ML C.I.S.FI.LG C.I.S.FI.L C.I.ST C.I.GB.

Section entry.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance entry_stable : SafepointStable (os_wi w0) := C.I.OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance entry_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic loads an owned private integer field as a signed 32-bit value. *)
Ltac load_int H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | arith |];
  iNext; iIntros H.

(** Signed comparisons of nonnegative 32-bit values read the values. *)
Ltac sx := repeat match goal with |- context [sign_extension (2 ^ 32) (2 ^ 31) (?x mod 2 ^ 32)] =>
  rewrite (sx_small x); [|lia] end.

(** This tactic decides a branch whose condition arithmetic settles. *)
Ltac brz :=
  iApply wp_branch; [vx | iNext]; sx;
  repeat match goal with
    | |- context [?x <? ?y] =>
        first [rewrite (proj2 (Z.ltb_lt x y)); [|lia] | rewrite (proj2 (Z.ltb_ge x y)); [|lia]]
    | |- context [?x =? ?y] =>
        first [rewrite (proj2 (Z.eqb_eq x y)); [|lia] | rewrite (proj2 (Z.eqb_neq x y)); [|lia]]
    end;
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** This tactic decides a branch whose condition has become closed. *)
Ltac close_br :=
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** This tactic rebuilds an integer field from its rewritten bytes. *)
Ltac icell := iSplit; [iPureIntro; lia | iAssumption].

(** This tactic proves a lookup through assignments and kept lookups. *)
Ltac lk :=
  first [ apply Symbolic.lookup_after_put_same
        | eapply lookup_put_miss; [vm_compute; reflexivity | lk]
        | eassumption
        | match goal with H : lookup ?k ?E = lookup ?k ?E1 |- lookup ?k ?E = _ => rewrite H; lk end ].

(** Each kept lookup becomes an equation about the new environment. *)
Ltac unkeep Hk :=
  let Hc := fresh "Hkc" in pose proof Hk as Hc;
  unfold keeps, colon_keys, entry_keys in Hc; cbn [List.map] in Hc;
  repeat match type of Hc with Forall _ (_ :: _) => let H := fresh "Hkk" in apply Forall_cons_1 in Hc as [H Hc] end.

(** The first blocks check pointers into the private object and read
    its diagnostic flag. This predicate records those values together
    with the call's arguments. *)
Definition start_env (e : env) (n : Z) (av p lo li : ptr) (lonly b pc err : Z) : Prop :=
  lookup (TAtom "v0") e = Some (WInt n) /\ lookup (TAtom "v2") e = Some (WPtr av) /\
  lookup (TAtom "v4") e = Some (WPtr p) /\ lookup (TAtom "v6") e = Some (WPtr lo) /\
  lookup (TAtom "v8") e = Some (WPtr li) /\ lookup (TAtom "v10") e = Some (WInt lonly) /\
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) /\ lookup (TAtom "v14") e = Some (WInt pc) /\
  lookup (TAtom "v19") e = Some (WInt err) /\
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) /\
  lookup (TAtom "chk1") e = Some (WPtr (mkPtr (b + 16) (Obj b))) /\
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))).

(** Two tests can request initialization, and both reach the same
    inlined code. Initialization clears the cursor, so the call then
    always goes to argument selection. *)
Lemma wp_getopt_entry_init e1 fr n av p os lo li lonly pc penv b r s (tail : list Z) (G : iProp Σ) Φ :
  getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  start_env e1 n av p lo li lonly b pc (gs_err s) -> needs_init s ->
  1 <= n < 2 ^ 31 -> 0 <= gs_ind s <= n -> 0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  live b r -∗ int_cell b 0 (gs_ind s) -∗ int_cell b 4 (gs_err s) -∗ int_cell b 8 (gs_opt s) -∗
  pcell b 16 null -∗ int_cell b 24 (gs_initialized s) -∗ pcell b 32 (gs_next s) -∗
  int_cell b 40 (gs_order s) -∗ int_cell b 44 (gs_first s) -∗ int_cell b 48 (gs_last s) -∗
  word_string DfracDiscarded p os -∗ G -∗
  (∀ e' s', ⌜entry_state s s' /\
       entry_env e' n av (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b (print_errors os (gs_err s)) /\
       (gs_next s' = null \/ tail = [])⌝ -∗ getopt_state_own b r s' -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L73") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e1 [] None (Enter (TAtom "iw_1.start") (Some fr))) : gexpr) {{ Φ }}.
Proof.
  intros Hget Hpenv (H0 & H2 & H4 & H6 & H8 & H10 & H12 & H14 & H19 & Hc0 & Hc1 & Hc2) Hni Hn Hi Hb Hal Hend Hr.
  iIntros "Hl Hi [%Herr Heb] Ho Ha Hini Hnext Hord Hf Hla #Hos HG HK".
  st. iApply (wp_getopt_initialize w0 registry ge _ n p os b r s pc penv G
    with "Hl Hi Hini Hnext Hord Hf Hla Hos HG"); try assumption; try lia.
  iIntros (e2 o (Hk & Ho)) "Hl Hi Hini Hnext Hord Hf Hla HG". unkeep Hk.
  iApply (wp_getopt_colon w0 registry ge _ p os b r null tail (gs_err s) with "Hl Hnext Hos []");
    try lk; try lia; [by iLeft|]. iSplit.
  - iIntros (e3 ((Hk3 & H3 & H19' & H20 & H80) & _)) "Hl Hnext". unkeep Hk3.
    iApply ("HK" $! e3 (init_state s o) with "[%] [-HG] HG").
    + split; [left; split; [exact Hni | exists o; split; [exact Ho | reflexivity]]|].
      split; [repeat split; lk | left; reflexivity].
    + unfold getopt_state_own, init_state; cbn [gs_ind gs_err gs_opt gs_arg gs_initialized gs_next
        gs_order gs_first gs_last]. iFrame. iPureIntro; repeat split; lia.
  - iIntros (e3 [_ [Hnn _]]). by exfalso.
Qed.

(** The first blocks of a call either initialize the private object or
    resume it, and then reach argument selection or option reading. The
    caller's getenv rule covers the environment query of initialization. *)
Lemma wp_getopt_entry e n av p os lo li lonly pc penv b r s tail (G : iProp Σ) Φ :
  getenv_rule w0 registry ge G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  lookup (TAtom "v0") e = Some (WInt n) -> lookup (TAtom "v2") e = Some (WPtr av) ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v6") e = Some (WPtr lo) ->
  lookup (TAtom "v8") e = Some (WPtr li) -> lookup (TAtom "v10") e = Some (WInt lonly) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "v14") e = Some (WInt pc) ->
  1 <= n < 2 ^ 31 -> 0 <= gs_ind s <= n ->
  getopt_state_own b r s -∗ word_string DfracDiscarded p os -∗
  (⌜gs_next s = null⌝ ∨ word_string DfracDiscarded (gs_next s) tail) -∗ G -∗
  ((∀ e' s', ⌜entry_state s s' /\
       entry_env e' n av (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b (print_errors os (gs_err s)) /\
       (gs_next s' = null \/ tail = [])⌝ -∗ getopt_state_own b r s' -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L73") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e' s', ⌜entry_state s s' /\
       entry_env e' n av (ptr_add p (Z.of_nat (opt_skip os))) lo li lonly b (print_errors os (gs_err s)) /\
       ~ needs_init s /\ gs_next s' <> null /\ tail <> []⌝ -∗ getopt_state_own b r s' -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L75") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "start") (b_insts getopt_blk_start) (b_jump getopt_blk_start))) : gexpr) {{ Φ }}.
Proof.
  intros Hget Hpenv Hv0 Hv2 Hv4 Hv6 Hv8 Hv10 Hv12 Hv14 Hn Hi.
  iIntros "(%Hown & Hl & Hi & He & Ho & Ha & Hini & Hnext & Hord & Hf & Hla) #Hos #Hcur HG HK".
  destruct Hown as (Hb & Hal & Hend & Hr).
  iDestruct "He" as "[%Herr Heb]". cbn [b_insts b_jump getopt_blk_start].
  st. norm. chk "Hl". load_int "Hl Heb". st.
  brz.
  st. st. norm. chk "Hl".
  iApply (wp_raw_store_pointer with "Hl Ha"); [vx | vx | reflexivity | arith | arith | wi_store |].
  iNext. iIntros "Hl Ha". chk "Hl". iDestruct "Hi" as "[%Hi0 Hib]". load_int "Hl Hib". st.
  norm. iApply wp_branch; [vx | iNext].
  destruct (Z.eqb_spec (gs_ind s) 0) as [E0|E0]; close_br.
  { st. br. iDestruct "HK" as "[HK _]".
    iApply (wp_getopt_entry_init with "Hl [Hib] [Heb] Ho Ha Hini Hnext Hord Hf Hla Hos HG HK");
      [exact Hget | exact Hpenv | repeat split; lk | left; exact E0 | lia | lia | lia | lia | lia | lia | icell | icell]. }
  st. st. norm. chk "Hl". iDestruct "Hini" as "[%Hn0 Hinib]". load_int "Hl Hinib". st. norm. st. st.
  iApply wp_branch; [vx | iNext].
  destruct (Z.eqb_spec (gs_initialized s) 0) as [I0|I0]; close_br.
  { iDestruct "HK" as "[HK _]".
    iApply (wp_getopt_entry_init with "Hl [Hib] [Heb] Ho Ha [Hinib] Hnext Hord Hf Hla Hos HG HK");
      [exact Hget | exact Hpenv | repeat split; lk | right; exact I0 | lia | lia | lia | lia | lia | lia | icell | icell | icell]. }
  st. iApply (wp_getopt_resume w0 registry ge _ p os with "Hos"); [lk|].
  iIntros (e1 Hk1). unkeep Hk1.
  iApply (wp_getopt_colon w0 registry ge _ p os b r (gs_next s) tail (gs_err s) with "Hl Hnext Hos Hcur");
    try lk; try lia. iSplit.
  - iIntros (e3 ((Hk3 & H3 & H19' & H20 & H80) & Hidle)) "Hl Hnext". unkeep Hk3.
    iDestruct "HK" as "[HK _]". iApply ("HK" $! e3 (clear_arg s) with "[%] [-HG] HG").
    + split; [right; split; [unfold needs_init; lia | reflexivity]|]. split; [repeat split; lk | exact Hidle].
    + unfold getopt_state_own, clear_arg; cbn [gs_ind gs_err gs_opt gs_arg gs_initialized gs_next
        gs_order gs_first gs_last]. iFrame. iPureIntro; repeat split; lia.
  - iIntros (e3 ((Hk3 & H3 & H19' & H20 & H80) & Hnn & Htn)) "Hl Hnext". unkeep Hk3.
    iDestruct "HK" as "[_ HK]". iApply ("HK" $! e3 (clear_arg s) with "[%] [-HG] HG").
    + split; [right; split; [unfold needs_init; lia | reflexivity]|].
      split; [repeat split; lk|]. split; [unfold needs_init; lia | split; [exact Hnn | exact Htn]].
    + unfold getopt_state_own, clear_arg; cbn [gs_ind gs_err gs_opt gs_arg gs_initialized gs_next
        gs_order gs_first gs_last]. iFrame. iPureIntro; repeat split; lia.
Qed.

End entry.
End GetoptEntryOn.
