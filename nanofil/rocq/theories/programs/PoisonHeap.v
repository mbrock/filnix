(** A heap-using program can process secret bytes without exposing their
    values through branches or addresses. This example allocates a scratch
    object, scans an arbitrary input length through recursive helper calls,
    selects values without branching on secrets, and frees the scratch object.

    The proof shows that no access fails and no secret controls a branch
    or address. It uses [[iris|Iris]] to track bytes and [[poison]] restrictions
    together. Related inputs produce equal finite IR leakage traces under
    the same deterministic runtime driver; this does not prove native timing. *)

From Stdlib Require Import String ZArith List Bool Lia Relations.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import weakestpre.
From iris.program_logic Require Import adequacy.
From iris.base_logic.lib Require Import gen_heap.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics
  Run Machine Panics StepRules Pieces Heap Language Logic PoisonModel PoisonLogic.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The byte-loop program

    Only the public byte count controls iteration. Each [[stage|checked IR]]
    iteration reads the next secret byte and uses branchless selection
    before writing a single reusable scratch slot. *)

(** An iteration reads one byte, selects a value, stores it, and recurses. *)
Definition loop_body : list inst :=
  [Let (TAtom "x") W (RawLoad (LdNarrow Ub) 0) [Tmp (TAtom "s")];
   Let (TAtom "z") W Select [Tmp (TAtom "x"); Const 9; Const 17];
   RawStore Wb 0 (Tmp (TAtom "z")) (Tmp (TAtom "d"));
   Let (TAtom "s1") P Add [Tmp (TAtom "s"); Const 1];
   Let (TAtom "n1") W Sub [Tmp (TAtom "n"); Const 1];
   Call CVoid (Global (TAtom "loop"))
     [Arg P (Tmp (TAtom "s1")); Arg P (Tmp (TAtom "d")); Arg W (Tmp (TAtom "n1"))]].
(** The helper stops at zero and otherwise executes one byte iteration. *)
Definition loop_fn : func := mkFunc (TAtom "loop") (TAtom "export") (RClass W)
  [(P, TAtom "s"); (P, TAtom "d"); (W, TAtom "n")]
  [mkBlock (TAtom "entry") [] []
      (JBranch (Tmp (TAtom "n")) (To (TAtom "body")) (To (TAtom "end")));
   mkBlock (TAtom "body") [] loop_body (JRet (Const 0));
   mkBlock (TAtom "end") [] [] (JRet (Const 0))].
(** The helper receives source and destination pointers and a public count. *)
Definition loop_env s d n : env := [(TAtom "n", WInt n); (TAtom "d", WPtr d); (TAtom "s", WPtr s)].
(** Both pointers and the count enter the helper without restrictions. *)
Definition loop_te : tenv := [(TAtom "n", WTInt taint_bot);
  (TAtom "d", WTPtr taint_bot taint_bot); (TAtom "s", WTPtr taint_bot taint_bot)].
(** A helper call starts at its entry block. *)
Definition loop_entry s d n := mkFrame loop_fn (loop_env s d n) [] None (Enter (TAtom "entry") None).

(** The kernel allocates scratch space, calls the byte loop, and frees it. *)
Definition kernel_fn : func := mkFunc (TAtom "kernel") (TAtom "export") (RClass W)
  [(P, TAtom "s"); (W, TAtom "n")]
  [mkBlock (TAtom "entry") []
    [Let (TAtom "d") P (Alloc 16) [Const 1];
     Call CVoid (Global (TAtom "loop"))
       [Arg P (Tmp (TAtom "s")); Arg P (Tmp (TAtom "d")); Arg W (Tmp (TAtom "n"))];
     Call CVoid (Global free_name) [Arg P (Tmp (TAtom "d"))]] (JRet (Const 0))].
(** The kernel receives an input pointer and its public length. *)
Definition kernel_env s n : env := [(TAtom "n", WInt n); (TAtom "s", WPtr s)].
(** The input pointer and its length are public; the pointed-to bytes are not. *)
Definition kernel_te : tenv := [(TAtom "n", WTInt taint_bot); (TAtom "s", WTPtr taint_bot taint_bot)].
(** A kernel call starts at its allocation block. *)
Definition kernel_entry s n := mkFrame kernel_fn (kernel_env s n) [] None (Enter (TAtom "entry") None).

(** The initial value heap records consecutive input bytes. *)
Fixpoint input_ps b o (xs : list Z) : list (piece * pval) :=
  match xs with [] => [] | x :: xs => (PByte b o, VByte x) :: input_ps b (o + 1) xs end.
(** Every input byte carries all three secret restrictions. *)
Definition input_pps b o (xs : list Z) := pbytes_ps b o (replicate (length xs) (pb_secret taint_all)).

(** Branching on a secret is rejected even when both targets are identical. *)
Lemma secret_branch_rejected pol ge f l n x m pm paux fuel :
  pstep pol ge
    (mkConfig (mkFrame f [(n, WInt x)] [] None
      (Exec l [] (JBranch (Tmp n) (To l) (To l)))) [] m fuel)
    (mkPState [(n, WTInt taint_all)] [] pm paux) = PTrap CannotBranch.
Proof. unfold pstep, tstep, jump_tstep. cbn. rewrite /name_eqb term_eqb_refl. reflexivity. Qed.

(** A secret address is rejected before the ordinary memory access runs. *)
Lemma secret_index_rejected pol ge f l n p m pm paux fuel :
  pstep pol ge
    (mkConfig (mkFrame f [(n, WPtr p)] [] None
      (Exec l [Let n W (RawLoad (LdNarrow Ub) 0) [Tmp n]] (JRet (Const 0)))) [] m fuel)
    (mkPState [(n, WTPtr taint_all taint_bot)] [] pm paux) = PTrap CannotIndex.
Proof. unfold pstep, tstep, inst_tstep, let_tstep. cbn. rewrite /name_eqb term_eqb_refl. reflexivity. Qed.

(** ## Owning the loop's memory

    The loop borrows input bytes and updates a scratch byte. Its
    [[separation-logic]] proof preserves the scratch object's lifetime
    token so that the caller can free the object after the helper returns. *)

Module PoisonHeap (R : Runtime).
Module PL := PoisonLogic R.
Import PL.
Section proof.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ, !gen_heapGS ppiece ppval Σ}.
Context (pol : poison_policy) (ge : genv).
Local Instance heap_poisonGS : irisGS_gen hlc (poison_lang pol ge) Σ := poison_irisGS pol ge.
Local Notation pexprL := (language.expr (poison_lang pol ge)).
(** Each input byte is owned together with its secret restrictions. *)
Fixpoint secret_bytes b o (xs : list Z) : iProp Σ :=
  match xs with
  | [] => True%I
  | x :: xs => (pts [(PByte b o, VByte x)] ∗
      ppts [(PPByte b o, VPByte (pb_secret taint_all))] ∗ secret_bytes b (o + 1) xs)%I
  end.
(** The loop handles every input list whose public length fits in 32 bits. *)
Lemma loop_spec xs : forall b reg o c creg y pb,
  0 <= b -> 0 <= o -> b + o + Z.of_nat (length xs) <= 2 ^ 48 ->
  Z.of_nat (length xs) < 2 ^ 32 -> 0 <= c < 2 ^ 48 -> pb_no_store pb = false ->
  find_fn ge (TAtom "loop") = Some (Defined loop_fn) ->
  pts [(PLive b, VLive reg)] -∗ secret_bytes b o xs -∗
  pts [(PLive c, VLive creg); (PByte c 0, VByte y)] -∗ ppts [(PPByte c 0, VPByte pb)] -∗
  WP (PRun (loop_entry (mkPtr (b + o) (Obj b)) (mkPtr c (Obj c)) (Z.of_nat (length xs))) loop_te : pexprL)
    {{ v, ⌜v = (Ret (WInt 0), [WTInt taint_bot])⌝ ∗
      ∃ y' pb', ⌜pb_no_store pb' = false⌝ ∗
        pts [(PLive c, VLive creg); (PByte c 0, VByte y')] ∗ ppts [(PPByte c 0, VPByte pb')] }}.
Proof.
  induction xs as [|x xs IH]; intros b reg o c creg y pb Hb Ho Hbound Hn Hc Hpb Hfn;
    iIntros "Hl Hxs Hd Hpd".
  - iApply wp_penter; [reflexivity|reflexivity|reflexivity|]. iNext.
    iApply wp_pbranch; [reflexivity|reflexivity|reflexivity|]. iNext.
    iApply wp_penter; [reflexivity|reflexivity|reflexivity|]. iNext.
    iApply wp_pret; [reflexivity|reflexivity|reflexivity|]. iNext.
    iSplit; [done|]. iExists y, pb. iFrame. done.
  - change (Z.of_nat (length (x :: xs))) with (Z.of_nat (S (length xs))) in *.
    assert (Hlen : 0 < Z.of_nat (S (length xs)) < 2 ^ 32) by lia.
    iApply wp_penter; [reflexivity|reflexivity|reflexivity|]. iNext.
    iApply (wp_pbranch pol ge _ _ _ _ _ _ _ _ (Z.of_nat (S (length xs))) taint_bot).
    { change (Some (WInt (Z.of_nat (S (length xs)) mod 2 ^ 32)) = Some (WInt (Z.of_nat (S (length xs))))).
      rewrite (Z.mod_small (Z.of_nat (S (length xs))) (2 ^ 32) ltac:(lia)). reflexivity. }
    { reflexivity. } { reflexivity. } iNext.
    rewrite (proj2 (Z.eqb_neq (Z.of_nat (S (length xs))) 0) ltac:(lia)).
    iApply wp_penter; [reflexivity|reflexivity|reflexivity|]. iNext.
    cbn [b_insts b_jump loop_body].
    iDestruct "Hxs" as "(Hx & Hpx & Hxs)".
    iApply (wp_praw_load_byte pol ge _ _ _ _ _ _ _ _ _ _ _ _ _ b reg o x
      (WInt (x mod 256)) (pb_secret taint_all) taint_bot taint_bot
      (DfracOwn 1) (DfracOwn 1) with "[Hl Hx] Hpx").
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    { unfold extended. cbn. rewrite (Z.mod_small (x mod 256) (2 ^ 32) ltac:(pose proof (Z.mod_pos_bound x 256 ltac:(lia)); lia)). reflexivity. }
    { by left. }
    { change ((b + o + 0) mod 2 ^ 64 = b + o). rewrite Z.add_0_r (Z.mod_small (b + o) (2 ^ 64) ltac:(lia)). reflexivity. }
    { reflexivity. } { apply andb_false_r. } { reflexivity. }
    { rewrite /pts /ptsq !big_sepL_cons. iDestruct "Hl" as "[$ _]". iDestruct "Hx" as "[$ _]". done. }
    iNext. iIntros "Hread _".
    rewrite /ptsq !big_sepL_cons. iDestruct "Hread" as "(Hl & _ & _)".
    iAssert (pts [(PLive b, VLive reg)]) with "[Hl]" as "Hl"; [rewrite /pts; iFrame; done|].
    iApply (wp_plet pol ge _ _ _ _ _ _ _ _ _ _ _ _ _
      (WInt (if x mod 256 =? 0 then 17 else 9)) (WTInt taint_all));
      [reflexivity|reflexivity| | | |].
    { reflexivity. }
    { intros m.
      rewrite (Z.mod_small (x mod 256) (2 ^ 32) ltac:(pose proof (Z.mod_pos_bound x 256 ltac:(lia)); lia)).
      reflexivity. }
    { intros pm paux. reflexivity. }
    iNext.
    iApply (wp_praw_store_byte pol ge _ _ _ _ _ _ _ _ _ _ _ c creg 0 y
      (if x mod 256 =? 0 then 17 else 9) pb taint_all taint_bot taint_bot with "Hd Hpd").
    { cbn [value_x lookup put word_at_class]. destruct (x mod 256 =? 0); reflexivity. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    { change ((c + 0) mod 2 ^ 64 = c + 0). rewrite Z.add_0_r (Z.mod_small c (2 ^ 64) ltac:(lia)). reflexivity. }
    { reflexivity. } { apply andb_false_r. } { exact Hpb. }
    iNext. iIntros "Hd Hpd".
    iApply (wp_plet pol ge _ _ _ _ _ _ _ _ _ _ _ _ _
      (WPtr (mkPtr (b + (o + 1)) (Obj b))) (WTPtr taint_bot taint_bot));
      [reflexivity|reflexivity|reflexivity| | |].
    { intros m. change (Some (OpRes (RVal (WPtr (mkPtr ((b + o + 1) mod 2 ^ 64) (Obj b)))) m) =
        Some (OpRes (RVal (WPtr (mkPtr (b + (o + 1)) (Obj b)))) m)).
      rewrite (Z.mod_small (b + o + 1) (2 ^ 64) ltac:(rewrite Nat2Z.inj_succ in Hbound; lia)).
      replace (b + o + 1) with (b + (o + 1)) by lia. reflexivity. }
    { intros pm paux. reflexivity. }
    iNext.
    iApply (wp_plet pol ge _ _ _ _ _ _ _ _ _ _ _ _
      [WInt (Z.of_nat (S (length xs))); WInt 1]
      (WInt (Z.of_nat (length xs))) (WTInt taint_bot)); [reflexivity|reflexivity| | | |].
    { change (Some [WInt (Z.of_nat (S (length xs)) mod 2 ^ 32); WInt 1] =
        Some [WInt (Z.of_nat (S (length xs))); WInt 1]).
      rewrite (Z.mod_small (Z.of_nat (S (length xs))) (2 ^ 32) ltac:(lia)). reflexivity. }
    { intros m. change (Some (OpRes (RVal (WInt ((Z.of_nat (S (length xs)) - 1) mod 2 ^ 32))) m) =
        Some (OpRes (RVal (WInt (Z.of_nat (length xs)))) m)).
      rewrite (Z.mod_small (Z.of_nat (S (length xs)) - 1) (2 ^ 32) ltac:(rewrite Nat2Z.inj_succ; lia)).
      replace (Z.of_nat (S (length xs)) - 1) with (Z.of_nat (length xs)) by lia. reflexivity. }
    { intros pm paux. reflexivity. }
    iNext.
    iApply (wp_pcall_bind pol ge _ _ _ _ _ _ _ _ _ _
      [WPtr (mkPtr (b + (o + 1)) (Obj b)); WPtr (mkPtr c (Obj c)); WInt (Z.of_nat (length xs))]
      [WTPtr taint_bot taint_bot; WTPtr taint_bot taint_bot; WTInt taint_bot]
      loop_fn (loop_entry (mkPtr (b + (o + 1)) (Obj b)) (mkPtr c (Obj c)) (Z.of_nat (length xs))) loop_te).
    { change (Some [WPtr (mkPtr (b + (o + 1)) (Obj b)); WPtr (mkPtr c (Obj c));
        WInt (Z.of_nat (length xs) mod 2 ^ 32)] =
        Some [WPtr (mkPtr (b + (o + 1)) (Obj b)); WPtr (mkPtr c (Obj c)); WInt (Z.of_nat (length xs))]).
      rewrite (Z.mod_small (Z.of_nat (length xs)) (2 ^ 32) ltac:(lia)).
      reflexivity. }
    { reflexivity. } { exact Hfn. } { reflexivity. } { reflexivity. } { reflexivity. }
    iNext.
    iApply (wp_wand with "[-]").
    { iApply (IH b reg (o + 1) c creg with "Hl Hxs Hd Hpd");
        try assumption; try (rewrite Nat2Z.inj_succ in Hbound; lia). }
    iIntros (v) "[%Hv Hout]". subst v.
    iExists _, _. iSplit; [iPureIntro; reflexivity|]. iNext.
    iApply wp_pret; [reflexivity|reflexivity|reflexivity|]. iNext.
    iFrame. done.
Qed.

(** Initial ownership from the two maps supplies the loop's input assertion. *)
Lemma input_ownership b o xs :
  pts (input_ps b o xs) -∗ ppts (input_pps b o xs) -∗ secret_bytes b o xs.
Proof.
  revert o. induction xs as [|x xs IH]; intros o; iIntros "Hv Hp"; [done|].
  rewrite /pts /ppts /=.
  iDestruct "Hv" as "[Hv Hvs]". iDestruct "Hp" as "[Hp Hps]".
  iSplitL "Hv"; [rewrite /pts; iFrame; done|].
  iSplitL "Hp"; [rewrite /ppts; iFrame; done|].
  iApply (IH with "Hvs Hps").
Qed.

(** The kernel's proof composes allocation, the helper, and deallocation. *)
Lemma kernel_spec b reg o xs :
  0 <= b -> 0 <= o -> b + o + Z.of_nat (length xs) <= 2 ^ 48 ->
  Z.of_nat (length xs) < 2 ^ 32 ->
  find_fn ge (TAtom "loop") = Some (Defined loop_fn) ->
  frees_heap (ge_free ge) -> find_fn ge free_name = None -> lookup free_name (ge_globals ge) = None ->
  pts ((PLive b, VLive reg) :: input_ps b o xs) -∗ ppts (input_pps b o xs) -∗
  WP (PRun (kernel_entry (mkPtr (b + o) (Obj b)) (Z.of_nat (length xs))) kernel_te : pexprL)
    {{ v, ⌜v = (Ret (WInt 0), [WTInt taint_bot])⌝ }}.
Proof.
  intros Hb Ho Hbound Hn Hloop Hfree Hfn Hdata. iIntros "Hv Hp".
  rewrite /pts big_sepL_cons. iDestruct "Hv" as "[Hl Hv]".
  iAssert (pts [(PLive b, VLive reg)]) with "[Hl]" as "Hl"; [rewrite /pts; iFrame; done|].
  iDestruct (input_ownership with "Hv Hp") as "Hxs".
  iApply wp_penter; [reflexivity|reflexivity|reflexivity|]. iNext.
  iApply (wp_palloc_heap pol ge _ _ _ _ _ _ _ _ _ _ _ 1);
    [reflexivity|reflexivity|lia|vm_compute; discriminate|].
  iNext. iIntros (c (Hc & Hmod & Hend)) "Hd Hpd".
  change (c + 16 <= 2 ^ 48) in Hend.
  iDestruct "Hd" as "(Hlive & Hbyte & _)".
  iDestruct "Hpd" as "(Hpoison & _)".
  iDestruct "Hbyte" as "[Hbyte _]". iDestruct "Hpoison" as "[Hpoison _]".
  iAssert (pts [(PLive c, VLive (mkRegion c (c + 16) Heap Live)); (PByte c 0, VByte 0)])
    with "[Hlive Hbyte]" as "Hd".
  { rewrite /pts !big_sepL_cons. iFrame. done. }
  iAssert (ppts [(PPByte c 0, VPByte pb_clean)]) with "[Hpoison]" as "Hpd".
  { rewrite /ppts !big_sepL_cons. iFrame. done. }
  iApply (wp_pcall_bind pol ge _ _ _ _ _ _ _ _ _ _
    [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr c (Obj c)); WInt (Z.of_nat (length xs))]
    [WTPtr taint_bot taint_bot; WTPtr taint_bot taint_bot; WTInt taint_bot]
    loop_fn (loop_entry (mkPtr (b + o) (Obj b)) (mkPtr c (Obj c)) (Z.of_nat (length xs))) loop_te).
  { change (Some [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr c (Obj c)); WInt (Z.of_nat (length xs) mod 2 ^ 32)] =
      Some [WPtr (mkPtr (b + o) (Obj b)); WPtr (mkPtr c (Obj c)); WInt (Z.of_nat (length xs))]).
    rewrite (Z.mod_small (Z.of_nat (length xs)) (2 ^ 32) ltac:(lia)). reflexivity. }
  { reflexivity. } { exact Hloop. } { reflexivity. } { reflexivity. } { reflexivity. }
  iNext. iApply (wp_wand with "[-]").
  { iApply (loop_spec xs b reg o c _ 0 pb_clean with "Hl Hxs Hd Hpd"); try assumption; try reflexivity; lia. }
  iIntros (v) "[%Hv Hout]". subst v. iExists _, _.
  iSplit; [iPureIntro; reflexivity|]. iNext.
  iDestruct "Hout" as (y pb) "(%Hpb & Hd & Hpd)".
  rewrite /pts !big_sepL_cons. iDestruct "Hd" as "(Hl & _ & _)".
  iApply (wp_pfree_sym pol ge free_name _ _ _ _ _ _ _ _ c (mkRegion c (c + 16) Heap Live) with "[Hl]");
    [reflexivity|exact Hfree|exact Hfn|exact Hdata|reflexivity|reflexivity|reflexivity|lia| |].
  { rewrite /pts. iFrame. done. }
  iNext. iApply wp_pret; [reflexivity|reflexivity|reflexivity|]. iNext. done.
Qed.
End proof.

(** ## Safety and constant time

    A proof over owned bytes gives guarantees for every reachable machine
    state, including collector steps. The [[runtime]] driver theorem
    separately compares finite traces of two related secret inputs. *)

(** The kernel avoids ordinary failures and poison faults from a valid input heap. *)
Theorem kernel_safe Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    {HpoisonP : gen_heapGpreS ppiece ppval Σ}
    pol ge b reg o xs m pm paux s fuel :
  0 <= b -> 0 <= o -> b + o + Z.of_nat (length xs) <= 2 ^ 48 ->
  Z.of_nat (length xs) < 2 ^ 32 ->
  find_fn ge (TAtom "loop") = Some (Defined loop_fn) ->
  frees_heap (ge_free ge) -> find_fn ge free_name = None -> lookup free_name (ge_globals ge) = None ->
  R.ready s m -> live_disjoint m ->
  all_agree m ((PLive b, VLive reg) :: input_ps b o xs) -> all_p_agree m pm paux (input_pps b o xs) ->
  NoDup (((PLive b, VLive reg) :: input_ps b o xs).*1) -> NoDup ((input_pps b o xs).*1) ->
  poison_safe pol ge (kernel_entry (mkPtr (b + o) (Obj b)) (Z.of_nat (length xs))) kernel_te m pm paux s fuel.
Proof.
  intros Hb Ho Hbound Hn Hloop Hfree Hfn Hdata Hr Hd Ha Hpa Hnd Hpnd.
  apply (wp_poison_safe _ _ _ _ _ _ _ _ _ (fun v _ => v = (Ret (WInt 0), [WTInt taint_bot]))).
  apply (poison_pieces_adequate Σ pol ge _ _ _ _ _ _ fuel
    ((PLive b, VLive reg) :: input_ps b o xs) (input_pps b o xs)
    (fun v => v = (Ret (WInt 0), [WTInt taint_bot]))); try assumption.
  intros HinvG HheapG HpoisonG. simpl. iIntros "Hv Hp".
  iApply (kernel_spec pol ge b reg o xs with "Hv Hp"); assumption.
Qed.

(** Related secret contents give the same finite traces under one driver. *)
Theorem kernel_ct Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    {HpoisonP : gen_heapGpreS ppiece ppval Σ}
    pol ge b reg o xs m1 m2 pm paux s fuel :
  0 <= b -> 0 <= o -> b + o + Z.of_nat (length xs) <= 2 ^ 48 ->
  Z.of_nat (length xs) < 2 ^ 32 ->
  pol_check_branches pol = true -> ge_free ge = free_res ->
  find_fn ge (TAtom "loop") = Some (Defined loop_fn) ->
  find_fn ge free_name = None -> lookup free_name (ge_globals ge) = None ->
  R.ready s m1 -> R.ready s m2 -> live_disjoint m1 ->
  all_agree m1 ((PLive b, VLive reg) :: input_ps b o xs) -> all_p_agree m1 pm paux (input_pps b o xs) ->
  NoDup (((PLive b, VLive reg) :: input_ps b o xs).*1) -> NoDup ((input_pps b o xs).*1) ->
  ct_rel (mkConfig (kernel_entry (mkPtr (b + o) (Obj b)) (Z.of_nat (length xs))) [] m1 fuel)
    (mkConfig (kernel_entry (mkPtr (b + o) (Obj b)) (Z.of_nat (length xs))) [] m2 fuel)
    (mkPState kernel_te [] pm paux) ->
  forall steps, exists tr,
    PD.pdriver_trace pol ge steps
      (mkConfig (kernel_entry (mkPtr (b + o) (Obj b)) (Z.of_nat (length xs))) [] m1 fuel)
      (mkPState kernel_te [] pm paux) s = Some tr /\
    PD.pdriver_trace pol ge steps
      (mkConfig (kernel_entry (mkPtr (b + o) (Obj b)) (Z.of_nat (length xs))) [] m2 fuel)
      (mkPState kernel_te [] pm paux) s = Some tr.
Proof.
  intros Hb Ho Hbound Hn Hcb Hfree Hloop Hfn Hdata Hr1 Hr2 Hd Ha Hpa Hnd Hpnd Hrel.
  apply wp_ct_driver; try assumption.
  apply (kernel_safe Σ pol ge b reg o xs); try assumption.
  rewrite Hfree. exact free_res_succeeds.
Qed.

(** A module containing the kernel never panics when its initialized memory
    supplies the input bytes and its admitted arguments name that input. *)
Theorem kernel_never_panics Σ {HinvP : invGpreS Σ} {HheapP : gen_heapGpreS piece pval Σ}
    {HpoisonP : gen_heapGpreS ppiece ppval Σ}
    (pol : poison_policy) md globals m b reg o xs pm paux :
  initial_memory md = Some (globals, m) ->
  find_fn (P.program_genv md globals) (TAtom "kernel") = Some (Defined kernel_fn) ->
  find_fn (P.program_genv md globals) (TAtom "loop") = Some (Defined loop_fn) ->
  find_fn (P.program_genv md globals) free_name = None -> lookup free_name globals = None ->
  0 <= b -> 0 <= o -> b + o + Z.of_nat (length xs) <= 2 ^ 48 -> Z.of_nat (length xs) < 2 ^ 32 ->
  live_disjoint m -> all_agree m ((PLive b, VLive reg) :: input_ps b o xs) ->
  all_p_agree m pm paux (input_pps b o xs) ->
  NoDup (((PLive b, VLive reg) :: input_ps b o xs).*1) -> NoDup ((input_pps b o xs).*1) ->
  P.never_panics md (TAtom "kernel")
    (fun args => args = [WPtr (mkPtr (b + o) (Obj b)); WInt (Z.of_nat (length xs))]).
Proof.
  intros Hm Hkernel Hloop Hfn Hdata Hb Ho Hbound Hn Hd Ha Hpa Hnd Hpnd.
  apply (poison_pieces_never_panics Σ pol md (TAtom "kernel") _ globals m kernel_fn
    ((PLive b, VLive reg) :: input_ps b o xs)); try assumption.
  intros args ->. exists (kernel_entry (mkPtr (b + o) (Obj b)) (Z.of_nat (length xs))),
    kernel_te, pm, paux, (input_pps b o xs).
  split; [reflexivity|]. split; [exact Hpa|]. split; [exact Hpnd|].
  intros HinvG HheapG HpoisonG. simpl. iIntros "Hv Hp".
  iApply (wp_wand with "[-]"); [|iIntros (v) "_"; done].
  iApply (kernel_spec pol (P.program_genv md globals) b reg o xs with "Hv Hp");
    try assumption. exact R.free_succeeds.
Qed.
End PoisonHeap.
