From Glibc Require Import GlibcProgram.
(** glibc's `c: tfind` searches a binary tree whose root pointer lives in
    a cell that the caller names. The gettext lookup calls it to search
    its cache of translations, and in a program that has translated
    nothing yet that cache is empty. This module proves what the captured
    body does then.

    When the root cell holds null, the function tests that the cell's
    address is not null, reads the cell twice and returns null. It never
    reads the key and never calls the comparison function, so the caller
    lends only a share of the root cell and its lifetime, and gets both
    back unchanged. The examples at the end check from the captured blocks
    that the empty route mentions neither the key nor the comparison
    function, while the block that walks a nonempty tree uses both. *)
From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic StringLogic.
From Glibc Require Import OsWorld OsBlocks FileInv LibioLogic StrlenBits TfindCode.
From Nanofil Require Validate.
From Glibc Require WordString.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.
Import FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** This tactic follows a branch whose condition has become closed. *)
Ltac close_edge := lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
  let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance tfind_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A search of an empty tree needs to read its root cell and nothing
    else. This resource is a share of that cell, holding null, together
    with a share of its object's lifetime. *)
Definition tfind_root (dq : dfrac) (rb ro : Z) (rreg : region) : iProp Σ :=
  liveq dq rb rreg ∗ pcellq dq rb ro null.

(** ## The empty tree

    The root pointer rt points at the cell, which must be aligned and lie
    inside the object's region. The key and the comparison function may be
    any pointers, because this route does not use them. *)

(** The body returns null and gives back the root cell. *)
Lemma wp_glibc_tfind_empty e key rt rb ro rreg dq cmp Φ :
  lookup (TAtom "v0") e = Some (WPtr key) -> lookup (TAtom "v2") e = Some (WPtr rt) ->
  lookup (TAtom "v4") e = Some (WPtr cmp) ->
  (ptr_cap rt = Obj rb \/ ptr_cap rt = Ro rb) -> ptr_addr rt = rb + ro ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  liveq dq rb rreg -∗ pcellq dq rb ro null -∗
  (liveq dq rb rreg -∗ pcellq dq rb ro null -∗ Φ (Ret (WPtr null))) -∗
  WP (ERun (mkFrame glibc_tfind e [] None (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hv0 Hv2 Hv4 Hc Ha Hrb Hro Hal Hend Hreg. iIntros "Hl Hp HK".
  step. step. step. step. branch_symbolic.
  rewrite Ha (Z.mod_small (rb + ro)); [|lia]. change ((0 mod 2 ^ 64) mod 2 ^ 64) with 0.
  replace (rb + ro =? 0) with false by (symmetry; apply Z.eqb_neq; lia). close_edge.
  step. iApply (wp_check_read_dq with "Hl"); [reflexivity | vx | exact Hc | rewrite Ha; ar | rewrite Ha; ar | rewrite Ha; ar |]; iNext; iIntros "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hp [//]"); [reflexivity | vx | exact Hc | rewrite Ha; ar | exact Hal | cbn; lia |].
  iNext. iIntros "Hl Hp _". step. step. iApply (wp_check_read_dq with "Hl"); [reflexivity | vx | exact Hc | rewrite Ha; ar | rewrite Ha; ar | rewrite Ha; ar |]; iNext; iIntros "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hp [//]"); [reflexivity | vx | exact Hc | rewrite Ha; ar | exact Hal | cbn; lia |].
  iNext. iIntros "Hl Hp _". step. step. branch. step.
  iApply wp_ret; [reflexivity | vx |]. iNext. iApply ("HK" with "Hl Hp").
  Unshelve. all: first [exact rreg | exact dq].
Qed.

(** A call of a name bound to the captured body resumes the caller with
    null and the root cell. *)
Lemma wp_call_glibc_tfind_empty f e ls l d g args rest j key rt rb ro rreg dq cmp Φ :
  map_option (arg_x ge e) args = Some [WPtr key; WPtr rt; WPtr cmp] ->
  find_fn ge g = Some (Defined glibc_tfind) ->
  (ptr_cap rt = Obj rb \/ ptr_cap rt = Ro rb) -> ptr_addr rt = rb + ro ->
  0 < rb -> 0 <= ro -> (rb + ro) mod 8 = 0 -> rb + ro + 8 <= r_end rreg -> r_end rreg <= 2 ^ 48 ->
  liveq dq rb rreg -∗ pcellq dq rb ro null -∗
  ▷ (liveq dq rb rreg -∗ pcellq dq rb ro null -∗
     WP (ERun (mkFrame f (put d (WPtr null) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call (CResult d P) (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type.
  intros Hargs Hg Hc Ha Hrb Hro Hal Hend Hreg. iIntros "Hl Hp HK".
  iApply wp_call_bind; [exact Hargs | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_tfind_empty with "Hl Hp"); [reflexivity | reflexivity | reflexivity | exact Hc | exact Ha | lia | lia | exact Hal | exact Hend | exact Hreg |].
  iIntros "Hl Hp". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. iApply ("HK" with "Hl Hp").
Qed.

(** The rules above must not apply to a tree that has nodes. Two shares
    of one cell agree on its contents, so a cell that holds a node's
    address cannot also be lent as an empty root. *)
Lemma tfind_root_nonempty dq1 dq2 rb ro p : 0 <= ptr_addr p < 2 ^ 64 ->
  pcellq dq1 rb ro p -∗ pcellq dq2 rb ro null -∗ ⌜p = null⌝.
Proof using Type.
  intros Hp. iIntros "H1 H2". iDestruct (WordString.ptsq_agree with "H1 H2") as %E; [reflexivity|].
  iPureIntro. destruct p as [a c]. cbn in Hp, E. injection E as Ec E0 E1 E2 E3 E4 E5 E6 E7. subst c.
  assert (a = 0) as ->; [|reflexivity].
  apply zero_word; [exact Hp|]. intros i Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hi' by lia.
  destruct_or! Hi'; subst i; assumption.
Qed.
End rules.

(** ## Controls

    These definitions inspect the captured blocks: which temporaries a
    block reads and whether it calls a function. The parameter v0 holds
    the key and v4 the comparison function. *)

(** This definition finds the block named l in the captured function. *)
Definition tblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks glibc_tfind) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
(** These definitions list the temporaries a block reads, test whether it
    calls a function, and test whether it reads the temporary named x. *)
Definition blk_uses (b : block) : list name :=
  flat_map Validate.inst_uses (b_insts b) ++ Validate.jump_uses (b_jump b) ++
  flat_map (fun '(Phi _ _ ps) => Validate.value_temps (map snd ps)) (b_phis b).
Definition blk_calls (b : block) : bool :=
  existsb (fun i => match i with Call _ _ _ | RawCall _ _ _ => true | _ => false end) (b_insts b).
Definition mentions (x : string) (b : block) : bool :=
  existsb (fun n => match n with TAtom s => String.eqb s x | _ => false end) (blk_uses b).
(** The blocks on the empty route read neither the key nor the comparison
    function and call nothing. *)
Example tfind_empty_route :
  forallb (fun l => negb (mentions "v0" (tblk l)) && negb (mentions "v4" (tblk l)) && negb (blk_calls (tblk l)))
    ["start"; "L11"; "L19"; "L21"] = true.
Proof. vm_compute. reflexivity. Qed.
(** The block that visits a node reads both and calls the comparison. *)
Example tfind_nonempty_route :
  mentions "v0" (tblk "L20") && mentions "v4" (tblk "L20") && blk_calls (tblk "L20") = true.
Proof. vm_compute. reflexivity. Qed.
