From Glibc Require Import GlibcProgram.
(** Each call of glibc's reentrant option scanner first initializes its
    private object or resumes the previous call's state. A resumed call
    must still skip the ordering prefix of the option string. Every call
    then asks two questions before scanning: whether the option string
    starts with a colon, which silences diagnostics, and whether a short
    option cluster is still in progress. This file proves those blocks of
    the captured [_getopt_internal_r] on the object's real cursor cell.

    A saved cursor is null, or it points into a string that the caller
    shares read-only. The scanner reads the cursor's first character. An
    empty suffix sends the call to the block that selects the next
    argument, and a nonempty suffix sends it to the block that reads the
    next option character. *)

From Glibc Require Import GlibcTactics LibioTactics.
From Glibc Require Import GlibcEnv.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes
  GetoptInitialize.
From Glibc Require FileInv GetoptBytes GetoptInitialize GetoptState LibioLogic OsWorld.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.
Local Transparent glibc_getopt_internal_r.

(** ## What these blocks compute *)

(** Diagnostics stay enabled unless the option string starts with a
    colon after its ordering prefix. *)
Definition print_errors (os : list Z) (err : Z) : Z :=
  if sbyte os (opt_skip os) =? 58 then 0 else err.

(** The ordering prefix is at most one character of the option string. *)
Lemma opt_skip_le os : (opt_skip os <= length os)%nat.
Proof.
  unfold opt_skip. destruct os as [|c os]; [reflexivity|]. cbn [length].
  destruct (_ || _); lia.
Qed.

(** Pointer arithmetic below the 64-bit wrap adds exactly. *)
Lemma addr_add a k : 0 <= a -> 0 <= k -> a + k < 2 ^ 64 ->
  (a mod 2 ^ 64 + k mod 2 ^ 64) mod 2 ^ 64 = a + k.
Proof. intros Ha Hk H. rewrite (Z.mod_small a); [|lia]. rewrite !Z.mod_small; lia. Qed.

(** A resumed call starts at this block. *)
Definition getopt_blk30 : block := Eval vm_compute in
  match find_block (TAtom "L30") (fn_blocks glibc_getopt_internal_r) with
  | Some b => b | None => mkBlock (TAtom "L30") [] [] JUnreachable end.
(** Both colon outcomes join at this block, which loads the cursor. *)
Definition getopt_blk68 : block := Eval vm_compute in
  match find_block (TAtom "L68") (fn_blocks glibc_getopt_internal_r) with
  | Some b => b | None => mkBlock (TAtom "L68") [] [] JUnreachable end.


(** Initialization supplies the private-field and byte modules. *)
Import GetoptInitialize GetoptState FileInv FileInv.ML FileInv.LG FileInv.L LibioLogic GetoptBytes.

(** After the colon check, the scanner also reads the skipped option string. *)
Definition colon_keys : list name := TAtom "pr.1" :: entry_keys.

(** The colon and cursor checks add the diagnostic flag, the checked
    option-string pointer, the checked cursor cell and a null constant. *)
Definition colon_env (e e' : env) (p : ptr) (os : list Z) (err b : Z) : Prop :=
  keeps colon_keys e e' /\ lookup (TAtom "pr.3") e' = Some (WInt (print_errors os err)) /\
  lookup (TAtom "chk19") e' = Some (WPtr (ptr_add p (Z.of_nat (opt_skip os)))) /\
  lookup (TAtom "chk20") e' = Some (WPtr (mkPtr (b + 32) (Obj b))) /\
  lookup (TAtom "v80") e' = Some (WInt 0).


Import ProgramAbbreviations.
Section colon.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance colon_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** This tactic checks and loads byte k of the shared string H at q as a signed byte. *)
Ltac rdchr H q s k :=
  let bb := fresh "bb" in let breg := fresh "breg" in let Hbb := fresh "Hbb" in
  iDestruct (ws_byte q s k with H) as (bb breg) "(%Hbb & #Hbl & #Hbt)"; [lia|];
  destruct Hbb as (Hcap & Hb0' & Hbq & Hbe & Hbr);
  iApply (wp_check_read_dq registry (os_wi w0) ge with "Hbl");
    [reflexivity | vx | exact Hcap | arith | arith | arith |]; iNext; iIntros "_";
  iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
    [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | arith |];
  iNext; iIntros "_ _".

(** Each kept lookup of a known value becomes a fact about the new
    environment. The tactic leaves the original hypothesis in place. *)
Ltac unkeep Hk :=
  let Hc := fresh "Hkc" in pose proof Hk as Hc;
  unfold keeps, colon_keys, entry_keys in Hc; cbn [List.map] in Hc;
  repeat match type of Hc with Forall _ (_ :: _) => let H := fresh "Hkk" in apply Forall_cons_1 in Hc as [H Hc] end;
  repeat match goal with H : lookup ?k ?e1 = lookup ?k ?e, H' : lookup ?k ?e = Some _ |- _ => rewrite H' in H end.

(** A run of assignments to other names keeps the listed lookups. *)
Ltac keep := repeat (apply keeps_put; [vm_compute; reflexivity |]); first [apply keeps_refl | assumption].

(** A resumed call skips the same ordering prefix as initialization,
    reading the option string through the caller's shared view. *)
Lemma wp_getopt_resume e p os Φ :
  lookup (TAtom "v4") e = Some (WPtr p) ->
  word_string DfracDiscarded p os -∗
  (∀ e', ⌜keeps entry_keys e e'⌝ -∗
     WP (ERun (mkFrame glibc_getopt_internal_r (put (TAtom "pr.1") (WPtr (ptr_add p (Z.of_nat (opt_skip os)))) e')
                 [] None (Exec (TAtom "L31") (b_insts getopt_blk31) (b_jump getopt_blk31))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "L30") (b_insts getopt_blk30) (b_jump getopt_blk30))) : gexpr) {{ Φ }}.
Proof.
  intros Hv4. iIntros "#Hos HK". cbn [b_insts b_jump getopt_blk30].
  iDestruct (ws_shape with "Hos") as %(Hch & Hp0 & Hpe).
  rdchr "Hos" p os 0%nat. pose proof (sbyte_range os 0 Hch) as Hc0r.
  step. iApply wp_branch; [vx | iNext]. rewrite chr_cmp; [|lia|lia].
  destruct (Z.eqb_spec (sbyte os 0) 45) as [E45|E45]; cbn [edge_label].
  { rewrite (opt_skip_minus os E45). step. branch. step. step. step. step.
    rewrite (addr_add (ptr_addr p) 1); [|lia|lia|lia]. iApply ("HK" with "[%]"). keep. }
  step. load_bytes_dq "Hbl Hbt" decode (apply extended_chr) by arith. iNext. iIntros "_ _".
  step. step. step. rewrite chr_cmp; [|lia|lia].
  destruct (Z.eqb_spec (sbyte os 0) 43) as [E43|E43].
  { rewrite (opt_skip_plus os E43). branch. step. step. step. step.
    rewrite (addr_add (ptr_addr p) 1); [|lia|lia|lia]. iApply ("HK" with "[%]"). keep. }
  rewrite (opt_skip_other os E45 E43). branch. step.
  assert (Ep : ptr_add p (Z.of_nat 0) = p) by (destruct p; unfold ptr_add; cbn; f_equal; lia).
  iEval (rewrite Ep) in "HK". iApply ("HK" with "[%]"). keep.
Qed.

(** This tactic decides a branch whose condition has become closed. *)
Ltac close_br :=
  lazymatch goal with |- context [edge_label (if ?c then _ else _)] =>
    let c' := eval vm_compute in c in change c with c' end; cbn [edge_label].

(** The colon check reads the option character after the ordering
    prefix and records whether diagnostics are printed. The cursor check
    then loads the saved cursor. A null cursor or an empty suffix sends
    the call to argument selection at L73, and a nonempty suffix sends it
    to option reading at L75. The caller passes the cursor's suffix,
    which the cursor's shared view determines when it is not null. *)
Lemma wp_getopt_colon e p os b r cur tail err Φ :
  lookup (TAtom "pr.1") e = Some (WPtr (ptr_add p (Z.of_nat (opt_skip os)))) ->
  lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "v19") e = Some (WInt err) -> 0 <= err < 2 ^ 32 ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  live b r -∗ pcell b 32 cur -∗ word_string DfracDiscarded p os -∗
  (⌜cur = null⌝ ∨ word_string DfracDiscarded cur tail) -∗
  ((∀ e', ⌜colon_env e e' p os err b /\ (cur = null \/ tail = [])⌝ -∗ live b r -∗ pcell b 32 cur -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L73") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }}) ∧
   (∀ e', ⌜colon_env e e' p os err b /\ cur <> null /\ tail <> []⌝ -∗ live b r -∗ pcell b 32 cur -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e' [] None (Enter (TAtom "L75") (Some (TAtom "L83")))) : gexpr)
        {{ Φ }})) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "L31") (b_insts getopt_blk31) (b_jump getopt_blk31))) : gexpr) {{ Φ }}.
Proof.
  intros Hp1 Hv12 Hc0 Hv19 Herr Hb Ha He Hr. iIntros "Hl Hnext #Hos #Hcur HK".
  cbn [b_insts b_jump getopt_blk31].
  pose proof (opt_skip_le os) as Hsk.
  iDestruct (ws_suffix p os (opt_skip os) Hsk with "Hos") as "#Hsuf".
  iAssert (∀ e2 fr, ⌜keeps colon_keys e e2 /\
      lookup (TAtom "chk19") e2 = Some (WPtr (ptr_add p (Z.of_nat (opt_skip os)))) /\
      phis_env ge (b_phis getopt_blk68) (Some fr) e2 = Some (put (TAtom "pr.3") (WInt (print_errors os err)) e2)⌝ -∗
    live b r -∗ pcell b 32 cur -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "L68") (Some fr))) : gexpr) {{ Φ }})%I
    with "[HK]" as "HL68".
  { iIntros (e2 fr (Hk & H19 & Hphi)) "Hl Hnext". unkeep Hk.
    iApply wp_enter; [reflexivity | exact Hphi | iNext]. cbn [b_insts b_jump getopt_blk68].
    step. check "Hl". iDestruct "Hcur" as "[%Hn | #Hw]".
    - subst cur. iApply (wp_raw_load_pointer_dq with "Hl Hnext []");
        [reflexivity | vx | left; reflexivity | arith | arith | cbn; lia | done |].
      iNext. iIntros "Hl Hnext _". step. step. step. branch. step. branch. iDestruct "HK" as "[HK _]".
      iApply ("HK" with "[%] Hl Hnext"). split; [|left; reflexivity].
      split; [keep|]. rewrite (addr_add b 32); [repeat split; vx | lia | lia | lia].
    - iDestruct (ws_shape with "Hw") as %(Hcht & Hcp0 & Hcpe).
      iDestruct (ws_byte cur tail 0 with "Hw") as (cb creg) "(%Hcb & #Hcl & #Hct)"; [lia|].
      destruct Hcb as (Hccap & Hcb0 & Hcbq & Hcbe & Hcbr).
      iAssert (live_capq DfracDiscarded (ptr_cap cur) creg) as "Hcc".
      { by destruct Hccap as [-> | ->]. }
      load_pointer_dq "Hl Hnext Hcc" by arith.
      iNext. iIntros "Hl Hnext _". step. step. step.
      assert (Ez : (ptr_addr cur mod 2 ^ 64 =? 0 mod 2 ^ 64) = false)
        by (apply Z.eqb_neq; rewrite !Z.mod_small; lia).
      iApply wp_branch; [vx | iNext]. rewrite Ez. close_br. step. step.
      load_pointer_dq "Hl Hnext Hcc" by arith.
      iNext. iIntros "Hl Hnext _".
      check_read_dq "Hcl" by arith. iNext. iIntros "_".
      load_bytes_dq "Hcl Hct" decode (apply extended_chr) by arith.
      iNext. iIntros "_ _". pose proof (sbyte_range tail 0 Hcht) as Htr.
      step. step. step. iApply wp_branch; [vx | iNext]. rewrite chr_cmp; [|lia|lia].
      destruct (Z.eqb_spec (sbyte tail 0) 0) as [Et|Et]; close_br.
      + apply (sbyte_zero tail 0 Hcht) in Et; [|lia]. iDestruct "HK" as "[HK _]".
        iApply ("HK" with "[%] Hl Hnext"). split; [|right; by destruct tail].
        split; [keep|]. rewrite (addr_add b 32); [repeat split; vx | lia | lia | lia].
      + iDestruct "HK" as "[_ HK]". iApply ("HK" with "[%] Hl Hnext").
        split; [split; [keep|]; rewrite (addr_add b 32); [repeat split; vx | lia | lia | lia]|].
        split; [intros ->; cbn in Hcp0; lia | intros ->; apply Et; reflexivity]. }
  iDestruct (ws_shape with "Hsuf") as %(Hch & Hq0 & Hqe).
  rdchr "Hsuf" (ptr_add p (Z.of_nat (opt_skip os))) (drop (opt_skip os) os) 0%nat.
  pose proof (sbyte_range _ 0 Hch) as Hcr.
  step. iApply wp_branch; [vx | iNext]. rewrite chr_cmp; [|lia|lia].
  rewrite (sbyte_drop os (opt_skip os) 0 Hsk) Nat.add_0_r.
  destruct (Z.eqb_spec (sbyte os (opt_skip os)) 58) as [E58|E58]; close_br.
  - iApply ("HL68" with "[%] Hl Hnext"). split; [keep|]. split; [vx|].
    unfold print_errors. rewrite (proj2 (Z.eqb_eq _ _) E58). vx.
  - step. step. iApply ("HL68" with "[%] Hl Hnext"). split; [keep|]. split; [vx|].
    unfold print_errors. rewrite (proj2 (Z.eqb_neq _ _) E58). rewrite -(Z.mod_small err (2 ^ 32)); [vx | lia].
  Unshelve. exact r. exact DfracDiscarded.
Qed.

End colon.
