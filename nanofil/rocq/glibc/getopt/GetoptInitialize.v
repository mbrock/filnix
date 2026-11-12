(** Each call of glibc's reentrant option scanner first checks whether
    its private object needs initialization. It initializes when the
    object is fresh or when the caller reset the public index to zero.
    This file proves the inlined [_getopt_initialize] blocks of the
    captured [_getopt_internal_r] on the object's real private cells,
    for any argument count of at least one.

    Initialization sets the index, both nonoption endpoints, the saved
    cursor, the ordering mode and the initialized flag. It reads the
    first character of the option string, where a minus or plus sign
    selects an ordering and is skipped. Otherwise glibc asks the
    environment whether POSIXLY_CORRECT is set. That call is an explicit
    dependency: the caller supplies a rule for glibc's getenv that
    preserves the caller's own resource. Every path then joins at the
    block that checks for a leading colon. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import OsWorld FileInv LibioLogic WordString GetoptModule GetoptState GetoptBytes.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.
Local Transparent glibc_getopt_internal_r.

(** ## What the first blocks compute

    The option string may begin with a character that selects argument
    ordering. The scanner skips that character before it looks for
    the colon that silences diagnostics. *)

(** A leading minus or plus sign selects an ordering and is skipped. *)
Definition opt_skip (os : list Z) : nat :=
  if (sbyte os 0 =? 45) || (sbyte os 0 =? 43) then 1%nat else 0%nat.

(** A leading minus sign is skipped. *)
Lemma opt_skip_minus os : sbyte os 0 = 45 -> opt_skip os = 1%nat.
Proof. unfold opt_skip. intros ->. reflexivity. Qed.

(** A leading plus sign is skipped. *)
Lemma opt_skip_plus os : sbyte os 0 = 43 -> opt_skip os = 1%nat.
Proof. unfold opt_skip. intros ->. reflexivity. Qed.

(** Any other first character remains part of the option list. *)
Lemma opt_skip_other os : sbyte os 0 <> 45 -> sbyte os 0 <> 43 -> opt_skip os = 0%nat.
Proof.
  unfold opt_skip. intros H1 H2. rewrite (proj2 (Z.eqb_neq _ _) H1) (proj2 (Z.eqb_neq _ _) H2). reflexivity.
Qed.

(** A loaded character equals a small constant exactly when the byte does. *)
Lemma chr_cmp x k : 0 <= x < 256 -> 0 <= k < 128 ->
  (if chr_w x mod 2 ^ 32 =? k mod 2 ^ 32 then 1 else 0) = (if x =? k then 1 else 0).
Proof.
  intros Hx Hk. rewrite (Z.mod_small (chr_w x)); [|apply chr_w_range].
  rewrite (Z.mod_small k); [|lia]. rewrite chr_w_eqb; lia.
Qed.

(** Every path joins at this block after the ordering prefix. *)
Definition getopt_blk31 : block := Eval vm_compute in
  match find_block (TAtom "L31") (fn_blocks glibc_getopt_internal_r) with
  | Some b => b | None => mkBlock (TAtom "L31") [] [] JUnreachable end.
(** This block marks the private object initialized. *)
Definition getopt_blk27 : block := Eval vm_compute in
  match find_block (TAtom "iw_1.L27") (fn_blocks glibc_getopt_internal_r) with
  | Some b => b | None => mkBlock (TAtom "iw_1.L27") [] [] JUnreachable end.
(** The inlined initialization starts at this block. *)
Definition getopt_blk_init : block := Eval vm_compute in
  match find_block (TAtom "iw_1.start") (fn_blocks glibc_getopt_internal_r) with
  | Some b => b | None => mkBlock (TAtom "iw_1.start") [] [] JUnreachable end.

(** Every proof below runs on the caller's [[runtime]] and logic instance. *)
Module GetoptInitializeOn (R : Runtime) (LG0 : LogicSig R).
(** The session module supplies the private-field representation. *)
Module S := GetoptStateOn R LG0.
(** Byte access supplies shared string reads. *)
Module GB := GetoptBytesOn R LG0.
(** The step tactics evaluate symbolic instructions. *)
Module ST := LibioStepOn R LG0.
(** The OS interpretation survives safepoints. *)
Module OW := OsWorldOn R LG0.
Import S S.FI S.FI.ML S.FI.LG S.FI.L ST GB.

Section initialize.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The OS interpretation survives the scanner's safepoints. *)
Local Instance init_stable : SafepointStable (os_wi w0) := OW.os_wi_stable w0.
(** The program logic uses the caller's registry and OS interpretation. *)
Local Instance init_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
(** This notation selects expressions of the linked language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Initialization calls getenv, and this file does not prove getenv.
    The caller instead supplies a rule for that call. The rule keeps the
    caller's resource G and may return any pointer. *)
Definition getenv_rule (G : iProp Σ) : Prop :=
  forall f e ls l d args rest j x Φ, map_option (arg_x ge e) args = Some [x] ->
  ⊢ G -∗ ▷ (∀ q, G -∗ WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame f e ls None
         (Exec l (Call (CResult d P) (Global (TAtom "__GI_getenv")) args :: rest) j)) : gexpr) {{ Φ }}.

(** This tactic loads an owned private integer field as a signed 32-bit value. *)
Ltac load_int H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; assumption | left; reflexivity | arith |];
  iNext; iIntros H.

(** This tactic loads a field whose value is a local definition. *)
Ltac load_int' H x :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | vx | reflexivity | apply load_sw_int; subst x; lia | left; reflexivity | arith |];
  iNext; iIntros H.

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

(** This tactic rebuilds an integer field from its rewritten bytes. *)
Ltac icell := iSplit; [iPureIntro; lia | iAssumption].

(** The environment e' keeps every lookup of e at the names ks. *)
Definition keeps (ks : list name) (e e' : env) : Prop := Forall (fun k => lookup k e' = lookup k e) ks.

(** The scanner reads these names after initialization. *)
Definition entry_keys : list name :=
  List.map TAtom ["v0"; "v2"; "v4"; "v6"; "v8"; "v10"; "v12"; "v14"; "v19"; "chk0"; "chk1"; "chk2"]%string.

(** Every environment keeps its own lookups. *)
Lemma keeps_refl ks e : keeps ks e e.
Proof. apply Forall_forall. reflexivity. Qed.

(** Assigning a name outside ks keeps every lookup at ks. *)
Lemma keeps_put ks k v e e' :
  forallb (fun k' => negb (name_eqb k' k)) ks = true -> keeps ks e e' -> keeps ks e (put k v e').
Proof.
  intros Hks Hk. apply Forall_forall. intros x Hx.
  rewrite (Symbolic.lookup_after_put_other _ x k v e'); [exact (proj1 (Forall_forall _ _) Hk x Hx)|].
  apply forallb_forall with (x := x) in Hks; [|exact Hx]. by destruct (name_eqb x k).
Qed.

(** Each kept lookup of a known value becomes a fact about the new
    environment. The tactic leaves the original hypothesis in place for
    the next join point. *)
Ltac unkeep Hk :=
  let Hc := fresh "Hkc" in pose proof Hk as Hc;
  unfold keeps, entry_keys in Hc; cbn [List.map] in Hc;
  repeat match type of Hc with Forall _ (_ :: _) => let H := fresh "Hkk" in apply Forall_cons_1 in Hc as [H Hc] end;
  repeat match goal with H : lookup ?k ?e1 = lookup ?k ?e, H' : lookup ?k ?e = Some _ |- _ => rewrite H' in H end.

(** A run of assignments to other names keeps the listed lookups. *)
Ltac keep := repeat (apply keeps_put; [vm_compute; reflexivity |]); first [apply keeps_refl | assumption].

(** Initialization writes each private field it owns: the public index,
    both nonoption endpoints, the saved cursor, the ordering mode and the
    initialized flag. When the caller has not requested an ordering, glibc
    asks the environment through the caller's getenv rule. *)
Lemma wp_getopt_initialize e n p os b r s pc penv (G : iProp Σ) Φ :
  getenv_rule G -> lookup (TAtom "glibc_getopt#str.145") (ge_globals ge) = Some penv ->
  lookup (TAtom "v4") e = Some (WPtr p) -> lookup (TAtom "v12") e = Some (WPtr (mkPtr b (Obj b))) ->
  lookup (TAtom "v14") e = Some (WInt pc) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (b + 4) (Obj b))) ->
  lookup (TAtom "chk2") e = Some (WPtr (mkPtr b (Obj b))) ->
  0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 -> 0 <= gs_ind s <= n -> 1 <= n < 2 ^ 31 ->
  live b r -∗ int_cell b 0 (gs_ind s) -∗ int_cell b 24 (gs_initialized s) -∗ pcell b 32 (gs_next s) -∗
  int_cell b 40 (gs_order s) -∗ int_cell b 44 (gs_first s) -∗ int_cell b 48 (gs_last s) -∗
  word_string DfracDiscarded p os -∗ G -∗
  (∀ e' o, ⌜keeps entry_keys e e' /\ 0 <= o <= 2⌝ -∗
     let i := if gs_ind s =? 0 then 1 else gs_ind s in
     live b r -∗ int_cell b 0 i -∗ int_cell b 24 1 -∗ pcell b 32 null -∗
     int_cell b 40 o -∗ int_cell b 44 i -∗ int_cell b 48 i -∗ G -∗
     WP (ERun (mkFrame glibc_getopt_internal_r (put (TAtom "pr.1") (WPtr (ptr_add p (Z.of_nat (opt_skip os)))) e')
                 [] None (Exec (TAtom "L31") (b_insts getopt_blk31) (b_jump getopt_blk31))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getopt_internal_r e [] None
              (Exec (TAtom "iw_1.start") (b_insts getopt_blk_init) (b_jump getopt_blk_init))) : gexpr) {{ Φ }}.
Proof.
  intros Hget Hpenv Hv4 Hv12 Hv14 Hc0 Hc2 Hb Ha He Hr Hi Hn.
  iIntros "Hl [%Hi0 Hib] [%Hini Hinib] Hnext [%Hord Hordb] [%Hf Hfb] [%Hla Hlab] #Hos HG HK".
  cbn [b_insts b_jump getopt_blk_init].
  set (i := if gs_ind s =? 0 then 1 else gs_ind s).
  assert (Hii : 1 <= i <= n) by (subst i; destruct (Z.eqb_spec (gs_ind s) 0); lia).
  iAssert (∀ e2 fr o, ⌜keeps entry_keys e e2 /\ 0 <= o <= 2 /\
      phis_env ge (b_phis getopt_blk27) (Some fr) e2 =
        Some (put (TAtom "iw_1.pr.1") (WPtr (ptr_add p (Z.of_nat (opt_skip os)))) e2)⌝ -∗
    live b r -∗ int_cell b 0 i -∗ pcell b 32 null -∗ int_cell b 40 o -∗ int_cell b 44 i -∗
    int_cell b 48 i -∗ G -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e2 [] None (Enter (TAtom "iw_1.L27") (Some fr))) : gexpr) {{ Φ }})%I
    with "[Hinib HK]" as "HL27".
  { iIntros (e2 fr o (Hk & Ho & Hphi)) "Hl Hi Hn Ho Hf Hla HG". unkeep Hk.
    iApply wp_enter; [reflexivity | exact Hphi | iNext]. cbn [b_insts b_jump getopt_blk27].
    st. norm. chk "Hl".
    iApply (wp_raw_store_w with "Hl Hinib"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hinib". st. iApply wp_enter; [reflexivity | vx | iNext].
    iApply ("HK" $! _ o with "[%] Hl Hi [Hinib] Hn Ho Hf Hla HG"); [split; [keep | exact Ho] | by iSplit]. }
  iAssert (∀ e1 from, ⌜keeps entry_keys e e1⌝ -∗ live b r -∗ bytes b 0 (int_bytes i) -∗
    WP (ERun (mkFrame glibc_getopt_internal_r e1 [] None (Enter (TAtom "iw_1.L12") (Some from))) : gexpr) {{ Φ }})%I
    with "[Hnext Hordb Hfb Hlab HG HL27]" as "HL12".
  { iIntros (e1 from Hk) "Hl Hib". unkeep Hk.
    iDestruct (ws_shape with "Hos") as %(Hch & Hp0 & Hpe).
    st. st. st. load_int' "Hl Hib" i. chk "Hl".
    iApply (wp_raw_store_w with "Hl Hlab"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hlab".
    iApply (wp_raw_store_w with "Hl Hfb"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hfb". st. chk "Hl".
    iApply (wp_raw_store_pointer with "Hl Hnext"); [vx | vx | reflexivity | arith | arith | wi_store |].
    iNext. iIntros "Hl Hnext". norm.
    rdchr "Hos" p os 0%nat. pose proof (sbyte_range os 0 Hch) as Hc0r.
    st. iApply wp_branch; [vx | iNext]. rewrite chr_cmp; [|lia|lia].
    destruct (Z.eqb_spec (sbyte os 0) 45) as [E45|E45]; cbn [edge_label].
    { rewrite (opt_skip_minus os E45). st. st. norm. chk "Hl".
      iApply (wp_raw_store_w with "Hl Hordb"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
      iNext. iIntros "Hl Hordb". st. norm. st.
      iApply ("HL27" $! _ _ 2 with "[%] Hl [Hib] Hnext [Hordb] [Hfb] [Hlab] HG");
        [split; [keep|]; split; [lia|]; unfold ptr_add; vx | icell | icell | icell | icell]. }
    st. norm. iApply (wp_raw_load_sub_bytes_dq with "Hbl Hbt");
      [reflexivity | vx | reflexivity | apply extended_chr | exact Hcap | arith |]. iNext. iIntros "_ _".
    st. iApply wp_branch; [vx | iNext]. rewrite chr_cmp; [|lia|lia].
    destruct (Z.eqb_spec (sbyte os 0) 43) as [E43|E43]; cbn [edge_label].
    { rewrite (opt_skip_plus os E43). st. st. norm. chk "Hl".
      iApply (wp_raw_store_w with "Hl Hordb"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
      iNext. iIntros "Hl Hordb". st. norm. st.
      iApply ("HL27" $! _ _ 0 with "[%] Hl [Hib] Hnext [Hordb] [Hfb] [Hlab] HG");
        [split; [keep|]; split; [lia|]; unfold ptr_add; vx | icell | icell | icell | icell]. }
    rewrite (opt_skip_other os E45 E43). cbn [Z.of_nat]. unfold ptr_add. rewrite Z.add_0_r.
    iAssert (∀ o (e3 : env) fr, ⌜keeps entry_keys e e3 /\ lookup (TAtom "v4") e3 = Some (WPtr p) /\ 0 <= o <= 1⌝ -∗
      int_cell b 40 (gs_order s) -∗ live b r -∗ G -∗
      WP (ERun (mkFrame glibc_getopt_internal_r e3 [] None
          (Enter (TAtom (if o =? 0 then "iw_1.L47" else "iw_1.L48")) (Some fr))) : gexpr) {{ Φ }})%I
      with "[Hib Hnext Hfb Hlab HL27]" as "HL47".
    { iIntros (o e3 fr (Hk3 & Hv43 & Ho)) "[_ Hordb] Hl HG". unkeep Hk3.
      assert (Ho' : 0 <= o < 2 ^ 32) by lia.
      assert (o = 0 \/ o = 1) as [-> | ->] by lia; st; st; norm; chk "Hl";
        (iApply (wp_raw_store_w with "Hl Hordb"); [vx | vx | reflexivity | arith | reflexivity | wi_store |]);
        iNext; iIntros "Hl Hordb"; st;
        [iApply ("HL27" $! _ _ 0 with "[%] Hl [Hib] Hnext [Hordb] [Hfb] [Hlab] HG")
        |iApply ("HL27" $! _ _ 1 with "[%] Hl [Hib] Hnext [Hordb] [Hfb] [Hlab] HG")]; try icell;
        (split; [keep|]); (split; [lia|]); destruct p; vx. }
    st. iApply wp_branch; [vx | iNext].
    destruct (Z.eqb_spec (pc mod 2 ^ 32) 0) as [Epc|Epc]; cbn [edge_label].
    - st. st. iApply (Hget with "HG"); [vx|]. iNext. iIntros (q) "HG". st. st. st.
      iApply wp_enter; [reflexivity | vx | iNext]. cbn [b_insts b_jump]. iApply wp_branch; [vx | iNext].
      destruct (ptr_addr q mod 2 ^ 64 =? 0 mod 2 ^ 64); cbn [negb];
        [change ((0 mod 2 ^ 32) mod 2 ^ 32 =? 0) with true | change ((1 mod 2 ^ 32) mod 2 ^ 32 =? 0) with false];
        cbn [edge_label].
      + iApply ("HL47" $! 1 with "[%] [Hordb] Hl HG"); [split; [keep|]; split; [vx | lia] | icell].
      + iApply ("HL47" $! 0 with "[%] [Hordb] Hl HG"); [split; [keep|]; split; [vx | lia] | icell].
    - st. iApply wp_branch; [vx | iNext]. cbn [edge_label].
      iApply ("HL47" $! 0 with "[%] [Hordb] Hl HG"); [split; [keep|]; split; [vx | lia] | icell]. }
  load_int "Hl Hib". st. iApply wp_branch; [vx | iNext]. norm.
  destruct (Z.eqb_spec (gs_ind s) 0) as [H0|H0].
  - assert (Ei : i = 1) by (unfold i; reflexivity). rewrite Ei.
    cbn [edge_label]. st. chk "Hl".
    iApply (wp_raw_store_w with "Hl Hib"); [vx | vx | reflexivity | arith | reflexivity | wi_store |].
    iNext. iIntros "Hl Hib". st. iApply ("HL12" with "[%] Hl Hib"). keep.
  - assert (Ei : i = gs_ind s) by (unfold i; reflexivity).
    rewrite Ei. cbn [edge_label].
    iApply ("HL12" with "[%] Hl Hib"). keep.
Qed.

End initialize.
End GetoptInitializeOn.
