(** Glibc compares one environment entry with the requested name before
    advancing the array cursor. A successful bounded comparison supplies
    the bounds for reading the following equals sign. The remaining array
    scan is a continuation, not an assumed proof of getenv. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run
  Machine Pieces Heap Language Logic ExternalCalls StepRules Symbolic.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics WordString
  GetoptBytes GetenvCode GetenvName StrncmpCode StrncmpLogic StrncmpBits StrcmpBits.
Import ListNotations LG0 LG0.L ProgramAbbreviations GetoptBytes GetoptBytes.ML.
Open Scope Z_scope.

(** Comparing the full name successfully means that it is an entry prefix.
    In particular, the entry's byte at the name length is readable, including
    when that byte is the entry's NUL terminator. *)
Lemma getenv_prefix s t :
  Forall (fun c => 0 < c < 256) s -> Forall (fun c => 0 < c < 256) t ->
  strncmp_res (Z.of_nat (length s)) s t = 0 <-> take (length s) t = s.
Proof.
  intros Hs Ht. unfold strncmp_res. rewrite Nat2Z.id take_ge; [|lia].
  rewrite strcmp_res_zero; [split; congruence | exact Hs | apply Forall_take; exact Ht].
Qed.

(** A prefix cannot be longer than the entry it prefixes. *)
Lemma getenv_prefix_bound (s t : list Z) : take (length s) t = s -> (length s <= length t)%nat.
Proof. intros H. apply (f_equal (@length Z)) in H. rewrite length_take in H. lia. Qed.

(** Signed first-byte loads preserve equality even for bytes above 127. *)
Lemma getenv_chr_eq x y : 0 <= x < 256 -> 0 <= y < 256 ->
  (chr_w x =? chr_w y) = (x =? y).
Proof.
  intros Hx Hy. destruct (Z.eqb_spec x y) as [->|Hne].
  - apply Z.eqb_refl.
  - apply Z.eqb_neq. intros E.
    destruct (Z.lt_ge_cases x 128) as [Hxlo|Hxhi];
      destruct (Z.lt_ge_cases y 128) as [Hylo|Hyhi].
    + rewrite (chr_w_small x ltac:(lia)) (chr_w_small y ltac:(lia)) in E. lia.
    + rewrite (chr_w_small x ltac:(lia)) (chr_w_large y ltac:(lia)) in E. lia.
    + rewrite (chr_w_large x ltac:(lia)) (chr_w_small y ltac:(lia)) in E. lia.
    + rewrite (chr_w_large x ltac:(lia)) (chr_w_large y ltac:(lia)) in E. lia.
Qed.

(** The next iteration needs the original name, its length, and the saved
    counter sample. These bindings retain them alongside the current cursor.
    The next-slot rule also supplies the advanced cursor in v81. *)
Definition getenv_scan_bindings e p ep n old :=
  lookup (TAtom "v0") e = Some (WPtr p) /\
  lookup (TAtom "pr.1") e = Some (WPtr ep) /\
  lookup (TAtom "v29") e = Some (WInt n) /\
  lookup (TAtom "v7") e = Some (WInt old) /\
  lookup (TAtom "v16") e = Some (WInt 0).

Section comparison.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Instance getenv_compare_stable : SafepointStable (os_wi w0) := OsWorld.os_wi_stable w0.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** A mismatch advances by one pointer slot and reaches the poll edge.
    It does not read that next slot or assume that it exists. *)
Lemma getenv_advance e p ep n old (G : iProp Σ) Φ :
  getenv_scan_bindings e p ep n old ->
  0 <= ptr_addr ep < 2 ^ 48 ->
  G -∗
  (∀ e', ⌜getenv_scan_bindings e' p ep n old /\
           lookup (TAtom "v81") e' = Some (WPtr (ptr_add ep 8))⌝ -∗ G -∗
    WP (ERun (mkFrame glibc_getenv e' [] None
      (Enter (TAtom "L32") (Some (TAtom "L34")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getenv e [] None
    (Enter (TAtom "L34") (Some (TAtom "L67")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros (Hp & Hep & Hn & Hold & Hz) Hepbound. iIntros "HG HK".
  step. step. step. iApply ("HK" with "[] HG"). iPureIntro.
  unfold getenv_scan_bindings, ptr_add. repeat split; try vx.
  cbn [put lookup]. rewrite (Z.mod_small (ptr_addr ep) (2 ^ 64)); [|lia].
  change (8 mod 2 ^ 64) with 8. rewrite Z.mod_small; [reflexivity |lia].
Qed.

(** After a successful comparison, the delimiter read is within the entry.
    A match returns the pointer immediately after the equals sign, including
    when it points to the empty value's terminator. *)
Lemma getenv_equals e p ep q s t old (G : iProp Σ) Φ :
  getenv_scan_bindings e p ep (Z.of_nat (length s)) old ->
  0 <= ptr_addr ep < 2 ^ 48 ->
  lookup (TAtom "v38") e = Some (WPtr q) ->
  take (length s) t = s ->
  word_string DfracDiscarded q t -∗ G -∗
  (if sbyte t (length s) =? 61 then
     G -∗ Φ (Ret (WPtr (ptr_add q (Z.of_nat (length s) + 1))))
   else ∀ e', ⌜getenv_scan_bindings e' p ep (Z.of_nat (length s)) old /\
           lookup (TAtom "v81") e' = Some (WPtr (ptr_add ep 8))⌝ -∗ G -∗
     WP (ERun (mkFrame glibc_getenv e' [] None
       (Enter (TAtom "L32") (Some (TAtom "L34")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getenv e [] None
    (Enter (TAtom "L66") (Some (TAtom "L58")))) : gexpr) {{ Φ }}.
Proof using Type.
  intros (Hp & Hep & Hn & Hold & Hz) Hepbound Hq Hprefix. iIntros "#Ht HG HK".
  pose proof (getenv_prefix_bound _ _ Hprefix) as Hlen.
  iDestruct (ws_shape with "Ht") as %(Hchars & Hpos & Hfit).
  iDestruct (ws_byte q t (length s) Hlen with "Ht") as (b reg) "(%Hb & #Hl & #Hb)".
  destruct Hb as (Hcap & Hbpos & Hbase & Hend & Hspace).
  step. step.
  rewrite (Z.mod_small (ptr_addr q) (2 ^ 64)); [|lia].
  rewrite (Z.mod_small (Z.of_nat (length s)) (2 ^ 64)); [|lia].
  rewrite (Z.mod_small (ptr_addr q + Z.of_nat (length s)) (2 ^ 64)); [|lia].
  check_read_dq "Hl" by (unfold raw_address; cbn; rewrite Z.add_0_r;
    rewrite Z.mod_small; lia).
  iNext. iIntros "_".
  load_bytes_dq "Hl Hb" decode (apply extended_chr) by
    (unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia).
  iNext. iIntros "_ _". step. step. step.
  rewrite (Z.mod_small (chr_w _) (2 ^ 32)); [|apply chr_w_range].
  change (61 mod 2 ^ 32) with 61.
  rewrite chr_w_eqb; [|apply sbyte_range; exact Hchars |lia].
  destruct (sbyte t (length s) =? 61) eqn:Heq; branch.
  - step. step. step. iApply wp_ret; [reflexivity | vx |]. iNext.
    unfold ptr_add. cbn.
    rewrite (Z.mod_small (ptr_addr q) (2 ^ 64)); [|lia].
    rewrite (Z.mod_small (Z.of_nat (length s)) (2 ^ 64)); [|lia].
    rewrite (Z.mod_small (ptr_addr q + Z.of_nat (length s)) (2 ^ 64)); [|lia].
    repeat rewrite (Z.mod_small (ptr_addr q + Z.of_nat (length s)) (2 ^ 64) ltac:(lia)).
    rewrite (Z.mod_small (ptr_addr q + Z.of_nat (length s) + 1) (2 ^ 64)); [|lia].
    replace (ptr_addr q + Z.of_nat (length s) + 1)
      with (ptr_addr q + (Z.of_nat (length s) + 1)) by lia.
    iApply ("HK" with "HG").
  - iApply (getenv_advance with "HG HK").
    + unfold getenv_scan_bindings. repeat split; vx.
    + exact Hepbound.
Qed.

(** These three tests are the actual short-circuit comparison: signed first
    characters, the bounded comparison result, and the following delimiter. *)
Definition getenv_entry_matches s t :=
  (sbyte s 0 =? sbyte t 0) &&
  (strncmp_res (Z.of_nat (length s)) s t =? 0) &&
  (sbyte t (length s) =? 61).

(** Comparing an entry does not consume the caller's memory permissions.
    The arbitrary frame G can retain both globals, the array lifetime, the
    current pointer cell, and the loaded target lifetime. Both strings remain
    readable; the rule makes no assumption about reading subsequent entries. *)
Lemma getenv_compare_entry e p ep q s t old (G : iProp Σ) Φ
    `{!Defines ge "__GI_strncmp" glibc_strncmp} :
  getenv_scan_bindings e p ep (Z.of_nat (length s)) old ->
  0 <= ptr_addr ep < 2 ^ 48 ->
  lookup (TAtom "v38") e = Some (WPtr q) -> s <> [] ->
  word_string DfracDiscarded p s -∗ word_string DfracDiscarded q t -∗ G -∗
  (if getenv_entry_matches s t then
     G -∗ Φ (Ret (WPtr (ptr_add q (Z.of_nat (length s) + 1))))
   else ∀ e', ⌜getenv_scan_bindings e' p ep (Z.of_nat (length s)) old /\
           lookup (TAtom "v81") e' = Some (WPtr (ptr_add ep 8))⌝ -∗ G -∗
     WP (ERun (mkFrame glibc_getenv e' [] None
       (Enter (TAtom "L32") (Some (TAtom "L34")))) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc_getenv e [] None
    (Enter (TAtom "L41") (Some (TAtom "L32")))) : gexpr) {{ Φ }}.
Proof.
  intros (Hp & Hep & Hn & Hold & Hz) Hepbound Hq Hnonempty.
  iIntros "#Hs #Ht HG HK".
  iDestruct (ws_shape with "Hs") as %(Hsc & Hsp & Hsf).
  iDestruct (ws_shape with "Ht") as %(Htc & Htp & Htf).
  iDestruct (ws_byte p s 0 with "Hs") as (bs rs) "(%Hsb & #Hsl & #Hsb)"; [lia|].
  destruct Hsb as (Hscap & Hbs & Hsbeg & Hsend & Hsspace).
  iDestruct (ws_byte q t 0 with "Ht") as (bt rt) "(%Htb & #Htl & #Htb)"; [lia|].
  destruct Htb as (Htcap & Hbt & Htbeg & Htend & Htspace).
  step.
  check_read_dq "Hsl" by (unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia).
  iNext. iIntros "_".
  load_bytes_dq "Hsl Hsb" decode (apply extended_chr) by
    (unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia).
  iNext. iIntros "_ _".
  check_read_dq "Htl" by (unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia).
  iNext. iIntros "_".
  load_bytes_dq "Htl Htb" decode (apply extended_chr) by
    (unfold raw_address; cbn; rewrite Z.add_0_r Z.mod_small; lia).
  iNext. iIntros "_ _". step.
  rewrite !(Z.mod_small (chr_w _) (2 ^ 32) (chr_w_range _)).
  rewrite getenv_chr_eq; [|apply sbyte_range; exact Hsc |apply sbyte_range; exact Htc].
  unfold getenv_entry_matches.
  destruct (sbyte s 0 =? sbyte t 0) eqn:Hfirst; cbn [andb]; branch.
  - step.
    iApply (StrncmpLogic.wp_call_glibc_strncmp registry (os_wi w0) ge with "Hs Ht");
      [ | vx | apply defines | reflexivity |].
    { apply Z.mod_pos_bound. lia. }
    iNext. iIntros "_ _". cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
    rewrite (Z.mod_small (Z.of_nat (length s)) (2 ^ 64)); [|lia].
    step. step. step. rewrite Z.mod_mod; [|lia]. change (0 mod 2 ^ 32) with 0.
    assert (Hresmod : strncmp_res (Z.of_nat (length s)) s t mod 2 ^ 32 =
                     strncmp_res (Z.of_nat (length s)) s t).
    { unfold strncmp_res. generalize (take (Z.to_nat (Z.of_nat (length s))) s)
        (take (Z.to_nat (Z.of_nat (length s))) t).
      intros a. induction a as [|x a IH]; intros [|y b]; cbn [strcmp_res];
        try reflexivity; try apply Z.mod_mod; try lia.
      destruct (x =? y); [apply IH |apply Z.mod_mod; lia]. }
    rewrite Hresmod.
    destruct (strncmp_res (Z.of_nat (length s)) s t =? 0) eqn:Hcmp; cbn [andb]; branch.
    + iApply (getenv_equals with "Ht HG HK").
      * unfold getenv_scan_bindings. repeat split; vx.
      * exact Hepbound.
      * vx.
      * apply (proj1 (getenv_prefix s t Hsc Htc)). apply Z.eqb_eq; exact Hcmp.
    + step. branch. iApply (getenv_advance with "HG HK").
      * unfold getenv_scan_bindings. repeat split; vx.
      * exact Hepbound.
  - step. branch. step. branch. iApply (getenv_advance with "HG HK").
    + unfold getenv_scan_bindings. repeat split; vx.
    + exact Hepbound.
Qed.
End comparison.

(** The machine tests recognize exactly NAME=value, not a shorter entry,
    a bare NAME, or a longer variable name sharing the same prefix. The
    value list may be empty. *)
Lemma getenv_entry_matches_iff s t :
  Forall (fun c => 0 < c < 256) s -> Forall (fun c => 0 < c < 256) t -> s <> [] ->
  getenv_entry_matches s t = true <-> exists value, t = s ++ 61 :: value.
Proof.
  intros Hs Ht Hne. unfold getenv_entry_matches.
  rewrite !Bool.andb_true_iff !Z.eqb_eq. split.
  - intros [[Hfirst Hcmp] Hdelim].
    apply (proj1 (getenv_prefix s t Hs Ht)) in Hcmp.
    pose proof (take_drop (length s) t) as Hsplit. rewrite Hcmp in Hsplit.
    rewrite <- Hsplit in Hdelim. unfold sbyte in Hdelim.
    rewrite <- app_assoc, app_nth2 in Hdelim; [|lia].
    rewrite Nat.sub_diag in Hdelim.
    destruct (drop (length s) t) as [|x value]; cbn in Hdelim; [discriminate|].
    subst x. exists value. symmetry. exact Hsplit.
  - intros [value ->].
    assert (Hprefix : take (length s) (s ++ 61 :: value) = s).
    { clear Hs Ht Hne. induction s; cbn; congruence. }
    split.
    + split.
      * destruct s; [contradiction|]. reflexivity.
      * apply (proj2 (getenv_prefix s (s ++ 61 :: value) Hs Ht)). exact Hprefix.
    + unfold sbyte. rewrite <- app_assoc, app_nth2; [|lia].
      rewrite Nat.sub_diag. reflexivity.
Qed.
