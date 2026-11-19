(** When a wide character has no ASCII byte, glibc's
    `c: __gconv_transliterate` searches the C locale's table of source
    strings for one that starts the remaining input. Each probe of that
    binary search compares one source string with the input, one wide
    character at a time. This file proves that the comparison reads
    only words inside the source table and inside the input.

    The comparison stops at the first difference, at the zero word that
    ends the source string, or at the end of the input. Its proof keeps
    the count of equal characters below the string's length and inside
    the input, so every read lands in bounds. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude CtypeTranslitTables
  OsWorld FileInv LibioLogic LibioDefaultXsputnBuf CBlocks Fix LibioWConvAscii.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## Reading the tables

    The search reads single words of the tables and of the input, so
    its proof needs one word of a list of words at a time. These lemmas
    find that word by its position. *)

Section words.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The word at position j of a list of words occupies the four bytes
    at offset 4 j, and giving those bytes back restores the list. *)
Lemma word_at dq b o ws j x : 0 <= j -> ws !! Z.to_nat j = Some x ->
  bytesq dq b o (le_words ws) ⊢ bytesq dq b (o + 4 * j) (le_bytes x 4) ∗
    (bytesq dq b (o + 4 * j) (le_bytes x 4) -∗ bytesq dq b o (le_words ws)).
Proof using Type.
  intros Hj Hx. replace (o + 4 * j) with (o + 4 * Z.of_nat (Z.to_nat j)) by lia. by apply wchar_at.
Qed.

End words.

(** A word of a list of 32-bit words is a 32-bit word. *)
Lemma word_bound ws j x : Forall (fun c => 0 <= c < 2 ^ 32) ws -> ws !! j = Some x -> 0 <= x < 2 ^ 32.
Proof using Type. intros H Hx. exact (Forall_lookup_1 _ _ _ _ H Hx). Qed.

(** The code widens a count with a signed extension, which keeps a
    count below 2^31. *)
Lemma sext_count m h u : 0 <= u < h -> h <= m -> sign_extension m h u = u.
Proof using Type. intros Hu Hm. unfold sign_extension. cbv zeta. rewrite (Z.mod_small u m); [|lia]. destruct (Z.leb_spec h u); lia. Qed.

(** ## The comparison loop

    The loop at block `c: L135` compares the source string that starts
    at word idx of the source table with the input that starts at
    character k. The proof takes the loop itself as an induction
    hypothesis, guarded by the [[later-modality]], and counts the
    characters that matched so far. *)

(** These are the temporaries that the comparison loop assigns. *)
Definition cmp_names : list name := Eval vm_compute in
  TAtom "pr.6" :: flat_map (fun b => app (map (fun p => match p with Phi d _ _ => d end) (b_phis b)) (flat_map inst_defs (b_insts b)))
    (filter (fun b => match b_label b with TAtom s => existsb (String.eqb s) ["L135"; "L140"; "L168"; "L169"]%string | _ => false end)
      (fn_blocks glibc_translit)).

(** The tactic [wnorm] simplifies the index arithmetic of a word
    read: the code widens a count, shifts it by two and adds it to a
    pointer, and each step wraps modulo a power of two. *)
Ltac wnorm := unwrap2;
  repeat (replace (2 ^ ((2 mod 2 ^ 32) mod 64)) with 4 by reflexivity);
  repeat (replace (2 ^ (2 mod 64)) with 4 by reflexivity);
  repeat match goal with |- context [sign_extension (2 ^ 32) (2 ^ 31) ?u] =>
    rewrite (sext_count (2 ^ 32) (2 ^ 31) u); [|lia..] end; unwrap2.

(** The tactic [a4] proves an address condition of a word read. *)
Ltac a4 := autounfold with offs; cbn [ptr_addr ptr_cap r_base r_end]; unfold raw_address; wnorm; a2.

(** The tactic [branch_w] follows a jump whose condition compares such addresses. *)
Ltac branch_w b :=
  iStartProof; eapply step_wand; [eapply wp_branch; inst; vx |];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    let E := fresh "E" in assert (E : (n =? 0) = b) by (wnorm;
      repeat match goal with |- context [?x <? ?y] => destruct (Z.ltb_spec x y) end;
      cbn; first [reflexivity | exfalso; lia]);
    rewrite E; clear E end; cbn [edge_label].

Section cmp.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** One probe compares a source string with the input and must not
    read past either of them. The source string starts at word idx of
    the table fw and ends with the zero word at idx + len. The input
    holds the characters ws, and the probe starts at character k. The
    loop ends with a count c' of equal characters that fits inside both
    strings. *)
Lemma translit_cmp ls dqf fb freg fw idx len dqi di ib ireg io ic ws k Φ :
  let n := Z.of_nat (length ws) in
  0 < fb -> fb + 4 * Z.of_nat (length fw) <= r_end freg -> r_end freg <= 2 ^ 63 -> Z.of_nat (length fw) < 2 ^ 30 ->
  Forall (fun x => 0 <= x < 2 ^ 32) fw -> 0 <= idx -> 0 < len -> fw !! Z.to_nat (idx + len) = Some 0 ->
  ic = Obj ib \/ ic = Ro ib -> 0 < ib -> 0 <= io -> ib + io + 4 * n <= r_end ireg -> r_end ireg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 2 ^ 32) ws -> 0 <= k ->
  ⊢ ∀ c e, ⌜0 <= c < len /\ k + c < n /\
      lookup (TAtom "v134") e = Some (WInt idx) /\ lookup (TAtom "v75") e = Some (WPtr (mkPtr fb (Ro fb))) /\
      lookup (TAtom "v24") e = Some (WPtr (mkPtr (ib + io + 4 * k) ic)) /\
      lookup (TAtom "v103") e = Some (WInt (ib + io + 4 * n)) /\ lookup (TAtom "pr.5") e = Some (WInt c)⌝ -∗
    liveq dqf fb freg -∗ bytesq dqf fb 0 (le_words fw) -∗ liveq di ib ireg -∗ bytesq dqi ib io (le_words ws) -∗
    (∀ c' e', ⌜0 <= c' <= len /\ k + c' <= n /\ lookup (TAtom "pr.6") e' = Some (WInt c') /\ same_out cmp_names e e'⌝ -∗
      liveq dqf fb freg -∗ bytesq dqf fb 0 (le_words fw) -∗ liveq di ib ireg -∗ bytesq dqi ib io (le_words ws) -∗
      WP (ERun (mkFrame glibc_translit e' ls None (body_at glibc_translit "L137")) : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame glibc_translit e ls None (body_at glibc_translit "L135")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros n Hfb Hfe Hfr Hfs Hfw Hidx Hlen Hz Hic Hib Hio Hie Hir Hws Hk.
  iLöb as "IH". iIntros (c e (Hc & Hkc & Hv134 & Hv75 & Hv24 & Hv103 & Hpr5)) "Hfl Hft Hil Hin HK".
  assert (Hlc : forall dq, live_capq dq ic ireg = liveq dq ib ireg) by (intros; destruct Hic as [-> | ->]; reflexivity).
  assert (Hzl : idx + len < Z.of_nat (length fw)) by (pose proof (lookup_lt_Some _ _ _ Hz); lia).
  body_start glibc_translit "L135". do 4 step.
  destruct (lookup_lt_is_Some_2 fw (Z.to_nat (idx + c)) ltac:(lia)) as [x Hx]. pose proof (word_bound _ _ _ Hfw Hx) as Hx32.
  check_read_dq "Hfl" by a4. iNext. iIntros "Hfl".
  iDestruct (word_at _ _ 0 _ (idx + c) x with "Hft") as "[Hx Hft]"; [lia | exact Hx |].
  load_bytes_dq "Hfl Hx" decode (apply load_uw_char; lia) by a4. iNext. iIntros "Hfl Hx". iDestruct ("Hft" with "Hx") as "Hft".
  do 3 step. destruct (lookup_lt_is_Some_2 ws (Z.to_nat (k + c)) ltac:(lia)) as [y Hy]. pose proof (word_bound _ _ _ Hws Hy) as Hy32.
  iApply (wp_check_read_dq with "Hil"); [reflexivity | vx | cbn [ptr_cap]; exact Hic | a4 | a4 | a4 |]. iNext. iIntros "Hil".
  iDestruct (word_at _ _ io _ (k + c) y with "Hin") as "[Hy Hin]"; [lia | exact Hy |].
  load_bytes_dq "Hil Hy" decode (apply load_uw_char; lia) by a4. iNext. iIntros "Hil Hy". iDestruct ("Hin" with "Hy") as "Hin". step.
  Local Ltac cmp_exit := split_and!; try lia;
    [rewrite Symbolic.lookup_after_put_same; try reflexivity; try (do 2 f_equal; unwrap2; reflexivity) | same_tac].
  destruct (Z.eq_dec x y) as [<- | Nxy].
  2: { branch_as false. step. iApply ("HK" $! c with "[%] Hfl Hft Hil Hin"). cmp_exit. }
  branch_as true. do 6 step.
  destruct (lookup_lt_is_Some_2 fw (Z.to_nat (idx + (c + 1))) ltac:(lia)) as [x1 Hx1]. pose proof (word_bound _ _ _ Hfw Hx1) as Hx132.
  check_read_dq "Hfl" by a4. iNext. iIntros "Hfl".
  iDestruct (word_at _ _ 0 _ (idx + (c + 1)) x1 with "Hft") as "[Hx Hft]"; [lia | exact Hx1 |].
  load_bytes_dq "Hfl Hx" decode (apply load_uw_char; lia) by a4. iNext. iIntros "Hfl Hx". iDestruct ("Hft" with "Hx") as "Hft". step.
  destruct (Z.eq_dec x1 0) as [-> | Nx1].
  { branch_as true. step. branch_as true. step. iApply ("HK" $! (c + 1) with "[%] Hfl Hft Hil Hin"). cmp_exit. }
  branch_as false. do 6 step. step. step.
  destruct (Z.ltb_spec (k + (c + 1)) n) as [Hlt | Hge].
  - (* The next characters are equal and the input goes on, so the loop runs again. *)
    branch_w false. step.
    assert (c + 1 <> len) by (intros <-; rewrite Hz in Hx1; congruence).
    iApply ("IH" $! (c + 1) with "[%] Hfl Hft Hil Hin [HK]").
    { split_and!; try lia; try (repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]); assumption).
      rewrite Symbolic.lookup_after_put_same. do 2 f_equal. unwrap2. reflexivity. }
    iIntros (c2 e2 (Hc2 & Hk2 & Hp2 & Hs2)). iApply ("HK" $! c2 e2 with "[%]").
    split_and!; try lia; try assumption. eapply same_out_trans; [|exact Hs2]. same_tac.
  - (* The input ends after the equal characters. *)
    branch_w true. step. iApply ("HK" $! (c + 1) with "[%] Hfl Hft Hil Hin"). cmp_exit.
Qed.

End cmp.
