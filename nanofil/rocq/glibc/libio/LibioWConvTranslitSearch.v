(** Transliteration looks for a replacement with a binary search over
    the C locale's sorted table of source strings. Each probe compares
    one source string with the remaining input. A full match leads to
    the replacement strings, and a search that runs out of candidates
    leads to the default replacement. This file proves that the search
    in `c: __gconv_transliterate` reads only inside the tables and the
    input.

    The search keeps two bounds, low and high, with low at most high
    and high at most the 1659 entries of each index. The midpoint of
    two such bounds is an index entry, and the image checks
    [wc_from_okb] and [wc_sizes] say where its source string ends. *)

From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic AbsInfer.
From Glibc Require Import CodePrelude CLocaleCells CtypeTranslitTables
  OsWorld FileInv LibioLogic LibioDefaultXsputnBuf CBlocks Fix LibioWConvAscii LibioWConvConsts
  LibioWConvTranslitCmp LibioWConvTranslitCall.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L FileInv LibioLogic.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation rop b := (mkPtr b (Ro b)).
Local Abbreviation fia := (conv_addr "glibc_C_ctype#translit_from_idx").
Local Abbreviation fta := (conv_addr "glibc_C_ctype#translit_from_tbl").

(** ## Strings in a table of words

    The image check [nul_at] measures a string by walking to its zero
    word. These lemmas turn a successful walk into the facts that a
    loop over the string needs: the zero word is there, and every word
    before it is not zero. *)

Lemma from_nul_at tbl f : forall p q, nul_at tbl p f = Some q ->
  tbl !! (p + q)%nat = Some 0 /\ forall i, (i < q)%nat -> exists x, tbl !! (p + i)%nat = Some x /\ x <> 0.
Proof using Type.
  induction f as [|f IH]; intros p q H; [discriminate|]. cbn in H.
  destruct (tbl !! p) as [x|] eqn:Ex; [|discriminate].
  destruct x as [|x|x].
  { injection H as <-. rewrite Nat.add_0_r. split; [exact Ex | intros; lia]. }
  all: destruct (nul_at tbl (S p) f) as [qq|] eqn:Eq; [|discriminate]; injection H as <-;
    destruct (IH _ _ Eq) as [Hz Hn]; split; [replace (p + S qq)%nat with (S p + qq)%nat by lia; exact Hz|];
    (intros [|i] Hi; [replace (p + 0)%nat with p by lia; eexists; split; [exact Ex | discriminate]|]);
    destruct (Hn i ltac:(lia)) as (y & Hy & Hy0); exists y;
    replace (p + S i)%nat with (S p + i)%nat by lia; split; [exact Hy | exact Hy0].
Qed.


(** A list passes the image's word check exactly when each element is a 32-bit word. *)
Lemma words_forall l : forallb word_okb l = true -> Forall (fun x => 0 <= x < 2 ^ 32) l.
Proof using Type.
  intros H. apply Forall_forall. intros x Hx. apply forallb_forall with (x := x) in H; [|exact Hx].
  unfold word_okb in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(** ## The names that the search assigns

    The search reads the input and the tables through pointers that
    glibc computed before the search began. Glibc computes them once,
    at the start of the function, and the search never changes them.
    The list below names every value that the search may change, so a
    proof can keep all the others. *)

(** These are the temporaries that the blocks with the given labels define. *)
Definition block_names (keep : string -> bool) : list name :=
  flat_map (fun b => app (map (fun p => match p with Phi d _ _ => d end) (b_phis b)) (flat_map inst_defs (b_insts b)))
    (filter (fun b => match b_label b with TAtom s => keep s | _ => false end) (fn_blocks glibc_translit)).

(** The search may assign every name outside the entry blocks. *)
Definition search_names : list name := Eval vm_compute in
  block_names (fun s => negb (existsb (String.eqb s) ["start"; "L31"; "L32"; "L51"]%string)).

(** Agreement outside a list survives when the list grows. A proof
    checks by computation that every name of the smaller list is in
    the larger one. *)
Lemma same_out_sub {A : Type} S T (e e' : list (name * A)) :
  forallb (fun x => existsb (name_eqb x) T) S = true -> same_out S e e' -> same_out T e e'.
Proof using Type.
  intros Hi H x Hx. apply H. destruct (existsb (name_eqb x) S) eqn:E; [|reflexivity].
  apply existsb_exists in E as (y & Hy & Ey). apply term_eqb_eq in Ey. subst y.
  apply forallb_forall with (x := x) in Hi; [|exact Hy]. rewrite Hi in Hx. discriminate.
Qed.

(** ## The search loop

    Each probe of the search reads the midpoint's entry of the source
    index, compares that source string with the input, and then either
    stops or halves the range. The proof follows the loop with the
    [[later-modality|later]] induction hypothesis of [iLöb], so every
    probe that goes around again needs no measure. These tactics handle
    the reads and jumps that the comparison loop's tactics do not. *)

(** The tactic [a5] proves an address condition of a read at the
    midpoint, which the code computes with a shift by one. *)
Local Ltac a5 := autounfold with offs; cbn [ptr_addr ptr_cap r_base r_end]; unfold raw_address;
  repeat (replace (2 ^ ((1 mod 2 ^ 32) mod 32)) with 2 by reflexivity); a4.

(** The tactic [branch_z] follows a jump like [branch_w] does. It
    also handles the unsigned comparison that asks whether the input
    has ended, and the comparisons for equality. *)
Local Ltac branch_z b :=
  iStartProof; eapply step_wand; [eapply wp_branch; inst; vx |];
  lazymatch goal with |- context [edge_label (if ?n =? 0 then _ else _)] =>
    let E := fresh "E" in assert (E : (n =? 0) = b) by (wnorm;
      repeat match goal with
        | |- context [?x <? ?y] => destruct (Z.ltb_spec x y)
        | |- context [?x <=? ?y] => destruct (Z.leb_spec x y)
        | |- context [?x =? ?y] => lazymatch x with context [if _ then _ else _] => fail | _ mod _ => fail | _ => destruct (Z.eqb_spec x y) end end;
      cbn; first [reflexivity | exfalso; lia]);
    rewrite E; clear E end; cbn [edge_label].

(** The tactic [search_env] proves the facts about the bounds that the
    loop header needs when the search goes around again. *)
Local Ltac search_env := split_and!; try lia;
  [repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]); rewrite Symbolic.lookup_after_put_same;
   do 2 f_equal; unwrap2; lia.. | same_tac].

(** The tactic [probe_lookup] finds the value of a name after a probe.
    It looks through the assignments since the probe, and through any
    stretch of code that keeps the name. *)
Local Ltac probe_lookup := repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]);
  first [assumption | match goal with H : same_out _ _ _ |- _ => erewrite H; [probe_lookup | reflexivity] end].

(** The tactic [probe_env] proves what a later block of the search
    needs to know about the values that one probe computed. *)
Local Ltac probe_env := split_and!; try lia; try probe_lookup; try same_tac;
  try match goal with H : same_out repl_names _ ?E |- same_out search_names _ ?E =>
    eapply same_out_trans; [|apply (same_out_sub repl_names); [vm_compute; reflexivity | exact H]]; same_tac end.

Section search.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The search ends in one of three ways: it finds a source string that
    starts the input, it runs out of candidates, or the input ends in
    the middle of a source string. This lemma proves the search from
    its loop header `c: L116` with any bounds low and high. The caller
    lends the frame G for the rest of the call, and a failed
    replacement may change the output bytes and the flags that G
    holds. The continuation K181 tries the replacements and may resume
    the search, K54 uses the default replacement, and K7 returns 7 so
    that the caller supplies more input. *)
Lemma translit_search (G : list Z -> Z -> iProp Σ) Φ e0 dI dqb ib ireg io ic ws k :
  let n := Z.of_nat (length ws) in
  0 < ib -> 0 <= io -> ib + io + 4 * n <= r_end ireg -> r_end ireg <= 2 ^ 63 -> ic = Obj ib \/ ic = Ro ib ->
  Forall (fun x => 0 <= x < 2 ^ 32) ws -> 0 <= k < n ->
  lookup (TAtom "v24") e0 = Some (WPtr (mkPtr (ib + io + 4 * k) ic)) ->
  lookup (TAtom "v103") e0 = Some (WInt (ib + io + 4 * n)) ->
  lookup (TAtom "v65") e0 = Some (WPtr (rop fia)) -> lookup (TAtom "v75") e0 = Some (WPtr (rop fta)) ->
  wconv_consts -∗
  □ (∀ e' zs fl med c, ⌜same_out search_names e0 e' /\ 0 <= med < 1659 /\ 0 < c < 2 ^ 31 /\ k + c <= n /\
        lookup (TAtom "v132") e' = Some (WInt (4 * med)) /\ lookup (TAtom "pr.6") e' = Some (WInt c)⌝ -∗
      liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs fl -∗
      (∀ e'' zs' fl', ⌜same_out repl_names e' e''⌝ -∗ liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs' fl' -∗
        WP (ERun (mkFrame glibc_translit e'' [] None (body_at glibc_translit "L183")) : sexpr) {{ Φ }}) -∗
      WP (ERun (mkFrame glibc_translit e' [] None (body_at glibc_translit "L181")) : sexpr) {{ Φ }}) -∗
  □ (∀ e' zs fl, ⌜same_out search_names e0 e'⌝ -∗ liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs fl -∗
      WP (ERun (mkFrame glibc_translit e' [] None (body_at glibc_translit "L54")) : sexpr) {{ Φ }}) -∗
  □ (∀ zs fl, liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs fl -∗ Φ (Ret (WInt 7))) -∗
  ∀ lo hi e zs fl, ⌜0 <= lo <= hi /\ hi <= 1659 /\ lookup (TAtom "pr.1") e = Some (WInt lo) /\
      lookup (TAtom "pr.3") e = Some (WInt hi) /\ same_out search_names e0 e⌝ -∗
    liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs fl -∗
    WP (ERun (mkFrame glibc_translit e [] None (body_at glibc_translit "L116")) : sexpr) {{ Φ }}.
Proof using Type*.
  intros n Hib Hio Hie Hir Hic Hws Hk V24 V103 V65 V75. iIntros "#Hc #K181 #K54 #K7".
  iDestruct "Hc" as "(_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hfil & Hfib & Hftl & Hftb & _)".
  iLöb as "IH". iIntros (lo hi e zs fl (Hlo & Hhi & P1 & P3 & Hs)) "Hil Hin HG".
  pose proof (Hs (TAtom "v24") eq_refl) as L24. pose proof (Hs (TAtom "v103") eq_refl) as L103.
  pose proof (Hs (TAtom "v65") eq_refl) as L65. pose proof (Hs (TAtom "v75") eq_refl) as L75.
  rewrite ?V24 ?V103 ?V65 ?V75 in L24 L103 L65 L75.
  body_start glibc_translit "L116". step.
  destruct (Z.ltb_spec lo hi) as [Hlh | Hlh].
  2: { branch_as true. step. iApply ("K54" $! _ zs fl with "[%] Hil Hin HG"). same_tac. }
  branch_as false. do 5 step.
  assert (Hmed : lo <= (lo + hi) / 2 < hi) by (split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; lia).
  set (med := (lo + hi) / 2) in *.
  destruct (lookup_lt_is_Some_2 wc_from_idx (Z.to_nat med) ltac:(rewrite (proj1 wc_sizes); lia)) as [idx Hidx].
  pose proof wc_words_okb as Hok.
  assert (Hidx32 : 0 <= idx < 2 ^ 32).
  { apply forallb_forall with (x := idx) in Hok; [unfold word_okb in Hok; lia|].
    apply in_or_app; left. apply list_elem_of_In. eapply list_elem_of_lookup_2. exact Hidx. }
  step. check_read_dq "Hfil" by a5. iNext. iIntros "_".
  iDestruct (word_at _ _ 0 _ med idx with "Hfib") as "[Hx _]"; [lia | exact Hidx |].
  load_bytes_dq "Hfil Hx" decode (apply load_uw_char; lia) by a5. iNext. iIntros "_ _". step.
  pose proof wc_from_okb as Hfo. apply forallb_forall with (x := idx) in Hfo;
    [|apply list_elem_of_In; eapply list_elem_of_lookup_2; exact Hidx].
  unfold from_okb in Hfo. apply andb_prop in Hfo as [Hi0 Hfo]. apply Z.leb_le in Hi0.
  change (wc_from_tbl ++ [0]) with wc_ft in Hfo.
  assert (Hq : exists q, nul_at wc_ft (Z.to_nat idx) 64 = Some (S q)).
  { clear - Hfo. destruct (nul_at wc_ft (Z.to_nat idx) 64) as [[|q]|]; try discriminate. eauto. }
  destruct Hq as [q Eq]. clear Hfo.
  destruct (from_nul_at _ _ _ _ Eq) as [Hz _].
  assert (Hftn : Z.of_nat (length wc_ft) = 3318) by (vm_compute; reflexivity).
  pose proof (words_forall wc_ft ltac:(vm_compute; reflexivity)) as Hftw.
  set (len := Z.of_nat (S q)).
  assert (Hzl : wc_ft !! Z.to_nat (idx + len) = Some 0) by (rewrite <- Hz; f_equal; lia).
  assert (Hil3 : idx + len < 3318) by (pose proof (lookup_lt_Some _ _ _ Hzl); lia).
  lazymatch goal with |- context [ERun (mkFrame _ ?E _ _ _)] => set (e1 := E) end.
  assert (R126 : lookup (TAtom "v126") e1 = Some (WInt med)).
  { subst e1. repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]). rewrite Symbolic.lookup_after_put_same.
    replace (2 ^ ((1 mod 2 ^ 32) mod 32)) with 2 by reflexivity. unwrap2. reflexivity. }
  assert (R132 : lookup (TAtom "v132") e1 = Some (WInt (4 * med))).
  { subst e1. repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]). rewrite Symbolic.lookup_after_put_same.
    replace (2 ^ ((1 mod 2 ^ 32) mod 32)) with 2 by reflexivity. replace (2 ^ ((2 mod 2 ^ 32) mod 64)) with 4 by reflexivity.
    unwrap2. do 2 f_equal. fold med. lia. }
  assert (R134 : lookup (TAtom "v134") e1 = Some (WInt idx)) by (subst e1; apply Symbolic.lookup_after_put_same).
  assert (Re1 : same_out search_names e0 e1) by (subst e1; same_tac).
  pose proof (Re1 (TAtom "v24") eq_refl) as R24. pose proof (Re1 (TAtom "v103") eq_refl) as R103.
  pose proof (Re1 (TAtom "v75") eq_refl) as R75. rewrite ?V24 ?V103 ?V75 in R24 R103 R75.
  assert (R1 : lookup (TAtom "pr.1") e1 = Some (WInt lo)) by (subst e1; repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]); exact P1).
  assert (R3 : lookup (TAtom "pr.3") e1 = Some (WInt hi)) by (subst e1; repeat (rewrite Symbolic.lookup_after_put_other; [|reflexivity]); exact P3).
  clearbody e1. clear L24 L103 L65 L75.
  iClear "Hx".
  iAssert (□ ∀ c e' zs' fl', ⌜0 <= c <= len /\ k + c <= n /\ lookup (TAtom "pr.6") e' = Some (WInt c) /\
      lookup (TAtom "v134") e' = Some (WInt idx) /\ lookup (TAtom "v126") e' = Some (WInt med) /\
      lookup (TAtom "pr.1") e' = Some (WInt lo) /\ lookup (TAtom "pr.3") e' = Some (WInt hi) /\
      same_out search_names e0 e'⌝ -∗ liveq dI ib ireg -∗ bytesq dqb ib io (le_words ws) -∗ G zs' fl' -∗
      WP (ERun (mkFrame glibc_translit e' [] None (body_at glibc_translit "L183")) : sexpr) {{ Φ }})%I as "#H183".
  { iIntros "!>" (c e' zs' fl' (Hc & Hkc & Q6 & Q134 & Q126 & Q1 & Q3 & Hs')) "Hil Hin HG".
    pose proof (Hs' (TAtom "v24") eq_refl) as Q24. pose proof (Hs' (TAtom "v103") eq_refl) as Q103.
    pose proof (Hs' (TAtom "v75") eq_refl) as Q75. rewrite ?V24 ?V103 ?V75 in Q24 Q103 Q75.
    body_start glibc_translit "L183". do 5 step.
    destruct (Z.ltb_spec (k + c) n) as [Hlt | Hge].
    - branch_z true. step.
    do 4 step.
    destruct (lookup_lt_is_Some_2 wc_ft (Z.to_nat (idx + c)) ltac:(lia)) as [x Hx]. pose proof (word_bound _ _ _ Hftw Hx) as Hx32.
    check_read_dq "Hftl" by a4. iNext. iIntros "_".
    iDestruct (word_at _ _ 0 _ (idx + c) x with "Hftb") as "[Hw _]"; [lia | exact Hx |].
    load_bytes_dq "Hftl Hw" decode (apply load_uw_char; lia) by a4. iNext. iIntros "_ _".
    destruct (lookup_lt_is_Some_2 ws (Z.to_nat (k + c)) ltac:(lia)) as [y Hy]. pose proof (word_bound _ _ _ Hws Hy) as Hy32.
    iApply (wp_check_read_dq with "Hil"); [reflexivity | vx | cbn [ptr_cap]; exact Hic | a4 | a4 | a4 |]. iNext. iIntros "Hil".
    iDestruct (word_at _ _ io _ (k + c) y with "Hin") as "[Hy Hin]"; [lia | exact Hy |].
    load_bytes_dq "Hil Hy" decode (apply load_uw_char; lia) by a4. iNext. iIntros "Hil Hy". iDestruct ("Hin" with "Hy") as "Hin".
    step. step.
      step. destruct (Z.ltb_spec x y) as [Hxy | Hxy].
      + branch_z false. do 4 step.
        iApply ("IH" $! (med + 1) hi _ zs' fl' with "[%] Hil Hin HG"). search_env.
      + branch_z true. step.
        iApply ("IH" $! lo med _ zs' fl' with "[%] Hil Hin HG"). search_env.
    - branch_z false. step. branch_z false. do 4 step.
      iApply ("IH" $! (med + 1) hi _ zs' fl' with "[%] Hil Hin HG"). search_env. }
  step.
  iApply (translit_cmp [] DfracDiscarded fta _ wc_ft idx len dqb dI ib ireg io ic ws k Φ $! 0 with "[%] Hftl Hftb Hil Hin [HG]");
    try solve [cbn [r_end]; lia | assumption].
  { split_and!; try lia; try (rewrite Symbolic.lookup_after_put_other; [assumption|reflexivity]). apply Symbolic.lookup_after_put_same. }
  iIntros (c' e' (Hc' & Hkc' & Q6 & Hs')) "_ _ Hil Hin".
  assert (Hs1 : same_out cmp_names e1 e') by (eapply same_out_trans; [|exact Hs']; same_tac).
  assert (Hs2 : same_out search_names e0 e') by
    (eapply same_out_trans; [exact Re1 | apply (same_out_sub cmp_names); [vm_compute; reflexivity | exact Hs1]]).
  assert (Q134 : lookup (TAtom "v134") e' = Some (WInt idx)) by (rewrite (Hs1 (TAtom "v134") eq_refl); exact R134).
  assert (Q126 : lookup (TAtom "v126") e' = Some (WInt med)) by (rewrite (Hs1 (TAtom "v126") eq_refl); exact R126).
  assert (Q132 : lookup (TAtom "v132") e' = Some (WInt (4 * med))) by (rewrite (Hs1 (TAtom "v132") eq_refl); exact R132).
  assert (Q1 : lookup (TAtom "pr.1") e' = Some (WInt lo)) by (rewrite (Hs1 (TAtom "pr.1") eq_refl); exact R1).
  assert (Q3 : lookup (TAtom "pr.3") e' = Some (WInt hi)) by (rewrite (Hs1 (TAtom "pr.3") eq_refl); exact R3).
  pose proof (Hs2 (TAtom "v24") eq_refl) as Q24. pose proof (Hs2 (TAtom "v103") eq_refl) as Q103.
  pose proof (Hs2 (TAtom "v75") eq_refl) as Q75. rewrite ?V24 ?V103 ?V75 in Q24 Q103 Q75.
  body_start glibc_translit "L137". step. destruct (Z.eq_dec c' 0) as [-> | Hc0].
  { branch_z true. step. branch_z true. step. branch_z true. step. branch_z true. step.
    iApply ("H183" $! 0 _ zs fl with "[%] Hil Hin HG"). probe_env. }
  branch_z false. do 5 step.
  destruct (lookup_lt_is_Some_2 wc_ft (Z.to_nat (idx + c')) ltac:(lia)) as [x Hx]. pose proof (word_bound _ _ _ Hftw Hx) as Hx32.
  check_read_dq "Hftl" by a4. iNext. iIntros "_".
  iDestruct (word_at _ _ 0 _ (idx + c') x with "Hftb") as "[Hw _]"; [lia | exact Hx |].
  load_bytes_dq "Hftl Hw" decode (apply load_uw_char; lia) by a4. iNext. iIntros "_ _". do 3 step.
  destruct (Z.eq_dec x 0) as [-> | Nx].
  { branch_z false. step.
    lazymatch goal with |- context [ERun (mkFrame _ ?E _ _ _)] =>
      iApply ("K181" $! E zs fl med c' with "[%] Hil Hin HG"); [probe_env|] end.
    iIntros (e2 zs2 fl2 Hr) "Hil Hin HG". iApply ("H183" $! c' e2 zs2 fl2 with "[%] Hil Hin HG"). probe_env. }
  branch_z true. step. branch_z false. do 6 step. step. step.
  destruct (Z.eq_dec (k + c') n) as [Hend | Hend].
  - branch_z false. step. iApply wp_ret; [reflexivity | vx |]. iNext. iApply ("K7" with "Hil Hin HG").
  - branch_z true. step. iApply ("H183" $! c' _ zs fl with "[%] Hil Hin HG"). probe_env.
Qed.

End search.
