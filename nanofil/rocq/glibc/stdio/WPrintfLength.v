(** The wide string conversion measures its argument before deciding
    whether to pad it. The image's length loop examines four characters
    per iteration but tests each character before loading the next one.
    It therefore needs only the string and its four-byte terminator. *)

From Glibc Require Import HelloImageTypedWC.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import CodePrelude Fix OsWorld FileInv LibioLogic CBlocks WPrintfDispatch.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic.
Open Scope Z_scope.

Definition wprintf_length_fn := hello_image_fn___wcslen.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Abbreviation size cs := (Z.of_nat (length cs)).

Section scan.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Abbreviation sexpr := (language.expr (nanofil_lang registry ge)).

(** The reader borrows one whole character. The same rule applies to
    the mutable argument and the read-only format literal. *)
Lemma wchar_at dq b o cs k x : cs !! k = Some x ->
  bytesq dq b o (stage_bytes cs) ⊢ bytesq dq b (o + 4*Z.of_nat k) (le_bytes x 4) ∗
    (bytesq dq b (o + 4*Z.of_nat k) (le_bytes x 4) -∗ bytesq dq b o (stage_bytes cs)).
Proof using Type.
  intros Hk. rewrite -{1 2}(take_drop_middle cs k x Hk) /stage_bytes flat_map_app. cbn [flat_map].
  rewrite /bytesq byte_ps_app byte_ps_app !ptsq_app. fold (stage_bytes (take k cs)).
  rewrite stage_bytes_length length_take_le; [|apply lookup_lt_Some in Hk; lia].
  replace (Z.of_nat (4*k)) with (4*Z.of_nat k) by lia. iIntros "(Hp & Hc & Hs)". iFrame "Hc". iIntros "Hc". iFrame.
Qed.

Local Lemma length_char dq b cs i : 0 <= i <= size cs -> Forall (fun c => 0 < c < 256) cs ->
  bytesq dq b 0 (stage_bytes (cs ++ [0])) ⊢ ∃ x, ⌜(x = 0 /\ i = size cs) \/ (0 < x < 256 /\ i < size cs)⌝ ∗
  bytesq dq b (4*i) (le_bytes x 4) ∗ (bytesq dq b (4*i) (le_bytes x 4) -∗ bytesq dq b 0 (stage_bytes (cs ++ [0]))).
Proof using Type.
  intros Hi Hcs. destruct (Z.eq_dec i (size cs)) as [->|Hlt].
  - iIntros "H". iExists 0. iSplit; [iPureIntro; by left|].
    iApply (wchar_at _ _ 0 _ (length cs) 0 with "H"). by rewrite lookup_app_r; [rewrite Nat.sub_diag|lia].
  - destruct (lookup_lt_is_Some_2 cs (Z.to_nat i) ltac:(lia)) as [x Hx]. iIntros "H". iExists x. iSplit.
    + iPureIntro. right. split; [exact (Forall_lookup_1 _ _ _ _ Hcs Hx)|lia].
    + replace (4*i) with (0 + 4*Z.of_nat (Z.to_nat i)) by lia. iApply (wchar_at with "H"). by apply lookup_app_l_Some.
Qed.

(** Each unrolled test either returns the full length or establishes
    that loading the following character stays within the allocation. *)
Local Lemma length_loop dq b br cs Φ : 0 < b -> b+4*size cs+4 <= r_end br -> r_end br <= 2^63 ->
  Forall (fun c => 0 < c < 256) cs -> ∀ i e, 0 <= i <= size cs ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr b (Obj b))) -> lookup (TAtom "pr.1") e = Some (WInt i) ->
  liveq dq b br -∗ bytesq dq b 0 (stage_bytes (cs ++ [0])) -∗
  (liveq dq b br -∗ bytesq dq b 0 (stage_bytes (cs ++ [0])) -∗ Φ (Ret (WInt (size cs)))) -∗
  WP (ERun (mkFrame wprintf_length_fn e [] None (body_at wprintf_length_fn "L3")) : sexpr) {{ Φ }}.
Proof using Type.
  intros Hb He Hr V. iIntros (i e Hi Hb' Hi') "Hl Hs HK". iLöb as "IH" forall (i e Hi Hb' Hi').
  body_start wprintf_length_fn "L3"%string.
  Local Ltac read_char cs idx := let x := fresh "x" in let Hx := fresh "Hx" in let Vx := fresh "Vx" in
    iDestruct (length_char _ _ cs idx ltac:(lia) ltac:(assumption) with "Hs") as (x Hx) "[Hx Hback]";
    assert (Vx : 0 <= x < 2^32) by (destruct Hx as [[-> _]|[? _]]; lia);
    norm; change (2 ^ (2 mod 64)) with 4; unwrap2;
    check_read_dq "Hl" by (cbn [ptr_addr]; unfold raw_address; unwrap2; lia); iNext; iIntros "Hl";
    load_bytes_dq "Hl Hx" decode (apply load_sw_int; lia) by (cbn [ptr_addr]; unfold raw_address; unwrap2; lia);
    iNext; iIntros "Hl Hx"; iDestruct ("Hback" with "Hx") as "Hs"; step;
    destruct Hx as [[-> ?]|[? ?]].
  Local Ltac end_scan cs := branch; step; iApply wp_ret; [reflexivity|vx|]; iNext; norm; unwrap2;
    lazymatch goal with |- environments.envs_entails _ (?P (Ret (WInt ?z))) => replace z with (size cs) by lia end;
    by iApply ("HK" with "Hl Hs").
  do 2 step. read_char cs i. { end_scan cs. } branch_as false. step.
  do 3 step. read_char cs (i+1). { end_scan cs. } branch_as true. step.
  do 3 step. read_char cs (i+2). { end_scan cs. } branch_as true. step.
  do 3 step. read_char cs (i+3). { end_scan cs. } branch_as true. step.
  do 3 step. iApply ("IH" $! (i+4) _ with "[%] [%] [%] Hl Hs HK"); [lia|lk_prove|]. lookups. unwrap2. f_equal. f_equal. lia.
Qed.

(** The returned length counts characters, not bytes. It excludes the
    terminator and imposes no signed-int bound on the greeting. *)
Lemma wp_wprintf_length fr dq b br cs Φ :
  call_frame wprintf_length_fn [WPtr (mkPtr b (Obj b))] = Some fr ->
  0 < b -> b+4*size cs+4 <= r_end br -> r_end br <= 2^63 -> Forall (fun c => 0 < c < 256) cs ->
  liveq dq b br -∗ bytesq dq b 0 (stage_bytes (cs ++ [0])) -∗
  ▷ (liveq dq b br -∗ bytesq dq b 0 (stage_bytes (cs ++ [0])) -∗ Φ (Ret (WInt (size cs)))) -∗ WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hb He Hr V. injection Hfr as <-. iIntros "Hl Hs HK". do 3 step.
  iApply (length_loop dq b br cs Φ Hb He Hr V 0 _ with "Hl Hs HK"); [lia|reflexivity|reflexivity].
Qed.
End scan.
