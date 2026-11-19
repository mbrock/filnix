(** The conversion `%d` of the formatter calls `c: _itoa_word` to turn a
    number into decimal text. This module proves that glibc's compiled
    function meets the contract [itoa_word_spec] of
    [ItoaWordSpec](ItoaWordSpec.v), so the proof of the formatter can
    use the contract and needs no fact about the function's code.

    For the base ten the function is one loop. Each round reads the
    character of the last digit from a read-only table, stores it in
    the byte below the digits it has written, and divides the number by
    ten. The loop stops when the number is zero. The proof follows the
    rounds by induction and matches them with [dec_digits_from], which
    computes the same digits in the same order. *)

From Glibc Require Import Unit_stdioZ2dcommon__fitoa_word_os.
From Glibc Require Import GlibcProgram GlibcSpec GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls Pieces StepRules Heap Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld FileInv LibioLogic PrintfSpec ItoaWordSpec.
Import ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.

(** ## How many rounds the loop needs

    The function [dec_digits_from] stops after a fixed number of
    rounds, while the C loop stops only when the number reaches zero.
    The two agree when the rounds are enough for every digit. The two
    lemmas below show that 20 rounds are enough for a 64-bit number,
    and that the count stays enough from one round to the next. *)

(** A number below 10^n has at most n digits, so n rounds of the loop
    write all of them. Each round that does not stop leaves a number
    with one digit fewer, so the next round still has enough. *)
Lemma itoa_fuel_next n u : (1 <= n)%nat -> 0 <= u < 10 ^ Z.of_nat n -> u / 10 <> 0 ->
  (1 <= n - 1)%nat /\ 0 <= u / 10 < 10 ^ Z.of_nat (n - 1).
Proof.
  intros Hn Hu Hq. destruct n as [|n]; [lia|]. replace (S n - 1)%nat with n by lia.
  rewrite Nat2Z.inj_succ Z.pow_succ_r in Hu; [|lia].
  assert (Hlo : 0 <= u / 10) by (apply Z.div_pos; lia).
  assert (Hhi : u / 10 < 10 ^ Z.of_nat n) by (apply Z.div_lt_upper_bound; lia).
  split; [|lia]. destruct n; [|lia]. cbn in Hhi. lia.
Qed.

(** A 64-bit number has at most 20 decimal digits. *)
Lemma itoa_fuel_start v : 0 <= v < 2 ^ 64 -> 0 <= v < 10 ^ Z.of_nat 20.
Proof. cbn. lia. Qed.

(** The proof of the loop states its block once. [iblk] finds the
    block of the compiled function with label l, and [iblk20] is the
    body of the loop. *)
Definition iblk (l : string) : block :=
  match find_block (TAtom l) (fn_blocks Unit_stdioZ2dcommon__fitoa_word_os.fn__itoa_word) with Some b => b | None => mkBlock (TAtom l) [] [] JUnreachable end.
Definition iblk20 : block := Eval vm_compute in iblk "L20".

(** ## The loop

    Each round of the loop reads one byte of the digit table and writes
    one byte of the caller's buffer. The caller lends the 20 bytes below
    the end of its buffer, and the function owns nothing else. The
    lemmas of this section find the one byte that a round reads or
    writes in the lent pieces, and then prove the loop. *)

Section itoa.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A share of a table's bytes holds a share of each single byte. *)
Lemma bytesq_nth dq b xs (i : nat) x : xs !! i = Some x -> bytesq dq b 0 xs ⊢ bytesq dq b (Z.of_nat i) [x].
Proof using Type.
  intros Hx. rewrite -(take_drop_middle xs i x Hx). unfold bytesq.
  rewrite byte_ps_app ptsq_app byte_ps_cons. rewrite length_take_le; [|apply lookup_lt_Some in Hx; lia].
  iIntros "[_ H]". rewrite /ptsq big_sepL_cons. iDestruct "H" as "[H _]". rewrite big_sepL_singleton. by iFrame.
Qed.

(** The table of lower-case digits holds the character of the digit
    r at its offset r. *)
Lemma lower_digit_at r : 0 <= r < 10 -> lower_digits_bytes !! Z.to_nat r = Some (48 + r).
Proof using Type.
  intros Hr. assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9) as Hc by lia.
  repeat destruct Hc as [-> | Hc]; try (subst; reflexivity).
Qed.

(** The loop writes the next digit into the byte just below the ones
    it has written. This lemma takes that byte out of the 20 lent
    bytes and puts the new digit back in its place. *)
Lemma itoa_slot b o old acc :
  length old = 20%nat -> (length acc < 20)%nat ->
  bytes b o (take (20 - length acc) old ++ acc) ⊢
  ∃ x, ibyte b (o + Z.of_nat (19 - length acc)) x ∗
    ∀ d, ibyte b (o + Z.of_nat (19 - length acc)) d -∗
      bytes b o (take (20 - length (d :: acc)) old ++ d :: acc).
Proof using Type.
  intros Hold Hk. set (k := length acc).
  destruct (lookup_lt_is_Some_2 old (19 - k) ltac:(lia)) as [x Hx].
  replace (20 - k)%nat with (S (19 - k)) by lia. rewrite (take_S_r _ _ _ Hx) -app_assoc.
  rewrite bytes_app length_take_le; [|lia]. rewrite bytes_app. cbn [length].
  iIntros "(H1 & H2 & H3)". iExists x. iSplitL "H2"; [rewrite /bytes /ibyte /byte_ps; done|].
  iIntros (d) "Hd". cbn [length]. replace (20 - S k)%nat with (19 - k)%nat by lia.
  rewrite bytes_app length_take_le; [|lia]. iFrame "H1".
  rewrite (bytes_app b _ [d] acc). cbn [length]. iFrame "H3". rewrite /bytes /ibyte /byte_ps. done.
Qed.

(** The loop starts a round with the number u and the pointer a below
    the digits acc that it has written. It ends with the digits of
    [dec_digits_from] and returns a pointer to the first of them, while
    the bytes of the buffer below them keep their old values. The count
    n is the number of rounds that remain; it must be enough for the
    digits of u and leave the digits inside the 20 lent bytes. *)
Lemma itoa_loop (n : nat) u acc a b reg hi old tb treg e Φ :
  a = b + hi - Z.of_nat (length acc) -> (1 <= n)%nat -> 0 <= u < 10 ^ Z.of_nat n -> u < 2 ^ 64 -> (length acc + n <= 20)%nat -> length old = 20%nat ->
  0 < b -> 20 <= hi -> b + hi <= r_end reg -> r_end reg <= 2 ^ 48 ->
  lookup (TAtom "v15") e = Some (WPtr (mkPtr tb (Ro tb))) ->
  0 < tb -> tb + 36 <= r_end treg -> r_end treg <= 2 ^ 63 ->
  live b reg -∗ bytes b (hi - 20) (take (20 - length acc) old ++ acc) -∗
  liveq DfracDiscarded tb treg -∗ bytesq DfracDiscarded tb 0 lower_digits_bytes -∗
  (live b reg -∗ bytes b (hi - 20) (take (20 - length (dec_digits_from n u acc)) old ++ dec_digits_from n u acc) -∗
   Φ (Ret (WPtr (mkPtr (b + hi - Z.of_nat (length (dec_digits_from n u acc))) (Obj b))))) -∗
  WP (ERun (mkFrame Unit_stdioZ2dcommon__fitoa_word_os.fn__itoa_word
      (put (TAtom "pr.1") (WInt u) (put (TAtom "pr.6") (WPtr (mkPtr a (Obj b))) e))
      [] None (Exec (TAtom "L20") (b_insts iblk20) (b_jump iblk20))) : sexpr) {{ Φ }}.
Proof using Type.
  intros Ha Hn Hu Hu64 Hk Hold Hb Hhi Hend Hmax Hv15 Htb Htend Htmax.
  revert u acc a e Ha Hn Hu Hu64 Hk Hv15. induction n as [|n IH]; intros u acc a e Ha Hn Hu Hu64 Hk Hv15; [lia|]. subst a.
  iIntros "Hl Hbs #Htl #Htb HK". cbn [iblk20 b_insts b_jump]. step. step. step. cbn [ptr_addr ptr_cap].
  assert (Hk20 : (length acc < 20)%nat) by lia.
  assert (Hum : u mod 2 ^ 64 = u) by (apply Z.mod_small; lia).
  assert (Hd : unsigned_division Z.modulo (u mod 2 ^ 64) (10 mod 2 ^ 64) = u mod 10) by (rewrite Hum; reflexivity).
  rewrite Hd. pose proof (Z.mod_pos_bound u 10 ltac:(lia)) as Hr.
  replace ((tb mod 2 ^ 64 + u mod 10 mod 2 ^ 64) mod 2 ^ 64) with (tb + u mod 10) by (rewrite !(Z.mod_small _ (2 ^ 64)); lia).
  replace (((b + hi - length acc) mod 2 ^ 64 - 1 mod 2 ^ 64) mod 2 ^ 64) with (b + hi - length acc - 1) by (rewrite !(Z.mod_small _ (2 ^ 64)); lia).
  check_read_dq "Htl" by a2. iNext. iIntros "_".
  iPoseProof (bytesq_nth _ _ _ (Z.to_nat (u mod 10)) _ (lower_digit_at _ Hr) with "Htb") as "Hdg".
  rewrite Z2Nat.id; [|lia].
  load_bytes_dq "Htl Hdg" decode (reflexivity) by a2. iNext. iIntros "_ _".
  replace (extension Sb (of_bytes [48 + u mod 10]) mod 2 ^ 32) with (48 + u mod 10)
    by (set (r := u mod 10) in *; assert (r = 0 \/ r = 1 \/ r = 2 \/ r = 3 \/ r = 4 \/ r = 5 \/ r = 6 \/ r = 7 \/ r = 8 \/ r = 9) as Hc by lia; repeat destruct Hc as [-> | Hc]; try (rewrite Hc); reflexivity).
  assert (Hkz : Z.of_nat (length acc) <= 19) by lia. check "Hl".
  iDestruct (itoa_slot with "Hbs") as (x) "[Hx Hback]"; [exact Hold | exact Hk20 |].
  iApply (wp_raw_store_byte with "Hl Hx"); [vx | vx | reflexivity | a2 | wi_store |].
  iNext. iIntros "Hl Hx". iDestruct ("Hback" with "Hx") as "Hbs".
  replace (((48 + u mod 10) mod 2 ^ 32) mod 256) with (48 + u mod 10) by (rewrite (Z.mod_small (48 + u mod 10)); [rewrite (Z.mod_small (48 + u mod 10) 256)|]; lia).
  step. step.
  assert (Hq : unsigned_division Z.div (u mod 2 ^ 64) (10 mod 2 ^ 64) = u / 10) by (rewrite Hum; reflexivity).
  rewrite Hq. cbn [dec_digits_from].
  branch_symbolic.
  assert (Hq64 : (u / 10) mod 2 ^ 64 = u / 10) by (apply Z.mod_small; split; [apply Z.div_pos | apply (Z.le_lt_trans _ u); [apply Z.div_le_upper_bound|]]; lia).
  rewrite Hq64. change (0 mod 2 ^ 64) with 0.
  destruct (Z.eqb_spec (u / 10) 0) as [Hz | Hz].
  - rewrite Hz. cbn -[put]. step. iApply wp_ret; [reflexivity | vx |]. iNext.
    cbn [Z.eqb length] in *. iEval (rewrite Nat2Z.inj_succ) in "HK".
    replace (b + hi - Z.succ (length acc)) with (b + hi - length acc - 1) by lia.
    iApply ("HK" with "Hl Hbs").
  - cbn -[put]. step.
    rewrite Hq64. destruct (itoa_fuel_next (S n) u ltac:(lia) Hu Hz) as [Hn' Hu']. replace (S n - 1)%nat with n in Hu' by lia.
    iApply (IH (u / 10) (48 + u mod 10 :: acc) with "Hl Hbs Htl Htb HK"); [cbn [length]; lia | lia | exact Hu' | apply Z.div_lt_upper_bound; lia | cbn [length]; lia | lk_prove].
Qed.

(** ## The contract

    A program may call the function by any name that its link gives
    this code. The entry blocks pick the table of lower-case digits for
    upper_case equal to zero, and they go to the loop for the base ten.
    The loop then starts with no digits written and 20 rounds. *)

(** The formatter prints a number with `%d` by calling the function
    with the base ten, and it relies on this lemma for that call. The
    lemma holds for each name n under which the program defines the
    compiled function. *)
Lemma itoa_word_has_spec (n : string) `{!Defines ge n Unit_stdioZ2dcommon__fitoa_word_os.fn__itoa_word} :
  HasSpec registry (os_wi w0) ge (TAtom n) itoa_word_spec.
Proof using Type.
  intros [[[[v b] reg] hi] old]. exists Unit_stdioZ2dcommon__fitoa_word_os.fn__itoa_word. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. injection Hfr as <-. cbn [fs_pre fs_post fs_args itoa_word_spec].
  iIntros "[%Hp (Hl & Hbs & Hro)] HK". destruct Hp as (Hv & Hb & Hhi & Hend & Hmax & Hold).
  iDestruct "Hro" as (tb treg (Hg & Htb & Htend & Htmax)) "[#Htl #Htb]".
  change (table_bytes lower_digits) with lower_digits_bytes in *.
  change (Z.of_nat (length lower_digits_bytes)) with 36 in Htend.
  step. branch. step. step_global Hg. step. step. step. branch. step.
  rewrite (Z.mod_small v); [|lia].
  iApply (itoa_loop 20 v [] (b + hi) b reg hi old tb treg with "Hl [Hbs] Htl Htb [HK]");
    [cbn [length]; lia | lia | exact (itoa_fuel_start v Hv) | lia | cbn [length]; lia | exact Hold | exact Hb | exact Hhi |
     exact Hend | exact Hmax | lk_prove | exact Htb | exact Htend | exact Htmax | rewrite app_nil_r firstn_all2; [iExact "Hbs" | cbn [length]; lia] |].
  iIntros "Hl Hbs". iApply "HK". iFrame "Hl Hbs". done.
Qed.

End itoa.
