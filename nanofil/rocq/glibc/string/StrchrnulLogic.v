(** In C, `c: strchrnul(p, c)` returns a pointer to the first occurrence
    of `c mod 256` in the string at `p`, or to the terminating NUL byte
    if `c mod 256` does not appear. Glibc's `c: strchr(p, c)` calls
    `c: strchrnul` and checks whether the stopped byte equals `c mod 256`,
    returning null if it does not. This module proves frame and call
    specifications for both functions over a [word_string] at any
    ownership share.

    Glibc's `__strchrnul` reads 8-byte [[word|words]] starting from the
    aligned word containing `p`. On the first word it marks every byte
    that equals zero or `c mod 256` and shifts away any bytes before `p`;
    on subsequent words it uses a faster mask that is exact up to the
    first matching byte. Once a word contains a match, a population count
    recovers the byte offset within the word. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrchrCode MemchrLast MemchrLogic
  StrcmpCode StrcmpBits StrcmpLoop.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Where strchrnul stops

    Both `c: strchrnul` and `c: strchr` scan a string until they hit
    either the target byte `cc` or the terminating NUL byte. We define
    [chr_idx] as the offset of that first stopping byte and prove that
    no earlier byte in the string can stop the scan. *)

(** Predicate [hitb] returns `true` when byte x is either NUL or the
    target byte cc. *)
Definition hitb (cc x : Z) : bool := (x =? 0) || (x =? cc).

(** Function [chr_idx] computes the byte offset of the first occurrence
    of cc in string s, or the length of s if cc does not appear. *)
Fixpoint chr_idx (cc : Z) (s : list Z) : nat :=
  match s with [] => O | x :: s' => if x =? cc then O else S (chr_idx cc s') end.

(** The stopping index `[chr_idx] cc s` never exceeds the length of s. *)
Lemma chr_idx_le cc s : (chr_idx cc s <= List.length s)%nat.
Proof. induction s as [|x s IH]; cbn [chr_idx List.length]; [lia|]. destruct (x =? cc); lia. Qed.

(** Looking up `[chr_idx] cc s` in the NUL-terminated byte list
    `s ++ [0]` always produces a stopping byte under [hitb]. *)
Lemma chr_idx_at cc s : hitb cc (nth (chr_idx cc s) (s ++ [0]) 0) = true.
Proof.
  induction s as [|x s IH]; cbn [chr_idx]; [reflexivity|].
  destruct (Z.eqb_spec x cc) as [->|]; [|exact IH]. cbn. unfold hitb. rewrite Z.eqb_refl orb_true_r. reflexivity.
Qed.

(** When every byte in string s is nonzero, no byte strictly before
    `[chr_idx] cc s` satisfies [hitb]. *)
Lemma chr_idx_below cc s j : Forall (fun x => 0 < x < 256) s -> (j < chr_idx cc s)%nat ->
  hitb cc (nth j (s ++ [0]) 0) = false.
Proof.
  revert j. induction s as [|x s IH]; intros j Hs Hj; cbn [chr_idx] in Hj; [lia|].
  apply Forall_cons_1 in Hs as [Hx Hs]. destruct (Z.eqb_spec x cc) as [->|Hne]; [lia|].
  destruct j as [|j]; cbn [app nth].
  - unfold hitb. apply orb_false_iff. split; apply Z.eqb_neq; lia.
  - apply IH; [exact Hs | lia].
Qed.

(** On any valid string window [str_shape], the byte at [chr_idx] is a
    stopping byte under [hitb] and every earlier byte is not. *)
Lemma shape_stop p b reg ws s cc : str_shape p b reg ws s ->
  hitb cc (sbyte p ws (Z.of_nat (chr_idx cc s))) = true /\
  forall j, 0 <= j < Z.of_nat (chr_idx cc s) -> hitb cc (sbyte p ws j) = false.
Proof.
  intros Hs. pose proof (sbyte_agree _ _ _ _ _ Hs) as A. pose proof (chr_idx_le cc s) as Hl. split.
  - rewrite A; [|lia]. rewrite Nat2Z.id. apply chr_idx_at.
  - intros j Hj. rewrite A; [|lia]. apply chr_idx_below; [exact (ss_chars _ _ _ _ _ Hs) | lia].
Qed.

(** Function [strchr_ptr] computes the pointer returned by `c: strchr`:
    it advances p to `[chr_idx] cc s` when cc is found or zero, and
    returns null otherwise. *)
Definition strchr_ptr (p : ptr) (cc : Z) (s : list Z) : ptr :=
  if (chr_idx cc s <? List.length s)%nat || (cc =? 0) then ptr_add p (Z.of_nat (chr_idx cc s)) else mkPtr 0 CNone.

(** Every element of the NUL-terminated byte list `s ++ [0]` lies in the
    unsigned byte range `0 <= b < 256`. *)
Lemma nth_byte_range n s : Forall (fun x => 0 < x < 256) s -> 0 <= nth n (s ++ [0]) 0 < 256.
Proof.
  intros Hs. destruct (Nat.lt_ge_cases n (List.length s)) as [H|H].
  - rewrite app_nth1; [|exact H]. rewrite Forall_forall in Hs. pose proof (Hs _ (proj2 (list_elem_of_In _ _) (nth_In s 0 H))). lia.
  - rewrite app_nth2; [|exact H]. destruct (n - List.length s)%nat as [|[|]]; cbn; lia.
Qed.

(** Checking whether `c: strchr` succeeded reduces to comparing the byte
    at `[chr_idx] cc s` against `cc`. *)
Lemma strchr_hit cc s : 0 <= cc < 256 -> Forall (fun x => 0 < x < 256) s ->
  ((chr_idx cc s <? List.length s)%nat || (cc =? 0)) = (nth (chr_idx cc s) (s ++ [0]) 0 =? cc).
Proof.
  intros Hcc Hs. induction s as [|x s IH]; cbn [chr_idx List.length].
  - destruct cc; cbn; reflexivity || lia.
  - apply Forall_cons_1 in Hs as [Hx Hs]. destruct (Z.eqb_spec x cc) as [->|Hne].
    + cbn. rewrite Z.eqb_refl. reflexivity.
    + cbn [app nth]. rewrite (IH Hs). reflexivity.
Qed.

(** ## The masks

    To test eight bytes in parallel for either NUL or target byte c,
    `__strchrnul` combines the zero-byte mask of word x with the
    zero-byte mask of `x` XOR `[rep] c`. The lemmas in this section
    characterize both the exact first-word mask [cmask] (and its shift
    [cshift]) and the loop mask [lmask]. *)

(** Bitwise XOR of two 64-bit integers stays within the 64-bit unsigned
    range. *)
Lemma lxor_range a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lxor a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (E : Z.lxor a b mod 2 ^ 64 = Z.lxor a b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2; [|lia]. rewrite Z.lxor_spec.
    destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
    rewrite (bits64 a n Ha E) (bits64 b n Hb E). reflexivity. }
  rewrite -E. apply Z.mod_pos_bound. lia.
Qed.

(** The exact zero-byte mask [first_mask] always fits in 64 bits. *)
Lemma first_mask_range x : 0 <= first_mask x < 2 ^ 64.
Proof. unfold first_mask. apply lxor_range; [apply Z.mod_pos_bound; lia | vm_compute; split; congruence]. Qed.

(** Function [cmask] marks every byte lane of word x that equals zero or
    `c mod 256` by combining two [first_mask] results. *)
Definition cmask (x c : Z) : Z := Z.lor (first_mask x) (first_mask (Z.lxor x (rep c))).

(** Function [lmask] computes the cheaper loop mask for word x, which
    remains exact up through the earliest stopping byte. *)
Definition lmask (x c : Z) : Z := Z.lor (loop_mask x) (loop_mask (Z.lxor x (rep c))).

(** When byte i of x is neither zero nor `c mod 256`, both x and
    `x` XOR `[rep] c` have a nonzero byte at lane i. *)
Lemma xor_nonzero x c i : 0 <= i < 8 -> hitb (c mod 256) (byte_of x i) = false ->
  byte_of x i <> 0 /\ byte_of (Z.lxor x (rep c)) i <> 0.
Proof.
  intros Hi H. unfold hitb in H. apply orb_false_iff in H as [H1 H2]. apply Z.eqb_neq in H1, H2.
  split; [exact H1|]. intros E. apply H2. apply xor_zero; [exact Hi | exact E].
Qed.

(** Byte lane i of `[cmask] x c` holds 128 when byte i of x satisfies
    [hitb], and zero otherwise. *)
Lemma cmask_byte x c i : 0 <= i < 8 -> byte_of (cmask x c) i = if hitb (c mod 256) (byte_of x i) then 128 else 0.
Proof.
  intros Hi. unfold cmask, hitb. rewrite byte_of_lor; [|lia]. rewrite !first_mask_byte; [|lia|lia].
  destruct (Z.eqb_spec (byte_of (Z.lxor x (rep c)) i) 0) as [E|E].
  - apply xor_zero in E; [|lia]. rewrite E Z.eqb_refl orb_true_r. destruct (_ =? 0); reflexivity.
  - replace (byte_of x i =? c mod 256) with false; [rewrite orb_false_r; destruct (_ =? 0); reflexivity|].
    symmetry. apply Z.eqb_neq. intros E'. apply E. apply xor_zero; [lia | exact E'].
Qed.

(** The broadcast word `[rep] c` always lies in the 64-bit unsigned
    range. *)
Lemma rep_range c : 0 <= rep c < 2 ^ 64.
Proof. unfold rep. apply Z.mod_pos_bound. lia. Qed.

(** The combined exact mask `[cmask] x c` always fits in 64 bits. *)
Lemma cmask_range x c : 0 <= cmask x c < 2 ^ 64.
Proof. apply lor_range; apply first_mask_range. Qed.

(** The combined loop mask `[lmask] x c` always fits in 64 bits. *)
Lemma lmask_range x c : 0 <= lmask x c < 2 ^ 64.
Proof. apply lor_range; apply loop_mask_range. Qed.

(** Every byte lane of `[lmask] x c` is either 0 or 128. *)
Lemma lmask_01 x c i : 0 <= i < 8 -> byte_of (lmask x c) i = 0 \/ byte_of (lmask x c) i = 128.
Proof.
  intros Hi. unfold lmask. rewrite byte_of_lor; [|lia].
  destruct (loop_mask_01 x i Hi) as [-> | ->], (loop_mask_01 (Z.lxor x (rep c)) i Hi) as [-> | ->]; cbn; auto.
Qed.

(** Every byte lane of `[lmask] x c` strictly before the word's first
    stopping byte j is zero. *)
Lemma lmask_below x c j i : j <= 8 -> (forall i, 0 <= i < j -> hitb (c mod 256) (byte_of x i) = false) ->
  0 <= i < j -> byte_of (lmask x c) i = 0.
Proof.
  intros Hj Hn Hi. unfold lmask. rewrite byte_of_lor; [|lia].
  rewrite (loop_mask_below x j i Hj); [|intros k Hk; apply (xor_nonzero x c k); [lia | apply Hn; lia] | lia].
  rewrite (loop_mask_below (Z.lxor x (rep c)) j i Hj); [reflexivity| |lia].
  intros k Hk. apply (xor_nonzero x c k); [lia | apply Hn; lia].
Qed.

(** At the word's earliest stopping byte j, lane j of `[lmask] x c`
    equals 128. *)
Lemma lmask_at x c j : 0 <= j < 8 -> (forall i, 0 <= i < j -> hitb (c mod 256) (byte_of x i) = false) ->
  hitb (c mod 256) (byte_of x j) = true -> byte_of (lmask x c) j = 128.
Proof.
  intros Hj Hn Hh. unfold lmask. rewrite byte_of_lor; [|lia].
  assert (N1 : forall i, 0 <= i < j -> byte_of x i <> 0) by (intros i Hi; apply (xor_nonzero x c i); [lia | auto]).
  assert (N2 : forall i, 0 <= i < j -> byte_of (Z.lxor x (rep c)) i <> 0)
    by (intros i Hi; apply (xor_nonzero x c i); [lia | auto]).
  unfold hitb in Hh. apply orb_true_iff in Hh as [H|H]; apply Z.eqb_eq in H.
  - rewrite (loop_mask_at x j Hj N1 H).
    destruct (loop_mask_01 (Z.lxor x (rep c)) j ltac:(lia)) as [-> | ->]; reflexivity.
  - rewrite (loop_mask_at (Z.lxor x (rep c)) j Hj N2 ltac:(apply xor_zero; [lia | exact H])).
    destruct (loop_mask_01 x j ltac:(lia)) as [-> | ->]; reflexivity.
Qed.

(** Function [cshift] shifts `[cmask] x c` right by k bytes to discard
    any bytes in the first aligned word that lie before the string. *)
Definition cshift (x c k : Z) : Z := cmask x c / 2 ^ (8 * k).

(** Computing `8 * (a mod 8)` in the IR yields the exact bit-shift
    count for discarding unaligned leading bytes at address a. *)
Lemma shift_amount a : 0 <= a < 2 ^ 64 ->
  ((Z.land (a mod 2 ^ 64) (7 mod 2 ^ 64) mod 2 ^ 64 * 2 ^ ((3 mod 2 ^ 32) mod 64)) mod 2 ^ 64) mod 2 ^ 32 mod 64
  = 8 * (a mod 8).
Proof.
  intros Ha. rewrite (Z.mod_small a); [|lia]. change (7 mod 2 ^ 64) with (Z.ones 3). rewrite Z.land_ones; [|lia].
  change (2 ^ 3) with 8. change (2 ^ ((3 mod 2 ^ 32) mod 64)) with 8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  rewrite (Z.mod_small (a mod 8)); [|lia]. rewrite (Z.mod_small (a mod 8 * 8) (2 ^ 64)); [|lia].
  rewrite (Z.mod_small (a mod 8 * 8) (2 ^ 32)); [|lia]. rewrite (Z.mod_small (a mod 8 * 8) 64); lia.
Qed.

(** Byte lane i of `[cshift] x c k` holds 128 when byte `i + k` of x
    stops the scan inside the word, and zero otherwise. *)
Lemma cshift_byte x c k i : 0 <= k < 8 -> 0 <= i < 8 ->
  byte_of (cshift x c k) i = if i + k <? 8 then (if hitb (c mod 256) (byte_of x (i + k)) then 128 else 0) else 0.
Proof.
  intros Hk Hi. unfold cshift. rewrite byte_of_div; [|lia|lia]. destruct (Z.ltb_spec (i + k) 8).
  - apply cmask_byte. lia.
  - apply byte_of_high; [apply cmask_range | lia].
Qed.

(** The shifted first-word mask `[cshift] x c k` always fits in 64 bits. *)
Lemma cshift_range x c k : 0 <= k -> 0 <= cshift x c k < 2 ^ 64.
Proof.
  intros Hk. unfold cshift. pose proof (cmask_range x c). assert (0 < 2 ^ (8 * k)) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (cmask x c)); [|lia]. apply Z.div_le_upper_bound; nia.
Qed.

(** When a 0/128 byte mask has its earliest 128 at lane j, the mask is
    nonzero and its [tail] bit count is `8 * j + 7`. *)
Lemma mask_tail m j : 0 <= m < 2 ^ 64 -> (forall i, 0 <= i < 8 -> byte_of m i = 0 \/ byte_of m i = 128) ->
  0 <= j < 8 -> byte_of m j = 128 -> (forall i, 0 <= i < j -> byte_of m i = 0) -> tail m = 8 * j + 7 /\ m <> 0.
Proof.
  intros Hr H01 Hj Hb Hl. split; [exact (tail_first m j Hr H01 Hj Hb Hl)|].
  intros E. rewrite E in Hb. unfold byte_of in Hb. rewrite Z.div_0_l in Hb; [discriminate | apply Z.pow_nonzero; lia].
Qed.

(** This functor packages the `strchrnul` and `strchr` specifications
    over a [[runtime]] R and a program logic instance LG0. *)
Module StrchrnulLogicOn (R : Runtime) (LG0 : LogicSig R).
(** Module [SL] supplies the step rules for symbolic execution. *)
Module SL := StrcmpLoopOn R LG0.
(** Module [WS] provides word-window and fractional read helpers. *)
Module WS := SL.WS.
(** Module [LG] re-exports the program logic instance. *)
Module LG := LG0.
(** Module [L] re-exports the core logic definitions. *)
Module L := LG.L.
Import L LG WS SL.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** To step through IR instructions in [[separation-logic|separation logic]],
    [rules_irisGS] connects the contract registry and world invariant `wi`
    to the Iris program logic. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** This shorthand names the expression type of the instantiated
    language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** Tactic [sl] advances one pure `let` instruction while keeping its
    result expression symbolic. *)
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** Tactic [sn] advances one `let` instruction and names its integer
    result in the context. *)
Ltac sn := eapply (s_letn registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |];
  let x := fresh "x" in let E := fresh "E" in intros x E.
(** Tactic [sf] advances one [[flight]] instruction in the proof mode. *)
Ltac sf := eapply (s_flight registry wi ge); [reflexivity | reflexivity | reflexivity |].
(** Tactic [en] steps into the target block and exposes its instructions
    and terminator. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** Tactic [sg] follows an unconditional `goto` and immediately enters the
    destination block. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** To resolve a temporary lookup below newer `put` bindings, [slk]
    rewrites the lookup using hypothesis H and steps one `let`. *)
Ltac slk n H := eapply (s_let registry wi ge); [reflexivity | reflexivity |
  cbn [map2_option value_x]; repeat (rewrite (lookup_after_put_other _ (TAtom n)); [|reflexivity]);
  rewrite H; reflexivity | intros ?; reflexivity |].
(** Tactic [sb] advances one conditional `branch` while keeping its
    condition expression symbolic. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** To keep intermediate integers readable, [normt] rewrites the
    integer in the newest temporary to `v` using tactic `tac`. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Tactic [normp] rewrites the address of the pointer stored in
    temporary `name` to `v` by arithmetic. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.

(** Tactic [unmod] strips 64-bit modulo wraps from mask and word
    expressions already known to fit in `[0, 2 ^ 64)`. *)
Ltac unmod :=
  repeat match goal with |- context [?y mod 2 ^ 64] =>
    rewrite (Z.mod_small y (2 ^ 64));
    [| first [apply loop_mask_range | apply lmask_range | apply cmask_range | apply first_mask_range
             | apply rep_range | apply lxor_range; first [apply rep_range | lia] | lia]] end.

(** To step through the 15-instruction population count on mask m, [pop]
    names each intermediate value, rewrites the final count using Htl,
    and enters the successor block. *)
Ltac pop m Htl :=
  en; do 15 sn;
  match goal with |- context [mkFrame _ (put _ (WInt ?t) _) _ _ _] =>
    let H := fresh in assert (H : t = tail m) by (eapply tail_chain; eassumption); rewrite H Htl; clear H end;
  repeat match goal with H : ?v = _ |- _ => is_var v; clear H end;
  sg.

(** Tactic [xrep] simplifies the IR computation of `x` XOR `[rep] c` into
    `Z.lxor x (rep c)` by dropping redundant modulo wraps. *)
Ltac xrep x := rewrite rep_mod; rewrite (Z.mod_small x);
  [first [reflexivity | rewrite Z.mod_small; [reflexivity | apply lxor_range; [lia | apply rep_range]]] | lia].

(** Block `L37` is the main word-scanning loop of [glibc_strchrnul]. *)
Definition blk37 : block := Eval vm_compute in
  match find_block (TAtom "L37") (fn_blocks glibc_strchrnul) with
  | Some b => b | None => mkBlock (TAtom "L37") [] [] JUnreachable end.
(** Entering `L37` at word index Q after no earlier byte stopped the
    scan, `nul_loop` steps word by word until it hits the stopping byte
    at offset t, returns `p + t`, and restores the window [wwin]. *)
Lemma nul_loop dq p b reg ws s c t Q A e Φ :
  str_shape p b reg ws s -> A = wstart p + 8 * Q - 8 -> 1 <= Q -> 8 * Q - ptr_addr p mod 8 <= Z.of_nat t -> (t <= List.length s)%nat ->
  hitb (c mod 256) (sbyte p ws (Z.of_nat t)) = true ->
  (forall j, 0 <= j < Z.of_nat t -> hitb (c mod 256) (sbyte p ws j) = false) ->
  lookup (TAtom "iw_1.v7") e = Some (WInt (rep c)) ->
  wwin dq b reg (wstart p - b) ws -∗
  (wwin dq b reg (wstart p - b) ws -∗ Φ (Ret (WPtr (ptr_add p (Z.of_nat t))))) -∗
  WP (ERun (mkFrame glibc_strchrnul (put (TAtom "pr.1") (WPtr (mkPtr A (ptr_cap p))) e) [] None
         (Exec (TAtom "L37") (b_insts blk37) (b_jump blk37))) : gexpr) {{ Φ }}.
Proof.
  intros Hs. destruct (shape_facts _ _ _ _ _ Hs) as (B1 & S1 & M1 & P1 & K1 & E1 & R1 & N1 & C1).
  pose proof (ss_words _ _ _ _ _ Hs) as F1.
  remember (Z.to_nat (Z.of_nat (List.length ws) - Q)) as n eqn:Hn.
  revert Q A e Hn. induction n as [|n IH]; intros Q A e Hn -> HQ Hc Ht Hat Hlow H7; [exfalso; lia|].
  iIntros "W HK". cbn [blk37 b_insts b_jump].
  sf. normp "v41" (wstart p + 8 * Q).
  iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq b reg (wstart p - b) ws Q with "W");
    [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W".
  set (x := wrd ws Q). pose proof (wrd_range ws Q F1) as X1.
  assert (Hb : forall u, 0 <= u < 8 -> byte_of x u = sbyte p ws (8 * Q - ptr_addr p mod 8 + u)).
  { intros u Hu. unfold x, sbyte. rewrite bt_word; [f_equal; lia | lia | lia]. }
  do 4 sl. normt (loop_mask x) ltac:(reflexivity).
  slk "iw_1.v7" H7. normt (Z.lxor x (rep c)) ltac:(unmod; reflexivity).
  do 4 sl. normt (loop_mask (Z.lxor x (rep c))) ltac:(reflexivity).
  sl. normt (lmask x c) ltac:(unmod; reflexivity).
  sl. sb. unmod.
  destruct (Z_lt_le_dec (ptr_addr p mod 8 + Z.of_nat t - 8 * Q) 8) as [Hin|Hout].
  - (* The stop is in this word, at j. *)
    pose (j := ptr_addr p mod 8 + Z.of_nat t - 8 * Q).
    assert (Hj : 0 <= j < 8) by (unfold j; lia).
    assert (Ej : 8 * Q - ptr_addr p mod 8 + j = Z.of_nat t) by (unfold j; lia). clearbody j.
    assert (Hlo : forall i, 0 <= i < j -> hitb (c mod 256) (byte_of x i) = false)
      by (intros i Hi; rewrite Hb; [apply Hlow; lia | lia]).
    destruct (mask_tail (lmask x c) j (lmask_range x c) (lmask_01 x c) ltac:(lia)
                (lmask_at x c j ltac:(lia) Hlo ltac:(rewrite Hb; [rewrite Ej; exact Hat | lia]))
                (fun i Hi => lmask_below x c j i ltac:(lia) Hlo Hi)) as [Htl Hnz].
    replace (lmask x c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). close_if.
    en. sb. replace (lmask x c =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). close_if.
    pop (lmask x c) Htl. sl. normt j ltac:(arith). sl. normt j ltac:(arith). sf.
    normp "v53" (ptr_addr p + Z.of_nat t).
    iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HK" with "W").
  - (* No stop in this word: the next. *)
    assert (Hz : lmask x c = 0).
    { apply zero_word; [apply lmask_range|]. intros i Hi. apply (lmask_below x c 8 i); [lia | | exact Hi].
      intros u Hu. rewrite Hb; [apply Hlow; lia | lia]. }
    rewrite Hz. close_if. en.
    iApply (IH (Q + 1) with "W HK"); [lia | cbn; lia | lia | lia | exact Ht | exact Hat | exact Hlow | look H7].
Qed.
(** Executing a call [[frame]] of [glibc_strchrnul] on a [word_string]
    at any share returns the pointer to the first stopping byte at
    [chr_idx] and restores the string. *)
Lemma wp_glibc_strchrnul_ws dq p s c Φ :
  0 <= c < 2 ^ 32 ->
  word_string dq p s -∗ (word_string dq p s -∗ Φ (Ret (WPtr (ptr_add p (Z.of_nat (chr_idx (c mod 256) s)))))) -∗
  WP (ERun (mkFrame glibc_strchrnul [(TAtom "v2", WInt c); (TAtom "v0", WPtr p)] [] None
              (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hc. iIntros "(%b & %reg & %ws & %Hs & W) HK".
  destruct (shape_facts _ _ _ _ _ Hs) as (B1 & S1 & M1 & P1 & K1 & E1 & R1 & N1 & C1).
  pose proof (ss_words _ _ _ _ _ Hs) as F1.
  en. sl. sl. sl. sf.
  match goal with |- context [put (TAtom "v12") (WPtr (mkPtr ?X _)) _] => replace X with (wstart p) by
    (unfold wstart; rewrite (Z.mod_small (ptr_addr p) (2 ^ 64)); [rewrite land_align; [arith | lia] | lia]) end.
  sl. sl. sl. normt (rep c) ltac:(symmetry; apply rep_ext; lia).
  iApply (wp_win_word registry wi ge _ _ _ _ _ _ _ _ _ _ dq b reg (wstart p - b) ws 0 with "W");
    [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia | exact F1 |]. iIntros "W".
  set (x := wrd ws 0). pose proof (wrd_range ws 0 F1) as X1.
  do 5 sl. normt (first_mask x) ltac:(reflexivity).
  sl. normt (Z.lxor x (rep c)) ltac:(xrep x).
  do 5 sl. normt (first_mask (Z.lxor x (rep c))) ltac:(reflexivity).
  sl. normt (cmask x c) ltac:(rewrite !Z.mod_small; [reflexivity | apply first_mask_range | apply first_mask_range]).
  do 3 sl. normt (cshift x c (ptr_addr p mod 8)) ltac:(unfold cshift; rewrite shift_amount; [rewrite (Z.mod_small (cmask x c)); [reflexivity | apply cmask_range] | lia]).
  sl. sb. rewrite (Z.mod_small (cshift _ _ _)); [|apply cshift_range; lia]. rewrite Zmod_0_l.
  destruct (shape_stop _ _ _ _ _ (c mod 256) Hs) as [Hat Hlow].
  pose proof (chr_idx_le (c mod 256) s) as Ht.
  remember (chr_idx (c mod 256) s) as t eqn:Et.
  set (k := ptr_addr p mod 8) in *.
  assert (Hb : forall u, 0 <= u < 8 -> byte_of x u = sbyte p ws (u - k)).
  { intros u Hu. unfold x, sbyte. rewrite (bt_word ws 0 u); [f_equal; lia | lia | lia]. }
  destruct (Z_lt_le_dec (Z.of_nat t) (8 - k)) as [Hin|Hout].
  - (* The stop is in the first word. *)
    set (m := cshift x c k).
    assert (Hmb : forall i, 0 <= i < 8 -> byte_of m i =
              if i + k <? 8 then (if hitb (c mod 256) (sbyte p ws i) then 128 else 0) else 0).
    { intros i Hi. unfold m. rewrite cshift_byte; [|lia|lia]. destruct (Z.ltb_spec (i + k) 8); [|reflexivity].
      rewrite Hb; [|lia]. replace (i + k - k) with i by lia. reflexivity. }
    assert (H01 : forall i, 0 <= i < 8 -> byte_of m i = 0 \/ byte_of m i = 128).
    { intros i Hi. rewrite Hmb; [|lia]. destruct (i + k <? 8), (hitb (c mod 256) (sbyte p ws i)); auto. }
    assert (Hm1 : byte_of m (Z.of_nat t) = 128).
    { rewrite Hmb; [|lia]. replace (Z.of_nat t + k <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite Hat. reflexivity. }
    assert (Hm0 : forall i, 0 <= i < Z.of_nat t -> byte_of m i = 0).
    { intros i Hi. rewrite Hmb; [|lia]. replace (i + k <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite Hlow; [reflexivity | lia]. }
    destruct (mask_tail m (Z.of_nat t) ltac:(apply cshift_range; lia) H01 ltac:(lia) Hm1 Hm0) as [Htl Hnz].
    replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). close_if.
    en. sl. sb. rewrite (Z.mod_small m); [|apply cshift_range; lia]. rewrite Zmod_0_l.
    replace (m =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hnz). close_if.
    pop m Htl. sl. normt (Z.of_nat t) ltac:(arith). sl. normt (Z.of_nat t) ltac:(arith). sf.
    normp "v35" (ptr_addr p + Z.of_nat t).
    iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply "HK". iExists b, reg, ws. by iFrame.
  - (* No stop in the first word: the loop. *)
    assert (Hz : cshift x c k = 0).
    { apply zero_word; [apply cshift_range; lia|]. intros i Hi. rewrite cshift_byte; [|lia|lia].
      destruct (Z.ltb_spec (i + k) 8); [|reflexivity]. rewrite Hb; [|lia]. rewrite Hlow; [reflexivity | lia]. }
    rewrite Hz. close_if. en.
    iApply (nul_loop dq p b reg ws s c t 1 with "W [HK]"); [exact Hs | cbn; lia | lia | lia | exact Ht | exact Hat | exact Hlow | reflexivity |].
    iIntros "W". iApply "HK". iExists b, reg, ws. by iFrame.
Qed.

(** Calling a global function g bound to [glibc_strchrnul] on a
    [word_string] at any share resumes the caller with the pointer to
    the first `c mod 256` or to NUL, and restores the string. *)
Lemma wp_call_glibc_strchrnul f e ls l r g args rest j dq p s c cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr p; WInt c] -> 0 <= c < 2 ^ 32 ->
  find_fn ge g = Some (Defined glibc_strchrnul) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None)
    (Ret (WPtr (ptr_add p (Z.of_nat (chr_idx (c mod 256) s))))) = Some cf' ->
  word_string dq p s -∗ ▷ (word_string dq p s -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hc Hg Hr. iIntros "Hs HK".
  iApply (wp_call_bind with "[Hs HK]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_strchrnul_ws with "Hs"); [exact Hc |].
  iIntros "Hs". iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hs").
Qed.

(** After `c: strchrnul` returns, `c: strchr` loads the byte at that
    pointer to check whether it matched `c`. Lemma [wp_win_ubyte]
    verifies that 1-byte read [[check]] and loads the unsigned byte from
    a shared window [wwin]. *)
Lemma wp_win_ubyte f e ls l c d pr rest j p dq b reg wo ws i Φ :
  map2_option (value_x ge e) [P] [Tmp pr] = Some [WPtr p] -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  ptr_addr p = b + wo + i -> 0 <= i < 8 * Z.of_nat (List.length ws) -> 0 < b -> 0 <= wo ->
  b + wo + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  wwin dq b reg wo ws -∗
  (wwin dq b reg wo ws -∗
   WP (ERun (mkFrame f (put d (WInt (bt ws i)) (put c (WPtr p) e)) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let c A (Check 0 1 Read 1) [Tmp pr] ::
                                         Let d W (RawLoad (LdNarrow Ub) 0) [Tmp c] :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hc Ha Hi Hb Hwo Hend Hreg. iIntros "[Hl Hw] HK".
  iApply (wp_check_read_dq with "Hl"); [reflexivity | exact Hx | exact Hc | arith | arith | apply Z.mod_1_r |].
  iNext. iIntros "Hl".
  iApply (wp_read_with registry wi ge (liveq dq b reg ∗ ptsq dq (words_ps b wo ws))%I
            (fun m => live_at m b reg /\ all_agree m (words_ps b wo ws)) _ _ [] with "[$Hl $Hw] [HK]").
  - iIntros (σ) "Hσ [Hl Hw]". iDestruct (ptsq_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (ptsq_facts with "Hσ Hw") as %(Hag & _). iPureIntro. auto.
  - intros m fuel [Hlv Hag].
    pose proof (words_ps_elem b wo ws (Z.to_nat i) _ (wbytes_bt ws i Hi)) as Hin.
    apply (all_agree_elem _ _ _ _ Hag) in Hin as [_ Hin]. rewrite Z2Nat.id in Hin; [|lia].
    destruct Hlv as [E Lv]. destruct (Hin reg E Lv) as (_ & _ & Hv).
    apply rule_let with (classes := [A]) (xs := [WPtr p]); [reflexivity | reflexivity | |].
    { cbn [map2_option value_x]. rewrite lookup_after_put_same. reflexivity. }
    assert (Er : raw_address (ptr_addr p) 0 = b + (wo + i)) by arith.
    rewrite (op_raw_load_byte m W Ub p 0 eq_refl).
    + rewrite Er Hv. pose proof (byte_of_range (wrd ws (i / 8)) (i mod 8)).
      unfold extended, bt. cbn [modulus extension option_map]. rewrite !(Z.mod_small (byte_of _ _)); [reflexivity | lia | lia].
    + rewrite Er. apply (access_read _ b reg); [exact Hc | exact E | lia | lia | apply Z.mod_1_r].
  - iNext. iIntros "[Hl Hw]". iApply ("HK" with "[$Hl $Hw]").
Qed.

(** Executing a call [[frame]] of [glibc_strchr] on a [word_string] at
    any share returns the [strchr_ptr] result and restores the
    string. *)
Lemma wp_glibc_strchr_ws dq p s c Φ :
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) -> 0 <= c < 2 ^ 32 ->
  word_string dq p s -∗ (word_string dq p s -∗ Φ (Ret (WPtr (strchr_ptr p (c mod 256) s)))) -∗
  WP (ERun (mkFrame glibc_strchr [(TAtom "v2", WInt c); (TAtom "v0", WPtr p)] [] None
              (Enter (TAtom "start") None)) : gexpr) {{ Φ }}.
Proof.
  intros Hg Hc. iIntros "Hs HK".
  en. iApply (wp_call_glibc_strchrnul with "Hs");
    [cbn; rewrite (Z.mod_small c); [reflexivity | lia] | exact Hc | exact Hg | reflexivity |].
  iNext. iIntros "(%b & %reg & %ws & %Hs & W)". cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  destruct (shape_facts _ _ _ _ _ Hs) as (B1 & S1 & M1 & P1 & K1 & E1 & R1 & N1 & C1).
  pose proof (chr_idx_le (c mod 256) s) as Ht. pose proof (sbyte_agree _ _ _ _ _ Hs) as Ag.
  iApply (wp_win_ubyte _ _ _ _ _ _ _ _ _ _ dq b reg (wstart p - b) ws (ptr_addr p mod 8 + Z.of_nat (chr_idx (c mod 256) s))
            with "W"); [reflexivity | exact C1 | cbn; lia | lia | lia | lia | lia | lia |]. iIntros "W".
  sl. sl. sb.
  assert (Ey : bt ws (ptr_addr p mod 8 + Z.of_nat (chr_idx (c mod 256) s)) = nth (chr_idx (c mod 256) s) (s ++ [0]) 0).
  { change (bt ws (ptr_addr p mod 8 + Z.of_nat (chr_idx (c mod 256) s))) with (sbyte p ws (Z.of_nat (chr_idx (c mod 256) s))).
    rewrite Ag; [|lia]. rewrite Nat2Z.id. reflexivity. }
  rewrite Ey. pose proof (nth_byte_range (chr_idx (c mod 256) s) s (ss_chars _ _ _ _ _ Hs)) as Yr.
  replace (extension Ub (c mod 2 ^ 32) mod 2 ^ 32) with (c mod 256)
    by (cbn [extension]; rewrite (Z.mod_small c (2 ^ 32)); [|lia]; pose proof (Z.mod_pos_bound c 256 ltac:(lia));
        rewrite (Z.mod_small (c mod 256) (2 ^ 32)); lia).
  rewrite (Z.mod_small (nth _ _ _) (2 ^ 32)); [|lia]. pose proof (Z.mod_pos_bound c 256 ltac:(lia)).
  rewrite (Z.mod_small (c mod 256) (2 ^ 32)); [|lia].
  unfold strchr_ptr. rewrite (strchr_hit (c mod 256) s ltac:(lia) (ss_chars _ _ _ _ _ Hs)).
  destruct (Z.eqb_spec (nth (chr_idx (c mod 256) s) (s ++ [0]) 0) (c mod 256)); close_if.
  - en. iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply "HK". iExists b, reg, ws. by iFrame.
  - en. sg. iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply "HK". iExists b, reg, ws. by iFrame.
Qed.

(** When a caller invokes `c: strchr` in a module that links
    `__GI___strchrnul` to [glibc_strchrnul], [wp_call_glibc_strchr]
    resumes the caller with the matching byte pointer or null and
    restores the string. *)
Lemma wp_call_glibc_strchr f e ls l r g args rest j dq p s c cf' Φ :
  map_option (arg_x ge e) args = Some [WPtr p; WInt c] -> 0 <= c < 2 ^ 32 ->
  find_fn ge g = Some (Defined glibc_strchr) ->
  find_fn ge (TAtom "__GI___strchrnul") = Some (Defined glibc_strchrnul) ->
  resume (mkFrame f e ls None (Exec l rest j)) (mkPending r None) (Ret (WPtr (strchr_ptr p (c mod 256) s))) = Some cf' ->
  word_string dq p s -∗ ▷ (word_string dq p s -∗ WP (ERun cf' : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Call r (Global g) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hx Hc Hg Hn Hr. iIntros "Hs HK".
  iApply (wp_call_bind with "[Hs HK]"); [exact Hx | exact Hg | reflexivity |]. iNext.
  iApply (wp_glibc_strchr_ws with "Hs"); [exact Hn | exact Hc |].
  iIntros "Hs". iExists cf'. iSplit; [done|]. iNext. iApply ("HK" with "Hs").
Qed.

End rules.
End StrchrnulLogicOn.
