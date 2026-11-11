(** glibc's own `__strchrnul` (StrchrCode.v's [glibc_strchrnul]) over a
    [word_string] (WordString.v) at any share: [wp_glibc_strchrnul_ws]
    for a frame of it and [wp_call_glibc_strchrnul] for a call. It
    returns the pointer to the first byte of the string that is c mod
    256, or to its NUL: [chr_idx] bytes in.

    glibc's strchrnul reads whole words from the one holding p's byte.
    On the first it marks each byte that is 0 or c's with string-fza.h's
    exact `find_zero_all` of the word and of the word xor'd with c's byte
    in each byte (StrlenBits.v's [first_mask], MemchrLast.v's [rep]),
    shifted past the bytes before p ([cmask]); on the others it uses the
    cheaper `find_zero_low` of both ([lmask]), exact up to the first
    stop. The population count of either ([tail]) is the stop's index.
    The steps are StrcmpLoop.v's, over the proof mode's entailment, and
    every read is a word of the string's window ([wp_win_word]). *)

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

(** ## Where strchrnul stops *)

(** The byte x stops strchrnul for the byte cc: it is a NUL or cc. *)
Definition hitb (cc x : Z) : bool := (x =? 0) || (x =? cc).

(** The index of the first byte cc of the string s, or its length. *)
Fixpoint chr_idx (cc : Z) (s : list Z) : nat :=
  match s with [] => O | x :: s' => if x =? cc then O else S (chr_idx cc s') end.

(** The first stop is at most the string's length. *)
Lemma chr_idx_le cc s : (chr_idx cc s <= List.length s)%nat.
Proof. induction s as [|x s IH]; cbn [chr_idx List.length]; [lia|]. destruct (x =? cc); lia. Qed.

(** The byte at [chr_idx], of the string and its NUL, is a stop. *)
Lemma chr_idx_at cc s : hitb cc (nth (chr_idx cc s) (s ++ [0]) 0) = true.
Proof.
  induction s as [|x s IH]; cbn [chr_idx]; [reflexivity|].
  destruct (Z.eqb_spec x cc) as [->|]; [|exact IH]. cbn. unfold hitb. rewrite Z.eqb_refl orb_true_r. reflexivity.
Qed.

(** The bytes before [chr_idx] of a string of nonzero bytes are no stops. *)
Lemma chr_idx_below cc s j : Forall (fun x => 0 < x < 256) s -> (j < chr_idx cc s)%nat ->
  hitb cc (nth j (s ++ [0]) 0) = false.
Proof.
  revert j. induction s as [|x s IH]; intros j Hs Hj; cbn [chr_idx] in Hj; [lia|].
  apply Forall_cons_1 in Hs as [Hx Hs]. destruct (Z.eqb_spec x cc) as [->|Hne]; [lia|].
  destruct j as [|j]; cbn [app nth].
  - unfold hitb. apply orb_false_iff. split; apply Z.eqb_neq; lia.
  - apply IH; [exact Hs | lia].
Qed.

(** The string's bytes from p: its stop for cc is at [chr_idx], and
    none before. *)
Lemma shape_stop p b reg ws s cc : str_shape p b reg ws s ->
  hitb cc (sbyte p ws (Z.of_nat (chr_idx cc s))) = true /\
  forall j, 0 <= j < Z.of_nat (chr_idx cc s) -> hitb cc (sbyte p ws j) = false.
Proof.
  intros Hs. pose proof (sbyte_agree _ _ _ _ _ Hs) as A. pose proof (chr_idx_le cc s) as Hl. split.
  - rewrite A; [|lia]. rewrite Nat2Z.id. apply chr_idx_at.
  - intros j Hj. rewrite A; [|lia]. apply chr_idx_below; [exact (ss_chars _ _ _ _ _ Hs) | lia].
Qed.

(** strchr's answer for the byte cc of a string at p: the pointer to
    its first cc, or to its NUL when cc is 0, else null. *)
Definition strchr_ptr (p : ptr) (cc : Z) (s : list Z) : ptr :=
  if (chr_idx cc s <? List.length s)%nat || (cc =? 0) then ptr_add p (Z.of_nat (chr_idx cc s)) else mkPtr 0 CNone.

(** The byte at [chr_idx] of a string and its NUL is a byte. *)
Lemma nth_byte_range n s : Forall (fun x => 0 < x < 256) s -> 0 <= nth n (s ++ [0]) 0 < 256.
Proof.
  intros Hs. destruct (Nat.lt_ge_cases n (List.length s)) as [H|H].
  - rewrite app_nth1; [|exact H]. rewrite Forall_forall in Hs. pose proof (Hs _ (proj2 (list_elem_of_In _ _) (nth_In s 0 H))). lia.
  - rewrite app_nth2; [|exact H]. destruct (n - List.length s)%nat as [|[|]]; cbn; lia.
Qed.

(** strchr finds c's byte cc just when the byte at [chr_idx] is cc. *)
Lemma strchr_hit cc s : 0 <= cc < 256 -> Forall (fun x => 0 < x < 256) s ->
  ((chr_idx cc s <? List.length s)%nat || (cc =? 0)) = (nth (chr_idx cc s) (s ++ [0]) 0 =? cc).
Proof.
  intros Hcc Hs. induction s as [|x s IH]; cbn [chr_idx List.length].
  - destruct cc; cbn; reflexivity || lia.
  - apply Forall_cons_1 in Hs as [Hx Hs]. destruct (Z.eqb_spec x cc) as [->|Hne].
    + cbn. rewrite Z.eqb_refl. reflexivity.
    + cbn [app nth]. rewrite (IH Hs). reflexivity.
Qed.

(** ## The masks *)

(** A xor of 64-bit words is a 64-bit word. *)
Lemma lxor_range a b : 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lxor a b < 2 ^ 64.
Proof.
  intros Ha Hb. assert (E : Z.lxor a b mod 2 ^ 64 = Z.lxor a b).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.testbit_mod_pow2; [|lia]. rewrite Z.lxor_spec.
    destruct (n <? 64) eqn:E; [reflexivity|]. apply Z.ltb_ge in E.
    rewrite (bits64 a n Ha E) (bits64 b n Hb E). reflexivity. }
  rewrite -E. apply Z.mod_pos_bound. lia.
Qed.

(** The first word's mask is a 64-bit word. *)
Lemma first_mask_range x : 0 <= first_mask x < 2 ^ 64.
Proof. unfold first_mask. apply lxor_range; [apply Z.mod_pos_bound; lia | vm_compute; split; congruence]. Qed.

(** strchrnul's first mask of the word x for c: 128 in each byte that
    is 0 or c's ([cmask_byte]). *)
Definition cmask (x c : Z) : Z := Z.lor (first_mask x) (first_mask (Z.lxor x (rep c))).

(** The loop's mask of the word x for c: exact up to its first stop. *)
Definition lmask (x c : Z) : Z := Z.lor (loop_mask x) (loop_mask (Z.lxor x (rep c))).

(** A byte of x xor [rep] c is not zero where x's byte is no c. *)
Lemma xor_nonzero x c i : 0 <= i < 8 -> hitb (c mod 256) (byte_of x i) = false ->
  byte_of x i <> 0 /\ byte_of (Z.lxor x (rep c)) i <> 0.
Proof.
  intros Hi H. unfold hitb in H. apply orb_false_iff in H as [H1 H2]. apply Z.eqb_neq in H1, H2.
  split; [exact H1|]. intros E. apply H2. apply xor_zero; [exact Hi | exact E].
Qed.

(** Byte i of [cmask]: 128 where x's byte is a stop. *)
Lemma cmask_byte x c i : 0 <= i < 8 -> byte_of (cmask x c) i = if hitb (c mod 256) (byte_of x i) then 128 else 0.
Proof.
  intros Hi. unfold cmask, hitb. rewrite byte_of_lor; [|lia]. rewrite !first_mask_byte; [|lia|lia].
  destruct (Z.eqb_spec (byte_of (Z.lxor x (rep c)) i) 0) as [E|E].
  - apply xor_zero in E; [|lia]. rewrite E Z.eqb_refl orb_true_r. destruct (_ =? 0); reflexivity.
  - replace (byte_of x i =? c mod 256) with false; [rewrite orb_false_r; destruct (_ =? 0); reflexivity|].
    symmetry. apply Z.eqb_neq. intros E'. apply E. apply xor_zero; [lia | exact E'].
Qed.

(** [rep] c is a 64-bit word. *)
Lemma rep_range c : 0 <= rep c < 2 ^ 64.
Proof. unfold rep. apply Z.mod_pos_bound. lia. Qed.

(** [cmask] is a 64-bit word. *)
Lemma cmask_range x c : 0 <= cmask x c < 2 ^ 64.
Proof. apply lor_range; apply first_mask_range. Qed.

(** [lmask] is a 64-bit word. *)
Lemma lmask_range x c : 0 <= lmask x c < 2 ^ 64.
Proof. apply lor_range; apply loop_mask_range. Qed.

(** The bytes of [lmask] are 0 or 128. *)
Lemma lmask_01 x c i : 0 <= i < 8 -> byte_of (lmask x c) i = 0 \/ byte_of (lmask x c) i = 128.
Proof.
  intros Hi. unfold lmask. rewrite byte_of_lor; [|lia].
  destruct (loop_mask_01 x i Hi) as [-> | ->], (loop_mask_01 (Z.lxor x (rep c)) i Hi) as [-> | ->]; cbn; auto.
Qed.

(** Below the word's first stop j, [lmask]'s bytes are 0. *)
Lemma lmask_below x c j i : j <= 8 -> (forall i, 0 <= i < j -> hitb (c mod 256) (byte_of x i) = false) ->
  0 <= i < j -> byte_of (lmask x c) i = 0.
Proof.
  intros Hj Hn Hi. unfold lmask. rewrite byte_of_lor; [|lia].
  rewrite (loop_mask_below x j i Hj); [|intros k Hk; apply (xor_nonzero x c k); [lia | apply Hn; lia] | lia].
  rewrite (loop_mask_below (Z.lxor x (rep c)) j i Hj); [reflexivity| |lia].
  intros k Hk. apply (xor_nonzero x c k); [lia | apply Hn; lia].
Qed.

(** At the word's first stop j, [lmask]'s byte is 128. *)
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

(** [cmask] shifted down past the k bytes of the word before the
    string, as glibc's `shift_find` (string-fza.h) does. *)
Definition cshift (x c k : Z) : Z := cmask x c / 2 ^ (8 * k).

(** The shift of the IR, from the address a: 8 times a's offset in its word. *)
Lemma shift_amount a : 0 <= a < 2 ^ 64 ->
  ((Z.land (a mod 2 ^ 64) (7 mod 2 ^ 64) mod 2 ^ 64 * 2 ^ ((3 mod 2 ^ 32) mod 64)) mod 2 ^ 64) mod 2 ^ 32 mod 64
  = 8 * (a mod 8).
Proof.
  intros Ha. rewrite (Z.mod_small a); [|lia]. change (7 mod 2 ^ 64) with (Z.ones 3). rewrite Z.land_ones; [|lia].
  change (2 ^ 3) with 8. change (2 ^ ((3 mod 2 ^ 32) mod 64)) with 8. pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  rewrite (Z.mod_small (a mod 8)); [|lia]. rewrite (Z.mod_small (a mod 8 * 8) (2 ^ 64)); [|lia].
  rewrite (Z.mod_small (a mod 8 * 8) (2 ^ 32)); [|lia]. rewrite (Z.mod_small (a mod 8 * 8) 64); lia.
Qed.

(** Byte i of [cshift]: [cmask]'s byte i + k inside the word, else 0. *)
Lemma cshift_byte x c k i : 0 <= k < 8 -> 0 <= i < 8 ->
  byte_of (cshift x c k) i = if i + k <? 8 then (if hitb (c mod 256) (byte_of x (i + k)) then 128 else 0) else 0.
Proof.
  intros Hk Hi. unfold cshift. rewrite byte_of_div; [|lia|lia]. destruct (Z.ltb_spec (i + k) 8).
  - apply cmask_byte. lia.
  - apply byte_of_high; [apply cmask_range | lia].
Qed.

(** [cshift] is a 64-bit word. *)
Lemma cshift_range x c k : 0 <= k -> 0 <= cshift x c k < 2 ^ 64.
Proof.
  intros Hk. unfold cshift. pose proof (cmask_range x c). assert (0 < 2 ^ (8 * k)) by (apply Z.pow_pos_nonneg; lia).
  split; [apply Z.div_pos; lia|]. apply (Z.le_lt_trans _ (cmask x c)); [|lia]. apply Z.div_le_upper_bound; nia.
Qed.

(** A mask whose bytes are 0 or 128, 128 first at j: its population
    count is 8j + 7, and it is not 0. *)
Lemma mask_tail m j : 0 <= m < 2 ^ 64 -> (forall i, 0 <= i < 8 -> byte_of m i = 0 \/ byte_of m i = 128) ->
  0 <= j < 8 -> byte_of m j = 128 -> (forall i, 0 <= i < j -> byte_of m i = 0) -> tail m = 8 * j + 7 /\ m <> 0.
Proof.
  intros Hr H01 Hj Hb Hl. split; [exact (tail_first m j Hr H01 Hj Hb Hl)|].
  intros E. rewrite E in Hb. unfold byte_of in Hb. rewrite Z.div_0_l in Hb; [discriminate | apply Z.pow_nonzero; lia].
Qed.

(** The triples over the [[runtime]] R and the Logic instance LG0. *)
Module StrchrnulLogicOn (R : Runtime) (LG0 : LogicSig R).
(** StrcmpLoop.v's steps and reads over R and LG0. *)
Module SL := StrcmpLoopOn R LG0.
(** Strings' windows. *)
Module WS := SL.WS.
(** The Logic instance. *)
Module LG := LG0.
(** Its language. *)
Module L := LG.L.
Import L LG WS SL.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** StrcmpLoop.v's steps: a let, its value whole. *)
Ltac sl := eapply (s_let registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |].
(** A let, its integer named. *)
Ltac sn := eapply (s_letn registry wi ge); [reflexivity | reflexivity | reflexivity | intros ?; reflexivity |];
  let x := fresh "x" in let E := fresh "E" in intros x E.
(** A flight. *)
Ltac sf := eapply (s_flight registry wi ge); [reflexivity | reflexivity | reflexivity |].
(** Entering the block a frame is entering. *)
Ltac en := eapply (s_enter registry wi ge); [reflexivity | reflexivity |]; cbn [b_insts b_jump].
(** A goto and the block it enters. *)
Ltac sg := eapply (s_goto registry wi ge); en.
(** A let that reads the temporary n below the puts, which H gives. *)
Ltac slk n H := eapply (s_let registry wi ge); [reflexivity | reflexivity |
  cbn [map2_option value_x]; repeat (rewrite (lookup_after_put_other _ (TAtom n)); [|reflexivity]);
  rewrite H; reflexivity | intros ?; reflexivity |].
(** A branch, its condition left whole. *)
Ltac sb := eapply (s_branch registry wi ge); [reflexivity|].
(** Replace the integer the newest temporary holds by v, proved by tac. *)
Ltac normt v tac :=
  match goal with |- context [mkFrame _ (put _ (WInt ?X) _) _ _ _] => replace X with v by tac end.
(** Replace the address of the pointer the temporary name holds by v. *)
Ltac normp name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by arith end.

(** Drop each wrap to 64 bits of a word known to be one. *)
Ltac unmod :=
  repeat match goal with |- context [?y mod 2 ^ 64] =>
    rewrite (Z.mod_small y (2 ^ 64));
    [| first [apply loop_mask_range | apply lmask_range | apply cmask_range | apply first_mask_range
             | apply rep_range | apply lxor_range; first [apply rep_range | lia] | lia]] end.

(** From the first block of a population count of the mask m, whose
    count Htl says is 8j + 7: the count's steps, to the block after. *)
Ltac pop m Htl :=
  en; do 15 sn;
  match goal with |- context [mkFrame _ (put _ (WInt ?t) _) _ _ _] =>
    let H := fresh in assert (H : t = tail m) by (eapply tail_chain; eassumption); rewrite H Htl; clear H end;
  repeat match goal with H : ?v = _ |- _ => is_var v; clear H end;
  sg.

(** The word x xor [rep] c, as the IR computes it, is [Z.lxor] x (rep c). *)
Ltac xrep x := rewrite rep_mod; rewrite (Z.mod_small x);
  [first [reflexivity | rewrite Z.mod_small; [reflexivity | apply lxor_range; [lia | apply rep_range]]] | lia].

(** The loop's block. *)
Definition blk37 : block := Eval vm_compute in
  match find_block (TAtom "L37") (fn_blocks glibc_strchrnul) with
  | Some b => b | None => mkBlock (TAtom "L37") [] [] JUnreachable end.

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

(** A call of glibc's strchrnul, in any module whose function at the
    called name g is glibc's `__strchrnul`, on a string at any share:
    the caller resumes with the pointer to the first c mod 256, or to
    the NUL, and the string. *)
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

(** A [[check]] of one byte for reading of the pointer pr holds, p, and
    a load of the unsigned byte there, where p addresses byte i of a
    window at a share: the load gives the byte. *)
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

(** glibc's strchr of the string s at p for c: the pointer to the first
    c mod 256 of s, or to its NUL when c mod 256 is 0, else null. *)
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

(** A call of glibc's strchr, in any module whose function at the
    called name g is glibc's `__GI_strchr` and at `__GI___strchrnul`
    glibc's strchrnul, on a string at any share. *)
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
