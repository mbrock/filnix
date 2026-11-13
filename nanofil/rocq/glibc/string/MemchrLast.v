(** In C, `c: memchr(p, c, n)` searches at most n bytes starting at p for
    the first byte equal to `c mod 256` and returns a pointer to it, or
    null if none matches. Glibc's `__memchr` reads 8-byte [[word|words]]
    at a time, XORs each word with a word filled with the target byte,
    marks any resulting zero bytes, and counts trailing bits to find the
    first match.

    This module sets up the byte-search specification [loop_hit] and
    proves [memchr_last] for the final word of the search range, where a
    match counts only if it falls at or before the end address E.
    [MemchrLoop] uses [memchr_last] as the base case for the main word
    loop, and [MemchrFirst] and [MemchrLogic] handle the entry block and
    first partial word. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  StepRules Symbolic ExternalCalls Pieces Heap Language Logic.
From Glibc Require Import StrlenBits StrlenLogic WordString StrlenLoop StrchrCode.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Bytes equal to c

    To test eight bytes in parallel for equality with a target byte c,
    glibc broadcasts the low byte of c across all eight lanes of a
    64-bit word and XORs the input word against it. A byte in the
    resulting word is zero if and only if the original byte matched c,
    which reduces byte equality to zero-byte detection. *)

(** Function [rep] broadcasts the low byte of c into every byte lane of a
    64-bit word. *)
Definition rep (c : Z) : Z := (c mod 256 * lows) mod 2 ^ 64.

(** Every byte lane i of `[rep] c` equals `c mod 256`. *)
Lemma rep_byte c i : 0 <= i < 8 -> byte_of (rep c) i = c mod 256.
Proof.
  intros Hi. unfold rep. pose proof (Z.mod_pos_bound c 256 ltac:(lia)) as Hc.
  set (d := c mod 256) in *. clearbody d.
  pose proof (all_bytes (fun d => forallb (fun i => byte_of ((d * lows) mod 2 ^ 64) i =? d) idx8)
    ltac:(vm_compute; reflexivity) d Hc) as H.
  rewrite forallb_forall in H. specialize (H i (idx8_cases i Hi)). apply Z.eqb_eq in H. exact H.
Qed.

(** Byte i of `x` XOR `[rep] c` is zero if and only if byte i of `x`
    equals `c mod 256`. *)
Lemma xor_zero x c i : 0 <= i < 8 -> byte_of (Z.lxor x (rep c)) i = 0 <-> byte_of x i = c mod 256.
Proof. intros Hi. rewrite byte_of_lxor; [|lia]. rewrite rep_byte; [|lia]. apply Z.lxor_eq_0_iff. Qed.

(** Predicate [first_byte] holds when index n is the earliest position
    in byte list bs that equals c. *)
Definition first_byte (c : Z) (bs : list Z) (n : nat) : Prop :=
  bs !! n = Some c /\ forall u, (u < n)%nat -> bs !! u <> Some c.

(** Every decidable predicate on indices below n either has a least
    witness j or fails everywhere below n. *)
Lemma least_below (P : nat -> Prop) (dec : forall i, {P i} + {~ P i}) n :
  (exists j, (j < n)%nat /\ P j /\ forall i, (i < j)%nat -> ~ P i) \/ (forall i, (i < n)%nat -> ~ P i).
Proof.
  induction n as [|n IH]; [right; lia|].
  destruct IH as [(j & Hj & Hp & Hl) | Hn]; [left; exists j; split; [lia | auto]|].
  destruct (dec n) as [Hp|Hp]; [left; exists n; auto | right; intros i Hi].
  destruct (Nat.eq_dec i n) as [->|]; [exact Hp | apply Hn; lia].
Qed.

(** An 8-byte word w either contains byte c first at some lane j or
    contains no byte equal to c. *)
Lemma word_first w c :
  (exists j, 0 <= j < 8 /\ byte_of w j = c /\ forall i, 0 <= i < j -> byte_of w i <> c) \/
  (forall i, 0 <= i < 8 -> byte_of w i <> c).
Proof.
  destruct (least_below (fun i => byte_of w (Z.of_nat i) = c) (fun i => Z.eq_dec _ _) 8)
    as [(j & Hj & Hp & Hl) | Hn].
  - left. exists (Z.of_nat j). split; [lia|]. split; [exact Hp|]. intros i Hi.
    specialize (Hl (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hl; [exact Hl | lia].
  - right. intros i Hi. specialize (Hn (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hn; [exact Hn | lia].
Qed.

(** When no byte of word w equals `c mod 256`, [loop_mask] produces zero
    for the XORed word. *)
Lemma mask_none w c : (forall i, 0 <= i < 8 -> byte_of w i <> c mod 256) -> loop_mask (Z.lxor w (rep c)) = 0.
Proof.
  intros Hn. apply zero_word; [apply loop_mask_range|]. intros i Hi.
  apply (loop_mask_below _ 8 i); [lia | | lia]. intros k Hk E. apply (Hn k Hk). apply xor_zero; [lia | exact E].
Qed.

(** To locate the first matching byte in word w, glibc counts trailing
    zero bits in the loop mask; when lane j is the earliest match for
    `c mod 256`, the mask is nonzero and [tail] returns `8 * j + 7`. *)
Lemma mask_first w c j : 0 <= j < 8 -> byte_of w j = c mod 256 ->
  (forall i, 0 <= i < j -> byte_of w i <> c mod 256) ->
  loop_mask (Z.lxor w (rep c)) <> 0 /\ tail (loop_mask (Z.lxor w (rep c))) = 8 * j + 7.
Proof.
  intros Hj Hc Hl. set (x := Z.lxor w (rep c)).
  assert (Hlow : forall i, 0 <= i < j -> byte_of x i <> 0).
  { intros i Hi E. apply (Hl i Hi). apply xor_zero; [lia | exact E]. }
  assert (Hb : byte_of (loop_mask x) j = 128) by (apply loop_mask_at; [lia | exact Hlow | apply xor_zero; [lia | exact Hc]]).
  split.
  - intros E. rewrite E in Hb. unfold byte_of in Hb. rewrite Z.div_0_l in Hb; [discriminate | apply Z.pow_nonzero; lia].
  - apply tail_first; [apply loop_mask_range | apply loop_mask_01 | lia | exact Hb |].
    intros i Hi. apply (loop_mask_below x j i); [lia | exact Hlow | exact Hi].
Qed.

(** Reducing `[rep] c` modulo `2 ^ 64` leaves it unchanged because it
    already fits in 64 bits. *)
Lemma rep_mod c : rep c mod 2 ^ 64 = rep c.
Proof. unfold rep. apply Z.mod_mod. lia. Qed.

(** ## The loop's outcome

    A call to `c: memchr` stops either at the first matching byte or at
    the end address E, whichever comes first. We specify that outcome
    with [loop_hit] on the byte list `bs`, then prove lemmas that peel
    off the unaligned first word, intermediate full words, and the final
    word containing E. *)

(** Predicate [loop_hit] relates a search from address A up to end
    address E over bytes bs to outcome r: either `Some t` at the first
    match within E, or `None` when no byte up to E matches. *)
Definition loop_hit (bs : list Z) (c A E : Z) (r : option nat) : Prop :=
  match r with
  | Some t => A + Z.of_nat t <= E /\ first_byte c bs t
  | None => E - A + 1 <= Z.of_nat (List.length bs) /\ forall u : nat, A + Z.of_nat u <= E -> bs !! u <> Some c
  end.

(** Function [hit_ptr] converts an optional byte offset r into the C
    pointer returned by `c: memchr`, advancing q by r or returning null. *)
Definition hit_ptr (q : ptr) (r : option nat) : ptr :=
  match r with Some t => mkPtr (ptr_addr q + Z.of_nat t) (ptr_cap q) | None => mkPtr 0 CNone end.

(** For any word w strictly before the final word, a match inside w
    determines the whole search outcome, and otherwise the search
    advances to `A + 8` with the remaining words `ws`. *)
Lemma hit_word w ws c A E r : A + 8 <= E -> loop_hit (wbytes (w :: ws)) c A E r ->
  (exists j, 0 <= j < 8 /\ r = Some (Z.to_nat j) /\ byte_of w j = c /\ forall i, 0 <= i < j -> byte_of w i <> c) \/
  ((forall i, 0 <= i < 8 -> byte_of w i <> c) /\ ws <> [] /\ (forall t, r = Some t -> (8 <= t)%nat) /\
   loop_hit (wbytes ws) c (A + 8) E (option_map (fun t => t - 8)%nat r)).
Proof.
  intros HE Hr. destruct (word_first w c) as [(j & Hj & Hc & Hl) | Hn].
  - left. exists j. split; [exact Hj|]. split; [|auto].
    assert (Hb : wbytes (w :: ws) !! Z.to_nat j = Some c) by (rewrite wbytes_head; [|lia]; rewrite Z2Nat.id; [congruence | lia]).
    destruct r as [t|]; cbn [loop_hit] in Hr.
    + destruct Hr as (_ & Ht & Hlt). f_equal. destruct (Nat.lt_total t (Z.to_nat j)) as [H|[H|H]]; [|exact H|].
      * exfalso. rewrite wbytes_head in Ht; [|lia]. injection Ht as Ht. apply (Hl (Z.of_nat t)); [lia | exact Ht].
      * exfalso. exact (Hlt _ H Hb).
    + exfalso. destruct Hr as [_ Hr]. apply (Hr (Z.to_nat j)); [lia | exact Hb].
  - right. split; [exact Hn|].
    assert (Hne : forall i : nat, (i < 8)%nat -> wbytes (w :: ws) !! i <> Some c).
    { intros i Hi E'. rewrite wbytes_head in E'; [|lia]. injection E' as E'. exact (Hn (Z.of_nat i) ltac:(lia) E'). }
    destruct r as [t|]; cbn [loop_hit option_map] in Hr |- *.
    + destruct Hr as (Ht & Hb & Hlt). assert (H8 : (8 <= t)%nat) by (destruct (Nat.lt_ge_cases t 8) as [H|H]; [exfalso; exact (Hne t H Hb) | lia]).
      replace t with (8 + (t - 8))%nat in Hb by lia. rewrite wbytes_tail in Hb.
      split; [intros ->; cbn in Hb; discriminate|]. split; [intros t' [= <-]; exact H8|].
      split; [lia|]. split; [exact Hb|].
      intros u Hu E'. apply (Hlt (8 + u)%nat); [lia | rewrite wbytes_tail; exact E'].
    + destruct Hr as [Hlen Hr]. rewrite wbytes_cons length_app length_map in Hlen. cbn [List.length idx8] in Hlen.
      split; [destruct ws; [cbn in Hlen; lia | discriminate]|]. split; [intros t' [=]|]. split; [lia|].
      intros u Hu E'. apply (Hr (8 + u)%nat); [lia | rewrite wbytes_tail; exact E'].
Qed.

(** In the final word containing end address E, the earliest match in w
    is the search result only when `A + j <= E`; otherwise the search
    returns `None`. *)
Lemma hit_last w ws c A E r : A <= E < A + 8 -> loop_hit (wbytes (w :: ws)) c A E r ->
  (exists j, 0 <= j < 8 /\ byte_of w j = c /\ (forall i, 0 <= i < j -> byte_of w i <> c) /\
     r = if A + j <=? E then Some (Z.to_nat j) else None) \/
  ((forall i, 0 <= i < 8 -> byte_of w i <> c) /\ r = None).
Proof.
  intros HE Hr. destruct (word_first w c) as [(j & Hj & Hc & Hl) | Hn].
  - left. exists j. split; [exact Hj|]. split; [exact Hc|]. split; [exact Hl|].
    assert (Hb : wbytes (w :: ws) !! Z.to_nat j = Some c) by (rewrite wbytes_head; [|lia]; rewrite Z2Nat.id; [congruence | lia]).
    destruct r as [t|]; cbn [loop_hit] in Hr.
    + destruct Hr as (Ht & Hbt & Hlt).
      assert (E1 : t = Z.to_nat j).
      { destruct (Nat.lt_total t (Z.to_nat j)) as [H|[H|H]]; [|exact H|].
        - exfalso. rewrite wbytes_head in Hbt; [|lia]. injection Hbt as Hbt. apply (Hl (Z.of_nat t)); [lia | exact Hbt].
        - exfalso. exact (Hlt _ H Hb). }
      subst t. replace (A + j <=? E) with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    + destruct Hr as [_ Hr]. destruct (Z.leb_spec (A + j) E); [|reflexivity].
      exfalso. apply (Hr (Z.to_nat j)); [lia | exact Hb].
  - right. split; [exact Hn|]. destruct r as [t|]; [|reflexivity]. exfalso. destruct Hr as (Ht & Hb & _).
    rewrite wbytes_head in Hb; [|lia]. injection Hb as Hb. exact (Hn (Z.of_nat t) ltac:(lia) Hb).
Qed.

(** Dropping k leading bytes from `w :: ws` maps index i within the
    first word to byte `k + i` of w. *)
Lemma drop_head w ws k i : (k + i < 8)%nat -> drop k (wbytes (w :: ws)) !! i = Some (byte_of w (Z.of_nat (k + i))).
Proof. intros H. rewrite lookup_drop wbytes_head; [reflexivity | lia]. Qed.

(** Dropping k leading bytes from `w :: ws` maps index `8 - k + i` to
    byte i of the remaining words `ws`. *)
Lemma drop_tail w ws k i : (k <= 8)%nat -> drop k (wbytes (w :: ws)) !! (8 - k + i)%nat = wbytes ws !! i.
Proof. intros H. rewrite lookup_drop. replace (k + (8 - k + i))%nat with (8 + i)%nat by lia. apply wbytes_tail. Qed.

(** In the unaligned first word starting at byte offset k, a match from
    k onward wins when its address is at most E; otherwise the search
    either finishes in that word or continues at the next word. *)
Lemma hit_first w ws c (k : nat) a E r : (k < 8)%nat -> a <= E ->
  loop_hit (drop k (wbytes (w :: ws))) c a E r ->
  (exists j, 0 <= j /\ j + Z.of_nat k < 8 /\ byte_of w (j + Z.of_nat k) = c /\
     (forall i, 0 <= i < j -> byte_of w (i + Z.of_nat k) <> c) /\
     r = if a + j <=? E then Some (Z.to_nat j) else None) \/
  ((forall i, Z.of_nat k <= i < 8 -> byte_of w i <> c) /\
   (E < a - Z.of_nat k + 8 -> r = None) /\
   (a - Z.of_nat k + 8 <= E -> ws <> [] /\ (forall t, r = Some t -> (8 - k <= t)%nat) /\
      loop_hit (wbytes ws) c (a - Z.of_nat k + 8) E (option_map (fun t => t - (8 - k))%nat r))).
Proof.
  intros Hk HaE Hr.
  destruct (least_below (fun i => byte_of w (Z.of_nat (k + i)) = c) (fun i => Z.eq_dec _ _) (8 - k))
    as [(j & Hj & Hp & Hl) | Hn].
  - left. exists (Z.of_nat j). split; [lia|]. split; [lia|]. split; [rewrite <- Hp; f_equal; lia|].
    split; [intros i Hi E'; apply (Hl (Z.to_nat i)); [lia | rewrite <- E'; f_equal; lia]|].
    assert (Hb : drop k (wbytes (w :: ws)) !! j = Some c) by (rewrite drop_head; [congruence | lia]).
    destruct r as [t|]; cbn [loop_hit] in Hr.
    + destruct Hr as (Ht & Hbt & Hlt).
      assert (E1 : t = j).
      { destruct (Nat.lt_total t j) as [H|[H|H]]; [|exact H|].
        - exfalso. rewrite drop_head in Hbt; [|lia]. injection Hbt as Hbt. exact (Hl t H Hbt).
        - exfalso. exact (Hlt _ H Hb). }
      subst t. rewrite Nat2Z.id. replace (a + Z.of_nat j <=? E) with true by (symmetry; apply Z.leb_le; lia).
      reflexivity.
    + destruct Hr as [_ Hr]. destruct (Z.leb_spec (a + Z.of_nat j) E); [|reflexivity].
      exfalso. exact (Hr j ltac:(lia) Hb).
  - right.
    assert (Hn' : forall i : nat, (i < 8 - k)%nat -> drop k (wbytes (w :: ws)) !! i <> Some c).
    { intros i Hi E'. rewrite drop_head in E'; [|lia]. injection E' as E'. exact (Hn i Hi E'). }
    split.
    { intros i Hi E'. apply (Hn (Z.to_nat i - k)%nat); [lia|]. rewrite <- E'. f_equal. lia. }
    assert (H8 : forall t, r = Some t -> (8 - k <= t)%nat).
    { intros t ->. destruct Hr as (_ & Hb & _). destruct (Nat.lt_ge_cases t (8 - k)) as [H|H]; [|exact H].
      exfalso. exact (Hn' t H Hb). }
    split.
    + intros HE. destruct r as [t|]; [|reflexivity]. exfalso. specialize (H8 t eq_refl).
      destruct Hr as (Ht & _). lia.
    + intros HE. split; [|split; [exact H8|]].
      * intros ->. destruct r as [t|]; cbn [loop_hit] in Hr.
        -- destruct Hr as (_ & Hb & _). specialize (H8 t eq_refl). replace t with (8 - k + (t - (8 - k)))%nat in Hb by lia.
           rewrite drop_tail in Hb; [|lia]. cbn in Hb. discriminate.
        -- destruct Hr as [Hlen _]. rewrite length_drop wbytes_length in Hlen. cbn [List.length] in Hlen. lia.
      * destruct r as [t|]; cbn [loop_hit option_map] in Hr |- *.
        -- specialize (H8 t eq_refl). destruct Hr as (Ht & Hb & Hlt).
           replace t with (8 - k + (t - (8 - k)))%nat in Hb, Ht by lia. rewrite drop_tail in Hb; [|lia].
           split; [lia|]. split; [exact Hb|]. intros u Hu E'. apply (Hlt (8 - k + u)%nat); [lia|].
           rewrite drop_tail; [exact E' | lia].
        -- destruct Hr as [Hlen Hr]. rewrite length_drop wbytes_length in Hlen. cbn [List.length] in Hlen.
           split; [rewrite wbytes_length; lia|]. intros u Hu E'. apply (Hr (8 - k + u)%nat); [lia|].
           rewrite drop_tail; [exact E' | lia].
Qed.

(** ## The loop

    When the word loop reaches the word holding the end address E, it
    must discard any matching byte that lies past E. This section sets
    up the program logic for `__memchr` and proves [memchr_last] for
    that final iteration, along with [wp_half_check_read_dq] for
    verifying [[half_check]] reads at any ownership share. *)

(** Tactic [zl] unfolds 32-bit, 48-bit, and 64-bit power-of-two bounds
    and solves linear or division arithmetic goals. *)
Ltac zl := change (2 ^ 64) with 18446744073709551616 in *; change (2 ^ 48) with 281474976710656 in *;
  change (2 ^ 32) with 4294967296 in *; first [lia | Z.div_mod_to_equations; lia].

(** To resolve IR temporary arguments during symbolic execution, [vx]
    looks up each temporary in the environment hypotheses and evaluates
    the remaining argument expressions. *)
Ltac vx :=
  cbn [map2_option map_option flight_arg_x flight_cap arg_x];
  repeat match goal with |- context [value_x ?g ?E ?k (Tmp ?n)] =>
    match goal with H : lookup n _ = Some ?x |- _ =>
      rewrite (value_x_tmp g E k n x); [|look H] end end;
  reflexivity.

(** To share the final-word and half-check rules across caller modules,
    [MemchrLastOn] instantiates them over a [[runtime]] R and a program
    logic instance LG0. *)
Module MemchrLastOn (R : Runtime) (LG0 : LogicSig R).
Module WS := WordStringOn R LG0.
Module LG := LG0.
Module L := LG.L.
Import L LG WS.

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

(** To step past pure instructions without manual boilerplate, [st]
    advances one pure `let`, [[flight]], block entry, or `goto` step
    whose premises reduce. *)
Ltac st :=
  first
    [ iApply wp_let; [reflexivity | reflexivity | vx | intros ?; reflexivity | iNext]
    | iApply wp_flight; [vx | reflexivity | vx | iNext]
    | iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]
    | iApply wp_goto; iNext ].

(** When a [[half_check]] verifies a read through pointer p against an
    already-checked capability proof `p1`, [wp_half_check_read_dq]
    discharges the check using fractional ownership of the live
    [[region]]. *)
Lemma wp_half_check_read_dq f e ls l d bd lo hi al args rest j classes p1 p b reg dq Φ :
  op_arg_classes (HalfCheck bd lo hi Read al) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p1; WPtr p] ->
  ptr_cap p1 = ptr_cap p -> ptr_cap p = Obj b \/ ptr_cap p = Ro b ->
  b <= raw_address (ptr_addr p) lo -> raw_address (ptr_addr p) lo + (hi - lo) <= r_end reg ->
  lo < hi -> r_end reg <= 2 ^ 63 -> raw_address (ptr_addr p) lo mod al = 0 ->
  liveq dq b reg -∗
  ▷ (liveq dq b reg -∗ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (HalfCheck bd lo hi Read al) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hx Hp1 Hp H1 H2 H3 H4 H5. apply (wp_read_dq registry wi ge dq _ _ _ []).
  intros m fuel (Hf & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [[E Lv] _].
  apply rule_let with (classes := classes) (xs := [WPtr p1; WPtr p]); [reflexivity | exact Hc | exact Hx |].
  exact (op_half_check_read _ _ _ _ _ _ _ _ _ Hp1 Hp E Lv H1 H2 H3 H4 H5).
Qed.

(** Block `L84` is the word-loop body of [glibc_memchr], which checks
    whether `pr.1` has reached the final word and otherwise tests word
    `pr.2` for a matching byte. *)
Definition memchr_blk84 : block := Eval vm_compute in
  match find_block (TAtom "L84") (fn_blocks glibc_memchr) with
  | Some b => b | None => mkBlock (TAtom "L84") [] [] JUnreachable end.

(** When `__memchr` reaches the word containing end address E, any match
    past E must be ignored. Lemma [memchr_last] verifies that final
    iteration of `L84`: it tests word `pr.2` against the repeated target
    byte, returns a pointer if the match lies at or before E, and
    otherwise returns null while restoring the [[region]] and word
    pieces. *)
Lemma memchr_last dq b reg w ws o e from q c E r Φ :
  (ptr_cap q = Obj b \/ ptr_cap q = Ro b) -> 0 <= o -> 0 < b -> (b + o) mod 8 = 0 -> ptr_addr q = b + o ->
  b + o + 8 * Z.of_nat (List.length (w :: ws)) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) (w :: ws) -> b + o = E - E mod 8 -> b + o <= E < 2 ^ 64 ->
  phis_env ge (b_phis memchr_blk84) from e =
    Some (put (TAtom "pr.1") (WPtr q) (put (TAtom "pr.2") (WInt (w mod 2 ^ 64)) e)) ->
  lookup (TAtom "v78") e = Some (WInt (E - E mod 8)) -> lookup (TAtom "iw_1.v7") e = Some (WInt (rep c)) ->
  lookup (TAtom "v40") e = Some (WInt E) ->
  loop_hit (wbytes (w :: ws)) (c mod 256) (b + o) E r ->
  liveq dq b reg -∗ ptsq dq (words_ps b o (w :: ws)) -∗
  (liveq dq b reg -∗ ptsq dq (words_ps b o (w :: ws)) -∗ Φ (Ret (WPtr (hit_ptr q r)))) -∗
  WP (ERun (mkFrame glibc_memchr e [] None (Enter (TAtom "L84") from)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Ho Hb0 Hal Hq Hend Hreg Hr HA HE Hphi H78 H7 H40 Hhit. iIntros "Hl Hps HK".
  iApply wp_enter; [reflexivity | exact Hphi |]. iNext. cbn [b_insts b_jump memchr_blk84].
  pose proof (Z.mod_pos_bound E 8 ltac:(lia)) as HE8.
  apply Forall_cons_1 in Hr as [Hw0 Hr]. cbn [List.length] in Hend. rewrite Nat2Z.inj_succ in Hend.
  pose proof (Nat2Z.is_nonneg (List.length ws)) as Hws.
  st. st. rewrite Hq (Z.mod_small (b + o)); [|zl]. rewrite (Z.mod_small (E - E mod 8)); [|zl].
  iApply wp_branch; [reflexivity|]. iNext. rewrite HA Z.eqb_refl. cbn [negb].
  change (0 mod 2 ^ 32 =? 0) with true. cbn [edge_label].
  st. do 6 st. rewrite !(Z.mod_small w (2 ^ 64) Hw0) rep_mod.
  set_int "iw_9.iw_1.iw_1.v13" (loop_mask (Z.lxor w (rep c))).
  iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small (loop_mask _) (2 ^ 64) (loop_mask_range _)) Zmod_0_l.
  destruct (hit_last w ws (c mod 256) (b + o) E r ltac:(zl) Hhit)
    as [(j & Hj & Hcj & Hlj & ->) | (Hn & ->)].
  + destruct (mask_first w c j Hj Hcj Hlj) as [Hm Ht]. rewrite (proj2 (Z.eqb_neq _ _) Hm). close_if.
    st. st. iApply wp_branch; [reflexivity|]. iNext.
    rewrite (Z.mod_small (loop_mask _) (2 ^ 64) (loop_mask_range _)) Zmod_0_l (proj2 (Z.eqb_neq _ _) Hm).
    close_if. do 16 (st; gen_top).
    set_tail "iw_10.iw_3.iw_1.iw_1.v22" (loop_mask (Z.lxor w (rep c))). rewrite Ht.
    st. st. set_int "iw_10.iw_3.iw_1.iw_1.v23" (8 * j + 7).
    st. set_int "iw_10.iw_3.iw_1.v27" j. st. set_int "v121" j. st. set_ptr "v122" (b + o + j).
    st. set_int "v128" (b + o + j). st.
    iApply wp_branch; [reflexivity|]. iNext.
    rewrite (Z.mod_small E (2 ^ 64)); [|zl]. rewrite (Z.mod_small (b + o + j) (2 ^ 64)); [|zl].
    destruct (Z.leb_spec (b + o + j) E) as [Hle|Hle].
    * replace ((if b + o + j <=? E then 1 else 0) mod 2 ^ 32 =? 0) with false
        by (rewrite (proj2 (Z.leb_le _ _) Hle); reflexivity).
      cbn [edge_label]. st. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      cbn [hit_ptr]. rewrite Z2Nat.id; [|lia]. rewrite Hq. iApply ("HK" with "Hl Hps").
    * replace ((if b + o + j <=? E then 1 else 0) mod 2 ^ 32 =? 0) with true
        by (rewrite (proj2 (Z.leb_gt _ _) Hle); reflexivity).
      cbn [edge_label]. st. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
      iApply ("HK" with "Hl Hps").
  + rewrite (mask_none w c Hn). close_if.
    st. iApply wp_ret; [reflexivity | reflexivity |]. iNext. iApply ("HK" with "Hl Hps").
Qed.

End rules.
End MemchrLastOn.
