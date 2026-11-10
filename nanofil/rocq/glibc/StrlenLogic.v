(** A triple for glibc's own `__strlen`, as nanofil compiles user
    glibc's string/strlen.c (docs/glibc-ir.md): for any string, not one
    literal, over any registry and world, so a program linked with
    glibc's strlen uses it as a rule at its call.

    glibc's strlen reads whole aligned 8-byte words: first the word
    holding the string's first byte, its bytes before the string masked
    off by a shift, then each next word until one holds a zero byte
    (StrlenBits.v). Every word it reads is a whole word of the
    string's object, so the triple's precondition is about words, not
    bytes:

    - the capability names the object b, read-write or read-only, and b
      is 8-aligned;
    - the caller owns the life of b and the words ws from the word that
      holds the first byte, through the word that holds the NUL, every
      byte of each, including bytes past the NUL ([words_ps]);
    - those words lie inside b's region.

    This is the whole-word rounding glibc's strlen depends on. A string
    whose NUL is the last byte of an object that ends mid-word does not
    meet it, and on such an object glibc's strlen would read past the
    end. Fil-C rounds every object up to a whole word, as filcc gives a
    13-byte literal a 16-byte object, and the model's layout rounds
    data to 8 (docs/glibc-ir.md, Findings). The result is the index of
    the first zero byte from the string's start ([first_zero]).

    [loop_spec] is the loop block, for any number of words, by
    induction on them; [wp_glibc_strlen] is the entry block, whose NUL
    is in the first word or the loop finds it. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules Symbolic ExternalCalls ExternalMachine Transport Pieces Heap Language Logic.
From Glibc Require Import LenCode GlibcLogic StrlenBits.
Open Scope Z_scope.
Open Scope list_scope.

(** glibc's `__strlen`, as the linked fixture of len.c holds it. *)
Definition glibc_strlen : func := Eval vm_compute in
  match find_direct (TAtom "__strlen")
          (match decode_module len_term with Some md => md | None => [] end) with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom "__strlen") (TAtom "export") (RClass L) [] []
  end.

(** The pieces of the 64-bit words ws from offset o of the object b. *)
Fixpoint words_ps (b o : Z) (ws : list Z) : list (piece * pval) :=
  match ws with [] => [] | w :: ws => cell b o w ++ words_ps b (o + 8) ws end.

(** The bytes of the words ws, little-endian, in order. *)
Definition wbytes (ws : list Z) : list Z := flat_map (fun w => map (byte_of w) idx8) ws.

(** The first zero of the bytes bs is at n. *)
Definition first_zero (bs : list Z) (n : nat) : Prop :=
  bs !! n = Some 0 /\ forall u, (u < n)%nat -> bs !! u <> Some 0.

(** The bytes of the words w :: ws are w's eight, then ws's. *)
Lemma wbytes_cons w ws : wbytes (w :: ws) = map (byte_of w) idx8 ++ wbytes ws.
Proof. reflexivity. Qed.

(** Byte i below 8 of w :: ws is w's byte i. *)
Lemma wbytes_head w ws (i : nat) : (i < 8)%nat -> wbytes (w :: ws) !! i = Some (byte_of w (Z.of_nat i)).
Proof.
  intros Hi. rewrite wbytes_cons lookup_app_l; [|rewrite length_map; cbn; lia].
  do 8 (destruct i as [|i]; [reflexivity|]). lia.
Qed.

(** Byte 8 + i of w :: ws is byte i of ws. *)
Lemma wbytes_tail w ws (i : nat) : wbytes (w :: ws) !! (8 + i)%nat = wbytes ws !! i.
Proof. rewrite wbytes_cons lookup_app_r; [|rewrite length_map; cbn; lia]. rewrite length_map. f_equal. cbn. lia. Qed.

(** Where the first zero of the bytes of w :: ws from k, k below 8,
    is at n, and k + n is inside w: byte k + n of w is zero and its
    bytes from k before it are not. *)
Lemma first_zero_in w ws k n : (k < 8)%nat -> first_zero (drop k (wbytes (w :: ws))) n -> (k + n < 8)%nat ->
  byte_of w (Z.of_nat (k + n)) = 0 /\ forall i, (k <= i < k + n)%nat -> byte_of w (Z.of_nat i) <> 0.
Proof.
  intros Hk [Hz Hlt] Hn. rewrite lookup_drop wbytes_head in Hz; [|lia]. split; [congruence|].
  intros i Hi E. apply (Hlt (i - k)%nat); [lia|]. rewrite lookup_drop wbytes_head; [|lia].
  replace (k + (i - k))%nat with i by lia. rewrite E. reflexivity.
Qed.

(** Where the first zero of the bytes of w :: ws from k is at n, and
    k + n is past w: w's bytes from k are nonzero, and the first zero
    of ws's bytes is at k + n - 8. *)
Lemma first_zero_past w ws k n : (k < 8)%nat -> first_zero (drop k (wbytes (w :: ws))) n -> (8 <= k + n)%nat ->
  (forall i, (k <= i < 8)%nat -> byte_of w (Z.of_nat i) <> 0) /\ first_zero (wbytes ws) (k + n - 8).
Proof.
  intros Hk [Hz Hlt] Hn. split.
  - intros i Hi E. apply (Hlt (i - k)%nat); [lia|]. rewrite lookup_drop wbytes_head; [|lia].
    replace (k + (i - k))%nat with i by lia. rewrite E. reflexivity.
  - split.
    + rewrite lookup_drop in Hz. replace (k + n)%nat with (8 + (k + n - 8))%nat in Hz by lia.
      rewrite wbytes_tail in Hz. exact Hz.
    + intros u Hu E. apply (Hlt (8 + u - k)%nat); [lia|]. rewrite lookup_drop.
      replace (k + (8 + u - k))%nat with (8 + u)%nat by lia. rewrite wbytes_tail. exact E.
Qed.

(** A temporary's value at class k is what the environment holds for it,
    taken at k. *)
Lemma value_x_tmp ge e k n x : lookup n e = Some x -> value_x ge e k (Tmp n) = word_at_class k x.
Proof. intros H. cbn. rewrite H. reflexivity. Qed.

(** The triple over the [[runtime]] R and the Logic instance LG0. *)
Module StrlenOn (R : Runtime) (LG0 : LogicSig R).
Module GL := GlibcLogicOn R LG0.
Module LG := LG0.
Module L := LG.L.
Import L LG GL.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
(** The Iris instance of the registry and wi. *)
Local Instance rules_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** One step whose premises reduce: a pure let, a flight, entering a
    block, or a goto. The values stay symbolic. *)
Ltac st :=
  first
    [ iApply wp_let; [reflexivity | reflexivity | reflexivity | intros ?; reflexivity | iNext]
    | iApply wp_flight; [reflexivity | reflexivity | reflexivity | iNext]
    | iApply wp_enter; [reflexivity | reflexivity | iNext; cbn [b_insts b_jump]]
    | iApply wp_goto; iNext ].

(** Drop each wrap to 64 or 32 bits that arithmetic shows the identity. *)
Ltac unwrap :=
  repeat match goal with
    | |- context [?x mod 2 ^ 64] => rewrite (Z.mod_small x (2 ^ 64)); [|lia]
    | |- context [?x mod 2 ^ 32] => rewrite (Z.mod_small x (2 ^ 32)); [|lia]
    end.

(** Keep only arithmetic hypotheses, so lia does not read the rest. *)
Ltac clear_junk :=
  repeat match goal with
    H : ?T |- _ =>
      lazymatch T with
      | @eq Z _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | and (Z.le _ _) _ => fail
      | lt _ _ => fail | le _ _ => fail
      | _ => clear H
      end
    end.
(** Compute each closed shift factor 2 ^ (n mod m). *)
Ltac pow_closed :=
  repeat match goal with |- context [2 ^ (?n mod ?m)] =>
    let v := fresh "v" in let Ev := fresh "Ev" in
    remember (2 ^ (n mod m)) as v eqn:Ev; vm_compute in Ev; subst v end.
(** An address or integer fact, by arithmetic. *)
Ltac arith := cbn [ptr_addr ptr_cap extension]; unfold raw_address; clear_junk; pow_closed; unwrap;
  first [lia | Z.div_mod_to_equations; lia].

(** A branch whose condition is closed: computed. *)
Ltac close_if :=
  match goal with |- context [edge_label (if ?c then _ else _)] =>
    first [change c with true | change c with false]
  end; cbn [edge_label].

(** The v4 lookup through the puts of a block, to the frame's e. *)
Ltac look H := repeat (rewrite lookup_after_put_other; [|reflexivity]); exact H.

(** Name the integer the temporary name holds v, by computation or arithmetic. *)
Ltac set_int name v :=
  match goal with |- context [put (TAtom name) (WInt ?X) _] => replace X with v by first [reflexivity | arith] end.
(** Name the address of the pointer the temporary name holds v. *)
Ltac set_ptr name v :=
  match goal with |- context [put (TAtom name) (WPtr (mkPtr ?X _)) _] => replace X with v by first [reflexivity | arith] end.

(** The loop's block, L28: load the next word and test it for a zero. *)
Definition blk28 : block := Eval vm_compute in
  match find_block (TAtom "L28") (fn_blocks glibc_strlen) with
  | Some b => b | None => mkBlock (TAtom "L28") [] [] JUnreachable end.

(** The loop, entered with pr.1 the previous word's pointer q and v4
    the string's address a, owning the words ws from offset o of the
    8-aligned word b + o on, whose first zero byte is t bytes in:
    strlen returns b + o + t - a, the pieces handed back. *)
Lemma loop_spec b reg c a ws o e from t q Φ :
  (c = Obj b \/ c = Ro b) -> 0 <= o -> 8 <= b + o -> (b + o) mod 8 = 0 -> 0 <= a <= b + o ->
  b + o + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws -> first_zero (wbytes ws) t ->
  ptr_addr q = b + o - 8 -> ptr_cap q = c ->
  phis_env ge (b_phis blk28) from e = Some (put (TAtom "pr.1") (WPtr q) e) ->
  lookup (TAtom "v4") e = Some (WInt a) ->
  live b reg -∗ pts (words_ps b o ws) -∗
  (live b reg -∗ pts (words_ps b o ws) -∗ Φ (Ret (WInt (b + o + Z.of_nat t - a)))) -∗
  WP (ERun (mkFrame glibc_strlen e [] None (Enter (TAtom "L28") from)) : gexpr) {{ Φ }}.
Proof.
  revert o e from t q. induction ws as [|w ws IH]; intros o e from t q Hc Ho Hb8 Hal Ha Hend Hreg Hr Hz Hqa Hqc Hphi Hv4.
  { destruct Hz as [Hz _]. cbn in Hz. discriminate. }
  cbn [List.length] in Hend. rewrite Nat2Z.inj_succ in Hend.
  iIntros "Hl Hps HK". cbn [words_ps]. rewrite pts_app. iDestruct "Hps" as "[Hw Hps]".
  iApply wp_enter; [reflexivity | exact Hphi |]. iNext. cbn [b_insts b_jump blk28].
  st. set_ptr "v32" (b + o).
  iApply (wp_check_read with "Hl").
  { reflexivity. } { reflexivity. } { cbn [ptr_cap]. rewrite Hqc. exact Hc. } { arith. } { arith. } { apply Z.mod_1_r. }
  iNext. iIntros "Hl".
  iApply (wp_raw_load_read with "Hl Hw"); [reflexivity | reflexivity | cbn [ptr_cap]; rewrite Hqc; exact Hc | arith |].
  iNext. iIntros "Hl Hw".
  apply Forall_cons_1 in Hr as [Hw0 Hr]. rewrite (Z.mod_small w (2 ^ 64) Hw0).
  do 4 st. set_int "iw_4.iw_1.v13" (loop_mask w).
  st. iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small (loop_mask w) (2 ^ 64) (loop_mask_range w)) Zmod_0_l.
  destruct (Nat.lt_ge_cases t 8) as [Ht|Ht].
  - (* w holds the NUL, at byte t. *)
    destruct (first_zero_in w ws 0 t ltac:(lia) Hz ltac:(lia)) as [Hzt Hnz]. cbn [Nat.add] in Hzt.
    assert (Hlow : forall i, 0 <= i < Z.of_nat t -> byte_of w i <> 0).
    { intros i Hi. specialize (Hnz (Z.to_nat i) ltac:(lia)). rewrite Z2Nat.id in Hnz; [exact Hnz | lia]. }
    assert (Hb : byte_of (loop_mask w) (Z.of_nat t) = 128) by (apply loop_mask_at; [lia | exact Hlow | exact Hzt]).
    assert (Hm : (loop_mask w =? 0) = false).
    { apply Z.eqb_neq. intros E. rewrite E in Hb. unfold byte_of in Hb. rewrite Z.div_0_l in Hb; [discriminate|].
      apply Z.pow_nonzero; lia. }
    rewrite Hm. close_if.
    st. iApply wp_branch; [reflexivity|]. iNext. close_if.
    do 16 st.
    set_int "iw_5.iw_3.iw_1.iw_1.v22" (tail (loop_mask w)).
    rewrite (tail_first (loop_mask w) (Z.of_nat t) (loop_mask_range w) (loop_mask_01 w) ltac:(lia) Hb
      (fun i Hi => loop_mask_below w (Z.of_nat t) i ltac:(lia) Hlow Hi)).
    st. st. set_int "iw_5.iw_3.iw_1.iw_1.v23" (8 * Z.of_nat t + 7).
    st. set_int "iw_5.iw_3.iw_1.v27" (Z.of_nat t).
    st. set_int "v41" (Z.of_nat t).
    st. set_ptr "v42" (b + o + Z.of_nat t).
    st.
    iApply wp_let;
      [reflexivity | reflexivity
      | cbn [map2_option]; rewrite (value_x_tmp _ _ _ (TAtom "v4") (WInt a)); [reflexivity | look Hv4]
      | intros ?; reflexivity | iNext].
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) => replace X with (b + o + Z.of_nat t - a) by arith end.
    iApply ("HK" with "Hl [$Hw $Hps]").
  - (* w has no zero byte: the next word. *)
    destruct (first_zero_past w ws 0 t ltac:(lia) Hz ltac:(lia)) as [Hnz Hz']. cbn [Nat.add] in Hz'.
    assert (Hm : loop_mask w = 0).
    { apply zero_word; [apply loop_mask_range|]. intros i Hi. apply (loop_mask_below w 8 i); [lia | | lia].
      intros k Hk. specialize (Hnz (Z.to_nat k) ltac:(lia)). rewrite Z2Nat.id in Hnz; [exact Hnz | lia]. }
    rewrite Hm. close_if.
    iApply (IH (o + 8) _ (Some (TAtom "L28")) (t - 8)%nat (mkPtr (b + o) (ptr_cap q)) with "Hl Hps [Hw HK]").
    + exact Hc.
    + lia.
    + lia.
    + replace (b + (o + 8)) with (b + o + 1 * 8) by ring. rewrite Z_mod_plus_full. exact Hal.
    + lia.
    + lia.
    + exact Hreg.
    + exact Hr.
    + exact Hz'.
    + cbn. lia.
    + exact Hqc.
    + reflexivity.
    + look Hv4.
    + iIntros "Hl Hps". replace (b + (o + 8) + Z.of_nat (t - 8) - a) with (b + o + Z.of_nat t - a) by lia.
      iApply ("HK" with "Hl [$Hw $Hps]").
Qed.

(** glibc's strlen of p: owning the life of the 8-aligned object b and
    the words ws of it from the word that holds p's byte, inside its
    region, whose first zero byte from p is n bytes in, the call
    returns n and hands the pieces back. *)
Lemma wp_glibc_strlen p b reg ws n Φ :
  (ptr_cap p = Obj b \/ ptr_cap p = Ro b) -> 0 < b -> b mod 8 = 0 -> b <= ptr_addr p ->
  ptr_addr p - ptr_addr p mod 8 + 8 * Z.of_nat (List.length ws) <= r_end reg -> r_end reg <= 2 ^ 48 ->
  Forall (fun w => 0 <= w < 2 ^ 64) ws ->
  first_zero (drop (Z.to_nat (ptr_addr p mod 8)) (wbytes ws)) n ->
  live b reg -∗ pts (words_ps b (ptr_addr p - ptr_addr p mod 8 - b) ws) -∗
  (live b reg -∗ pts (words_ps b (ptr_addr p - ptr_addr p mod 8 - b) ws) -∗ Φ (Ret (WInt (Z.of_nat n)))) -∗
  WP (ERun (mkFrame glibc_strlen [(TAtom "v0", WPtr p)] [] None (Enter (TAtom "start") None)) : gexpr)
    {{ Φ }}.
Proof.
  destruct p as [a c]. cbn [ptr_addr ptr_cap]. intros Hc Hb0 Hb8 Hba Hend Hreg Hr Hz.
  pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Hk.
  assert (Hal : b <= a - a mod 8) by (pose proof (Z.div_mod a 8 ltac:(lia)); pose proof (Z.div_mod b 8 ltac:(lia)); nia).
  destruct ws as [|w ws].
  { destruct Hz as [Hz _]. rewrite drop_nil in Hz. discriminate. }
  cbn [List.length] in Hend. rewrite Nat2Z.inj_succ in Hend.
  apply Forall_cons_1 in Hr as [Hw0 Hr].
  iIntros "Hl Hps HK". cbn [words_ps]. rewrite pts_app. iDestruct "Hps" as "[Hw Hps]".
  do 5 st.
  match goal with |- context [put (TAtom "v10") (WPtr (mkPtr ?X _)) _] =>
    replace X with (a - a mod 8) by
      (cbn [ptr_addr]; rewrite (Z.mod_small a (2 ^ 64)); [rewrite land_align; [arith | lia] | lia]) end.
  iApply (wp_check_read with "Hl"); [reflexivity | reflexivity | exact Hc | arith | arith | apply Z.mod_1_r |].
  iNext. iIntros "Hl".
  iApply (wp_raw_load_read with "Hl Hw"); [reflexivity | reflexivity | exact Hc | arith |].
  iNext. iIntros "Hl Hw". rewrite (Z.mod_small w (2 ^ 64) Hw0).
  do 8 st. set_int "iw_2.v12" (first_shift w a).
  st. iApply wp_branch; [reflexivity|]. iNext.
  rewrite (Z.mod_small (first_shift w a) (2 ^ 64) (first_shift_range w a)) Zmod_0_l.
  assert (Hfs : forall i, 0 <= i -> byte_of (first_shift w a) i =
            if i + a mod 8 <? 8 then (if byte_of w (i + a mod 8) =? 0 then 128 else 0) else 0)
    by (intros i Hi; apply first_shift_byte; lia).
  assert (Hk8 : (Z.to_nat (a mod 8) < 8)%nat) by (change 8%nat with (Z.to_nat 8); apply Z2Nat.inj_lt; lia).
  destruct (Nat.lt_ge_cases (Z.to_nat (a mod 8) + n) 8) as [Hn|Hn].
  - (* The NUL is in the first word. *)
    destruct (first_zero_in w ws _ n Hk8 Hz Hn) as [Hzn Hnz].
    rewrite Nat2Z.inj_add Z2Nat.id in Hzn; [|lia].
    assert (Hat : byte_of (first_shift w a) (Z.of_nat n) = 128).
    { rewrite Hfs; [|lia]. replace (Z.of_nat n + a mod 8 <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      rewrite (Z.add_comm (Z.of_nat n)) Hzn. reflexivity. }
    assert (Hlow : forall i, 0 <= i < Z.of_nat n -> byte_of (first_shift w a) i = 0).
    { intros i Hi. rewrite Hfs; [|lia]. replace (i + a mod 8 <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
      specialize (Hnz (Z.to_nat (i + a mod 8)) ltac:(lia)). rewrite Z2Nat.id in Hnz; [|lia].
      apply Z.eqb_neq in Hnz. rewrite Hnz. reflexivity. }
    assert (H01 : forall i, 0 <= i < 8 -> byte_of (first_shift w a) i = 0 \/ byte_of (first_shift w a) i = 128).
    { intros i Hi. rewrite Hfs; [|lia]. destruct (_ <? 8); [destruct (_ =? 0)|]; auto. }
    assert (Hnz0 : (first_shift w a =? 0) = false).
    { apply Z.eqb_neq. intros E. rewrite E in Hat. unfold byte_of in Hat. rewrite Z.div_0_l in Hat; [discriminate|].
      apply Z.pow_nonzero; lia. }
    rewrite Hnz0. close_if.
    st. st. iApply wp_branch; [reflexivity|]. iNext.
    rewrite (Z.mod_small (first_shift w a) (2 ^ 64) (first_shift_range w a)) Zmod_0_l Hnz0. close_if.
    do 16 st.
    set_int "iw_3.iw_1.iw_1.v22" (tail (first_shift w a)).
    rewrite (tail_first (first_shift w a) (Z.of_nat n) (first_shift_range w a) H01 ltac:(lia) Hat Hlow).
    st. st. set_int "iw_3.iw_1.iw_1.v23" (8 * Z.of_nat n + 7).
    st. set_int "iw_3.iw_1.v27" (Z.of_nat n).
    st. set_int "v26" (Z.of_nat n).
    iApply wp_ret; [reflexivity | reflexivity |]. iNext.
    match goal with |- environments.envs_entails _ (Φ (Ret (WInt ?X))) => replace X with (Z.of_nat n) by arith end.
    iApply ("HK" with "Hl [$Hw $Hps]").
  - (* The NUL is in a later word: the loop. *)
    destruct (first_zero_past w ws _ n Hk8 Hz Hn) as [Hnz Hz'].
    assert (H0 : first_shift w a = 0).
    { apply zero_word; [apply first_shift_range|]. intros i Hi. rewrite Hfs; [|lia].
      destruct (i + a mod 8 <? 8) eqn:E; [|reflexivity]. apply Z.ltb_lt in E.
      specialize (Hnz (Z.to_nat (i + a mod 8)) ltac:(lia)). rewrite Z2Nat.id in Hnz; [|lia].
      apply Z.eqb_neq in Hnz. rewrite Hnz. reflexivity. }
    rewrite H0. close_if.
    iApply (loop_spec b reg c a ws (a - a mod 8 - b + 8) _ (Some (TAtom "start"))
              (Z.to_nat (a mod 8) + n - 8)%nat (mkPtr (a - a mod 8) c) with "Hl Hps [Hw HK]").
    + exact Hc.
    + lia.
    + lia.
    + replace (b + (a - a mod 8 - b + 8)) with (8 * (a / 8 + 1)) by (pose proof (Z.div_mod a 8); lia).
      rewrite Z.mul_comm Z_mod_mult. reflexivity.
    + lia.
    + lia.
    + exact Hreg.
    + exact Hr.
    + exact Hz'.
    + cbn. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + iIntros "Hl Hps".
      replace (b + (a - a mod 8 - b + 8) + Z.of_nat (Z.to_nat (a mod 8) + n - 8) - a) with (Z.of_nat n) by lia.
      iApply ("HK" with "Hl [$Hw $Hps]").
Qed.

End rules.
End StrlenOn.
