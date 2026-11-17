(** The checker of [AbsRun](AbsRun.v) keeps the bytes of every object it
    owns, and it decides from them whether a check passes and what a
    load returns. This module shows that those decisions agree with the
    machine. It relates the contents that [AbsDen](AbsDen.v) gives an
    abstract state to a real memory, and then it proves one lemma for
    each kind of memory instruction: a check, a load, a store, a
    pointer load, a pointer store, a flight and an allocation.

    Every lemma here is an ordinary proposition about the machine's
    functions. The program logic appears only in
    [AbsSound](AbsSound.v), which turns these lemmas into rules. *)

From Stdlib Require Import String ZArith List Bool Lia PeanoNat.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics Symbolic Pieces StepRules
  AbsRun AbsDen.
Import ListNotations.
Open Scope Z_scope.

(** * Little-endian bytes

    A load returns the number whose little-endian bytes are in memory.
    The lemmas of this section relate that number to its bytes. *)

Definition is_byte (x : Z) : Prop := 0 <= x < 256.

Lemma byte_of_range x i : is_byte (byte_of x i).
Proof. unfold is_byte, byte_of. apply Z.mod_pos_bound. lia. Qed.

Lemma of_bytes'_bound xs : Forall is_byte xs -> 0 <= of_bytes' xs < 2 ^ (8 * Z.of_nat (length xs)).
Proof.
  induction 1 as [|x xs Hx _ IH]; cbn [of_bytes' length]; [cbn; lia|].
  rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat (length xs))) with (8 + 8 * Z.of_nat (length xs)) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256. unfold is_byte in Hx. nia.
Qed.

Lemma byte_of_cons_0 x r : is_byte x -> byte_of (x + 256 * r) 0 = x.
Proof.
  intros Hx. unfold byte_of. change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r.
  replace (x + 256 * r) with (x + r * 256) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. exact Hx.
Qed.

Lemma byte_of_cons_S x r i : is_byte x -> 0 <= i -> byte_of (x + 256 * r) (i + 1) = byte_of r i.
Proof.
  intros Hx Hi. unfold byte_of. replace (8 * (i + 1)) with (8 + 8 * i) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  rewrite <- Z.div_div by lia. f_equal. f_equal.
  replace (x + 256 * r) with (x + r * 256) by lia. rewrite Z.div_add by lia.
  rewrite (Z.div_small x 256) by exact Hx. reflexivity.
Qed.

(** The bytes of a number that was built from bytes are those bytes. *)
Lemma byte_of_of_bytes' xs i x :
  Forall is_byte xs -> nth_error xs i = Some x -> byte_of (of_bytes' xs) (Z.of_nat i) = x.
Proof.
  intros H. revert i. induction H as [|y ys Hy _ IH]; intros [|i]; cbn [nth_error of_bytes']; try discriminate.
  - intros [= <-]. apply byte_of_cons_0. exact Hy.
  - intros E. rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite byte_of_cons_S by (auto; lia). apply IH. exact E.
Qed.

(** Consecutive bytes of one number, starting at byte [i], build the
    number shifted down by [i] bytes and cut to their length. *)
Lemma of_bytes'_byte_of v xs : forall i, 0 <= i ->
  (forall j x, nth_error xs j = Some x -> x = byte_of v (i + Z.of_nat j)) ->
  of_bytes' xs = (v / 2 ^ (8 * i)) mod 2 ^ (8 * Z.of_nat (length xs)).
Proof.
  induction xs as [|x xs IH]; intros i Hi H; cbn [of_bytes' length]; [cbn; rewrite Z.mod_1_r; reflexivity|].
  rewrite Nat2Z.inj_succ. replace (8 * Z.succ (Z.of_nat (length xs))) with (8 + 8 * Z.of_nat (length xs)) by lia.
  rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
  rewrite Z.rem_mul_r by lia. rewrite Z.div_div by lia.
  rewrite (IH (i + 1)); [|lia|].
  - replace (8 * (i + 1)) with (8 * i + 8) by lia. rewrite Z.pow_add_r by lia. change (2 ^ 8) with 256.
    rewrite (H O x eq_refl). unfold byte_of. rewrite Z.add_0_r. reflexivity.
  - intros j y E. rewrite (H (Datatypes.S j) y E). f_equal. lia.
Qed.

Lemma testbit_byte_of v i k : 0 <= i -> 0 <= k < 8 -> Z.testbit (byte_of v i) k = Z.testbit v (8 * i + k).
Proof.
  intros Hi Hk. unfold byte_of. change 256 with (2 ^ 8). rewrite Z.mod_pow2_bits_low by lia.
  rewrite Z.div_pow2_bits by lia. f_equal. lia.
Qed.

Lemma land_low_byte x r mask : is_byte x -> 0 <= mask < 256 -> Z.land (x + 256 * r) mask = Z.land x mask.
Proof.
  intros Hx Hm. apply Z.bits_inj'. intros n Hn. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases n 8) as [Hlt|Hge].
  - f_equal. rewrite <- (byte_of_cons_0 x r Hx) at 2. rewrite testbit_byte_of by lia. f_equal.
  - assert (Z.testbit mask n = false) as ->; [|rewrite !andb_false_r; reflexivity].
    destruct (Z.eq_dec mask 0) as [->|Hne]; [apply Z.bits_0|]. apply Z.bits_above_log2; [lia|].
    apply Z.log2_lt_pow2; [lia|]. apply Z.lt_le_trans with (2 ^ 8); [exact (proj2 Hm)|].
    apply Z.pow_le_mono_r; lia.
Qed.

(** * Windows of a list

    A load reads a window of an object's bytes, and a store splices new
    bytes into them. These lemmas say what [window] and [splice] do to
    one position of a list. *)

Lemma nth_error_window {Y : Type} k w (l : list Y) j :
  0 <= k -> (j < Z.to_nat w)%nat -> nth_error (window k w l) j = nth_error l (Z.to_nat k + j).
Proof.
  intros Hk Hj. unfold window. rewrite nth_error_firstn.
  destruct (Nat.ltb_spec j (Z.to_nat w)); [|lia]. apply nth_error_skipn.
Qed.

Lemma length_window {Y : Type} k w (l : list Y) :
  0 <= k -> 0 <= w -> k + w <= Z.of_nat (length l) -> length (window k w l) = Z.to_nat w.
Proof. intros Hk Hw H. unfold window. rewrite length_firstn, length_skipn. lia. Qed.

Lemma length_splice {Y : Type} k (new l : list Y) :
  0 <= k -> k + Z.of_nat (length new) <= Z.of_nat (length l) -> length (splice k new l) = length l.
Proof. intros Hk H. unfold splice. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

Lemma nth_error_splice {Y : Type} k (new l : list Y) j :
  0 <= k -> k + Z.of_nat (length new) <= Z.of_nat (length l) ->
  nth_error (splice k new l) j =
  if (Z.to_nat k <=? j)%nat && (j <? Z.to_nat k + length new)%nat then nth_error new (j - Z.to_nat k)
  else nth_error l j.
Proof.
  intros Hk H. unfold splice.
  destruct (Nat.leb_spec (Z.to_nat k) j) as [H1|H1]; cbn [andb].
  - rewrite nth_error_app2 by (rewrite length_firstn; lia). rewrite length_firstn.
    replace (Nat.min (Z.to_nat k) (length l)) with (Z.to_nat k) by lia.
    destruct (Nat.ltb_spec j (Z.to_nat k + length new)) as [H2|H2].
    + apply nth_error_app1. lia.
    + rewrite nth_error_app2 by lia. rewrite nth_error_skipn. f_equal. lia.
  - rewrite nth_error_app1 by (rewrite length_firstn; lia). rewrite nth_error_firstn. destruct (Nat.ltb_spec j (Z.to_nat k)); [reflexivity | lia].
Qed.

(** Two lists are related position by position when they have the same
    length and the elements at every position are related. *)
Lemma Forall2_nth {X Y : Type} (P : X -> Y -> Prop) l l' :
  Forall2 P l l' <->
  length l = length l' /\ forall j a b, nth_error l j = Some a -> nth_error l' j = Some b -> P a b.
Proof.
  split.
  - induction 1 as [|a b l l' Hab _ [IH1 IH2]]; split; cbn; try lia.
    + intros [|j]; discriminate.
    + intros [|j] a' b'; cbn; [intros [= <-] [= <-]; exact Hab | apply IH2].
  - revert l'. induction l as [|a l IH]; intros [|b l'] [Hl H]; try discriminate; constructor.
    + exact (H O a b eq_refl eq_refl).
    + apply IH. split; [cbn in Hl; lia|]. intros j. exact (H (Datatypes.S j)).
Qed.

Lemma Forall_nth_error {X : Type} (P : X -> Prop) l :
  Forall P l <-> forall j a, nth_error l j = Some a -> P a.
Proof.
  rewrite Forall_forall. split.
  - intros H j a E. apply H. eapply nth_error_In. exact E.
  - intros H a Hin. destruct (In_nth_error _ _ Hin) as [j E]. exact (H j a E).
Qed.

Lemma of_bytes'_app xs ys : of_bytes' (xs ++ ys) = of_bytes' xs + 256 ^ Z.of_nat (length xs) * of_bytes' ys.
Proof.
  induction xs as [|x xs IH]; cbn [app of_bytes' length]; [rewrite Z.pow_0_r; lia|].
  rewrite IH, Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma load_go m a : forall xs acc,
  (forall j x, nth_error xs j = Some x -> m_bytes m (a + Z.of_nat j) = x) ->
  (fix go (n : nat) (acc : Z) {struct n} : Z :=
     match n with
     | O => acc
     | Datatypes.S n' => go n' (acc * 256 + m_bytes m (a + Z.of_nat n'))
     end) (length xs) acc = acc * 256 ^ Z.of_nat (length xs) + of_bytes' xs.
Proof.
  induction xs as [|x xs IH] using rev_ind; intros acc H; [cbn; lia|].
  rewrite length_app. cbn [length]. rewrite Nat.add_1_r.
  rewrite (H (length xs) x) by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
  rewrite IH by (intros j y E; apply H; rewrite nth_error_app1 by (apply nth_error_Some; congruence); exact E).
  rewrite of_bytes'_app, Nat2Z.inj_succ, Z.pow_succ_r by lia. cbn [of_bytes']. ring.
Qed.

(** The machine loads the number that the bytes in memory build. *)
Lemma load_bytes_spec m a xs :
  (forall j x, nth_error xs j = Some x -> m_bytes m (a + Z.of_nat j) = x) ->
  load_bytes m a (Z.of_nat (length xs)) = of_bytes' xs.
Proof.
  intros H. unfold load_bytes. rewrite Nat2Z.id. etransitivity; [apply (load_go m a xs 0 H)|]. lia.
Qed.

Lemma byte_of_small x : is_byte x -> byte_of x 0 = x.
Proof.
  intros Hx. unfold byte_of. change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r. apply Z.mod_small. exact Hx.
Qed.

Lemma Forall2_firstn {X Y : Type} (P : X -> Y -> Prop) n l l' :
  Forall2 P l l' -> Forall2 P (firstn n l) (firstn n l').
Proof. intros H. revert n. induction H; intros [|n]; cbn; constructor; auto. Qed.

Lemma Forall2_skipn {X Y : Type} (P : X -> Y -> Prop) n l l' :
  Forall2 P l l' -> Forall2 P (skipn n l) (skipn n l').
Proof. intros H. revert n. induction H; intros [|n]; cbn; auto. Qed.

Lemma Forall2_window {X Y : Type} (P : X -> Y -> Prop) k w l l' :
  Forall2 P l l' -> Forall2 P (window k w l) (window k w l').
Proof. intros H. apply Forall2_firstn, Forall2_skipn. exact H. Qed.

Lemma Forall_firstn' {X : Type} (P : X -> Prop) n l : Forall P l -> Forall P (firstn n l).
Proof. intros H. revert n. induction H; intros [|n]; cbn; constructor; auto. Qed.

Lemma Forall_skipn' {X : Type} (P : X -> Prop) n l : Forall P l -> Forall P (skipn n l).
Proof. intros H. revert n. induction H; intros [|n]; cbn; auto. Qed.

Lemma Forall_window {X : Type} (P : X -> Prop) k w l : Forall P l -> Forall P (window k w l).
Proof. intros H. apply Forall_firstn', Forall_skipn'. exact H. Qed.

Lemma Forall_splice {X : Type} (P : X -> Prop) k new l : Forall P new -> Forall P l -> Forall P (splice k new l).
Proof.
  intros H1 H2. unfold splice. apply Forall_app. split; [apply Forall_firstn'; exact H2|].
  apply Forall_app. split; [exact H1 | apply Forall_skipn'; exact H2].
Qed.

(** New elements spliced into one list are related to the other list
    when they are related to its window at the same place. *)
Lemma Forall2_splice {X Y : Type} (P : X -> Y -> Prop) k new l l' :
  0 <= k -> k + Z.of_nat (length new) <= Z.of_nat (length l) ->
  Forall2 P l l' -> Forall2 P new (window k (Z.of_nat (length new)) l') -> Forall2 P (splice k new l) l'.
Proof.
  intros Hk Hl H Hn. apply Forall2_nth in H as [El H]. apply Forall2_nth in Hn as [_ Hn].
  apply Forall2_nth. split; [rewrite length_splice by lia; exact El|].
  intros j a b. rewrite nth_error_splice by lia.
  destruct ((Z.to_nat k <=? j)%nat && (j <? Z.to_nat k + length new)%nat) eqn:Ej; [|apply H].
  apply andb_true_iff in Ej as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
  intros Ea Eb. apply (Hn (j - Z.to_nat k)%nat a b Ea).
  rewrite nth_error_window by lia. rewrite <- Eb. f_equal. lia.
Qed.

(** A sign or zero extension of a loaded number is the number itself
    when its sign bit is known to be clear or the class cuts it off. *)
Lemma extension_keep n k md u hi :
  ((k = W /\ md = 2 ^ 32) \/ (k = L /\ md = 2 ^ 64)) -> 0 <= u < 2 ^ (8 * fst (narrow_type n)) -> u <= hi ->
  match n with
  | Uw | Uh | Ub => true
  | Sw => match k with W => true | _ => hi <? 2 ^ 31 end
  | Sh => hi <? 32768
  | Sb => hi <? 128
  end = true ->
  extension n u mod md = u.
Proof.
  intros Hk Hu Hh Hkeep.
  assert (Hmd : 2 ^ 32 <= md) by (destruct Hk as [[_ ->]|[_ ->]]; lia).
  destruct n; cbn [narrow_type fst] in Hu; unfold extension, sign_extension; cbv zeta.
  - assert (Hu' : 0 <= u < 2 ^ 32) by exact Hu. rewrite (Z.mod_small u (2 ^ 32)) by exact Hu'.
    destruct (Z.leb_spec (2 ^ 31) u) as [Hge|Hlt]; [|apply Z.mod_small; lia].
    destruct Hk as [[-> ->]|[-> ->]].
    + replace (u - 2 ^ 32) with (u + (-1) * 2 ^ 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    + change ((hi <? 2 ^ 31) = true) in Hkeep. apply Z.ltb_lt in Hkeep. lia.
  - assert (Hu' : 0 <= u < 2 ^ 32) by exact Hu. rewrite (Z.mod_small u (2 ^ 32)) by exact Hu'.
    apply Z.mod_small. lia.
  - assert (Hu' : 0 <= u < 65536) by exact Hu. apply Z.ltb_lt in Hkeep. rewrite (Z.mod_small u 65536) by exact Hu'.
    destruct (Z.leb_spec 32768 u); [lia|]. apply Z.mod_small. lia.
  - assert (Hu' : 0 <= u < 65536) by exact Hu. rewrite (Z.mod_small u 65536) by exact Hu'. apply Z.mod_small. lia.
  - assert (Hu' : 0 <= u < 256) by exact Hu. apply Z.ltb_lt in Hkeep. rewrite (Z.mod_small u 256) by exact Hu'.
    destruct (Z.leb_spec 128 u); [lia|]. apply Z.mod_small. lia.
  - assert (Hu' : 0 <= u < 256) by exact Hu. rewrite (Z.mod_small u 256) by exact Hu'. apply Z.mod_small. lia.
Qed.

Lemma Forall2_splice2 {X Y : Type} (P : X -> Y -> Prop) k new new' l l' :
  Forall2 P l l' -> Forall2 P new new' -> Forall2 P (splice k new l) (splice k new' l').
Proof.
  intros H Hn. unfold splice. rewrite (Forall2_length Hn). apply Forall2_app; [apply Forall2_firstn; exact H|].
  apply Forall2_app; [exact Hn | apply Forall2_skipn; exact H].
Qed.

(** The function [bytes_of] lists the first [n] little-endian bytes of
    a number, starting with the lowest byte. *)
Definition bytes_of (z : Z) (n : nat) : list Z := map (fun i => byte_of z (Z.of_nat i)) (seq 0 n).

Lemma length_bytes_of z n : length (bytes_of z n) = n.
Proof. unfold bytes_of. rewrite length_map, length_seq. reflexivity. Qed.

Lemma nth_error_bytes_of z n j :
  nth_error (bytes_of z n) j = if (j <? n)%nat then Some (byte_of z (Z.of_nat j)) else None.
Proof. unfold bytes_of. rewrite nth_error_map, nth_error_seq. destruct (j <? n)%nat; reflexivity. Qed.

Lemma bytes_of_bytes z n : Forall is_byte (bytes_of z n).
Proof.
  apply Forall_nth_error. intros j x. rewrite nth_error_bytes_of. destruct (j <? n)%nat; [|discriminate].
  intros [= <-]. apply byte_of_range.
Qed.

Lemma nth_error_sym_bytes s : forall n i j,
  nth_error (sym_bytes s i n) j = if (j <? n)%nat then Some (BOf s (i + Z.of_nat j)) else None.
Proof.
  induction n as [|n IH]; intros i [|j]; cbn [sym_bytes nth_error]; try reflexivity.
  - rewrite Z.add_0_r. reflexivity.
  - rewrite IH. change (Datatypes.S j <? Datatypes.S n)%nat with (j <? n)%nat.
    destruct (j <? n)%nat; [|reflexivity]. do 2 f_equal. lia.
Qed.

Lemma length_sym_bytes s : forall n i, length (sym_bytes s i n) = n.
Proof. induction n; intros i; cbn [sym_bytes length]; [reflexivity | rewrite IHn; reflexivity]. Qed.

Lemma Forall2_repeat {X Y : Type} (P : X -> Y -> Prop) a b n : P a b -> Forall2 P (repeat a n) (repeat b n).
Proof. intros H. induction n; cbn; constructor; auto. Qed.

(** A flight adds a number to an address modulo 2^64. The sum does not
    wrap when the checker's offset stays inside the address space. *)
Lemma flight_addr base a n δ :
  0 <= base <= 2 ^ 62 -> 0 <= a + δ <= 2 ^ 62 -> (n - δ) mod 2 ^ 64 = 0 ->
  ((base + a) mod 2 ^ 64 + n) mod 2 ^ 64 = base + (a + δ).
Proof.
  intros Hb Ha Hn. rewrite Z.add_mod_idemp_l by lia. apply Z.mod_divide in Hn as [c Hc]; [|lia].
  replace (base + a + n) with (base + (a + δ) + c * 2 ^ 64) by lia. rewrite Z.mod_add by lia.
  apply Z.mod_small. lia.
Qed.

Lemma signed64_mod z : (z - signed64 z) mod 2 ^ 64 = 0.
Proof.
  unfold signed64. destruct (z <? 2 ^ 63); [rewrite Z.sub_diag; reflexivity|].
  replace (z - (z - 2 ^ 64)) with (2 ^ 64) by lia. reflexivity.
Qed.

Section mem.
Variable guard : Prop.
Variable ge : genv.
Variable gobjs : list name.
Local Abbreviation M := (M guard ge gobjs).
Local Abbreviation obj_ok := (obj_ok guard).
Local Abbreviation R := (R guard ge gobjs).

(** * Memory

    The checker reasons about the bytes it believes an object has, and
    the machine runs on a real memory. The two are connected by one
    predicate. The contents of an object hold in a memory when the
    object is live at its place and the memory has those bytes and
    those shadow slots there. *)

Definition holds (m : mem) (pl : place) (xs : list Z) (cs : list cap) : Prop :=
  live_at m (pl_base pl) (pl_reg pl) /\
  (forall j x, nth_error xs j = Some x ->
     pl_base pl + Z.of_nat j < r_end (pl_reg pl) /\ m_bytes m (pl_base pl + Z.of_nat j) = x) /\
  (forall j c, nth_error cs j = Some c ->
     pl_base pl + Z.of_nat j < r_end (pl_reg pl) /\ aux_holds m (pl_base pl + Z.of_nat j) c).

(** A memory agrees with the contents of a state when every owned
    object holds in it. *)
Definition mholds (B : list place) (X : cont) (m : mem) : Prop :=
  forall i pl xs cs, nth_error B i = Some pl -> nth_error X i = Some (Some (xs, cs)) -> holds m pl xs cs.

(** An object of a true state has a place and contents. *)
Lemma M_obj ρ B st e X o ob :
  M ρ B st e X -> get_obj st o = Some ob ->
  exists pl xs cs, nth_error B o = Some pl /\ nth_error X o = Some (Some (xs, cs)) /\
                   obj_ok ρ B pl ob xs cs /\ place_ok pl.
Proof using Type.
  intros (HB & _ & _ & _ & _ & (_ & _ & Ho)) E. unfold get_obj in E.
  destruct (nth_error (st_objs st) o) as [[ob'|]|] eqn:En; try discriminate. injection E as ->.
  destruct (Ho o ob En) as (pl & xs & cs & Hp & Hx & Hok). exists pl, xs, cs.
  split; [exact Hp|]. split; [exact Hx|]. split; [exact Hok|].
  rewrite Forall_forall in HB. apply HB. eapply nth_error_In. exact Hp.
Qed.

Lemma obj_ok_len ρ B pl ob xs cs :
  obj_ok ρ B pl ob xs cs -> Z.of_nat (length xs) = o_size ob /\ Z.of_nat (length cs) = o_size ob.
Proof using Type.
  intros (Hb & Ha & El & _). unfold o_size. apply Forall2_length in Hb. apply Forall2_length in Ha. lia.
Qed.

(** * Access

    A pointer is located in a place when it carries the capability of
    the place and the span it is about to access lies inside the live
    object there, at the alignment the access asks for. *)

Record located (m : mem) (pl : place) (q : ptr) (lo n al : Z) (r : rights) : Prop := {
  loc_cap : ptr_cap q = pl_cap pl;
  loc_live : live_at m (pl_base pl) (pl_reg pl);
  loc_addr : raw_address (ptr_addr q) lo = ptr_addr q + lo;
  loc_lo : pl_base pl <= ptr_addr q + lo;
  loc_hi : ptr_addr q + lo + n <= r_end (pl_reg pl);
  loc_small : r_end (pl_reg pl) <= 2 ^ 62;
  loc_al : (ptr_addr q + lo) mod al = 0;
  loc_rw : r = Write -> pl_ro pl = false }.

(** The machine's access check passes for a located pointer. *)
Lemma located_access m pl q lo n al r :
  located m pl q lo n al r -> access_res m (raw_address (ptr_addr q) lo) (ptr_cap q) n r al = Some ok.
Proof using Type.
  intros [Hc [Hr Hl] Ha H1 H2 _ H3 Hw]. rewrite Ha, Hc. unfold access_res, pl_cap, cap_access_res.
  assert (Hb : (pl_base pl <=? ptr_addr q + lo) && (ptr_addr q + lo + n <=? r_end (pl_reg pl)) = true).
  { apply andb_true_iff. split; [apply Z.leb_le | apply Z.leb_le]; assumption. }
  assert (Hal : aligned_res (ptr_addr q + lo) al = ok).
  { unfold aligned_res. rewrite H3. reflexivity. }
  destruct (pl_ro pl) eqn:Ero; rewrite Hr, Hb.
  - destruct r; [cbn [readonly_access_res]; rewrite Hal; reflexivity | discriminate (Hw eq_refl)].
  - rewrite Hal. reflexivity.
Qed.

Lemma mod_chain base oa al : base mod oa = 0 -> oa mod al = 0 -> 0 < al -> base mod al = 0.
Proof using Type.
  intros H1 H2 Hal. destruct (Z.eq_dec oa 0) as [->|Hne].
  - rewrite Z.mod_0_r in H1. subst. apply Z.mod_0_l. lia.
  - apply Z.mod_divide in H1; [|exact Hne]. apply Z.mod_divide in H2; [|lia].
    apply Z.mod_divide; [lia|]. eapply Z.divide_trans; eauto.
Qed.

(** The checker bounds the offset of a pointer into an owned object.
    The record [at_obj] collects what those bounds say about the real
    pointer. The pointer has an offset between the bounds, and it is
    located in every memory where the object is live. *)
Record at_obj (ρ : nat -> Z) (B : list place) (X : cont) (o : nat) (a : aint) (ob : aobj) (alo ahi : Z)
    (lo n al : Z) (r : rights) (w : word) (pl : place) (xs : list Z) (cs : list cap) : Prop := {
  ao_place : nth_error B o = Some pl;
  ao_cont : nth_error X o = Some (Some (xs, cs));
  ao_ok : obj_ok ρ B pl ob xs cs;
  ao_word : w = WPtr (mkPtr (pl_base pl + dint ρ a) (pl_cap pl));
  ao_rng : alo <= dint ρ a <= ahi;
  ao_base : 0 <= pl_base pl;
  ao_loc : forall m, live_at m (pl_base pl) (pl_reg pl) ->
             located m pl (mkPtr (pl_base pl + dint ρ a) (pl_cap pl)) lo n al r }.

(** A pointer into an owned object is located when the checker's
    bounds on its offset keep the span inside the object. *)
Lemma locate ρ B st e X o a ob alo ahi lo n al r w :
  M ρ B st e X -> wf_int (length (st_bnd st)) a -> dval ge ρ B (VP o a) w ->
  get_obj st o = Some ob -> rng st a = (alo, ahi) ->
  0 <= alo + lo -> ahi + lo + n <= o_size ob -> 0 <= n ->
  (r = Write -> o_ro ob = false) ->
  (al = 1 \/ (alo = ahi /\ (alo + lo) mod al = 0 /\ o_align ob mod al = 0 /\ 0 < al)) ->
  exists pl xs cs, at_obj ρ B X o a ob alo ahi lo n al r w pl xs cs.
Proof using Type.
  intros HM Wa Hv Eo Er H1 H2 Hn Hw Hal.
  destruct (M_obj _ _ _ _ _ _ _ HM Eo) as (pl & xs & cs & Hp & Hx & Hok & [Hb0 Hend]).
  pose proof (rng_sound guard ρ st a alo ahi (M_sat _ _ _ _ _ _ _ _ HM) Wa Er) as Ra.
  destruct Hv as (pl' & Hp' & ->). rewrite Hp in Hp'. injection Hp' as <-.
  destruct (obj_ok_len _ _ _ _ _ _ Hok) as [Lx _]. pose proof Hok as (_ & _ & _ & Hro & Hmod & Hfit).
  exists pl, xs, cs. constructor; try assumption; try reflexivity; try lia.
  intros m Hlive. constructor; cbn [ptr_addr ptr_cap]; try lia.
  - reflexivity.
  - exact Hlive.
  - unfold raw_address. apply Z.mod_small. lia.
  - destruct Hal as [->|(E & Hm & Ho & Hpos)]; [apply Z.mod_1_r|].
    replace (pl_base pl + dint ρ a + lo) with (pl_base pl + (alo + lo)) by lia.
    rewrite Z.add_mod by lia. rewrite Hm, (mod_chain _ _ _ Hmod Ho Hpos). apply Z.mod_0_l. lia.
  - intros Hr. rewrite Hro. exact (Hw Hr).
Qed.

(** * Checks *)

(** A check that the checker accepts passes on the machine. The
    pointer it was given is a pointer into an owned object, and the
    span of the check is located there. *)
Lemma acheck_sound ρ B st e X lo hi r al p w :
  M ρ B st e X -> wf_val (length (st_bnd st)) p -> dval ge ρ B p w ->
  acheck lo hi r al p st = true ->
  lo < hi /\ exists o a ob alo ahi pl xs cs, p = VP o a /\
    at_obj ρ B X o a ob alo ahi lo (hi - lo) al r w pl xs cs.
Proof using Type.
  intros HM Wp Hv. destruct p as [| | |o a| | |]; try discriminate. cbn [acheck wf_val] in *.
  destruct (get_obj st o) as [ob|] eqn:Eo; [|discriminate]. destruct (rng st a) as [alo ahi] eqn:Er.
  intros Hc. apply andb_true_iff in Hc as [Hc Hal]. apply andb_true_iff in Hc as [Hc Hrw].
  apply andb_true_iff in Hc as [Hc H3]. apply andb_true_iff in Hc as [H1 H2].
  apply Z.leb_le in H1, H2. apply Z.ltb_lt in H3.
  assert (Hw : r = Write -> o_ro ob = false).
  { intros ->. apply negb_true_iff in Hrw. exact Hrw. }
  assert (Ha : al = 1 \/ (alo = ahi /\ (alo + lo) mod al = 0 /\ o_align ob mod al = 0 /\ 0 < al)).
  { apply orb_true_iff in Hal as [H|H]; [left; apply Z.eqb_eq; exact H | right].
    apply andb_true_iff in H as [H H7]. apply andb_true_iff in H as [H H6]. apply andb_true_iff in H as [H4 H5].
    apply Z.eqb_eq in H4, H5, H6. apply Z.ltb_lt in H7. auto. }
  split; [exact H3|].
  destruct (locate ρ B st e X o a ob alo ahi lo (hi - lo) al r w HM Wp Hv Eo Er ltac:(lia) ltac:(lia)
              ltac:(lia) Hw Ha) as (pl & xs & cs & Hat).
  exists o, a, ob, alo, ahi, pl, xs, cs. auto.
Qed.

Lemma cap_eqb_same c : cap_eqb c c = true.
Proof using Type. destruct c; cbn; try reflexivity; try apply Z.eqb_refl; apply term_eqb_refl. Qed.

(** A full check, a renewed check and a half check all pass for a
    located pointer and return it. *)
Lemma check_op m pl q lo hi al r :
  located m pl q lo (hi - lo) al r ->
  op_res (Check lo hi r al) A [WPtr q] m = Some (OpRes (RVal (WPtr q)) m).
Proof using Type.
  intros H. cbn [op_res op_res_int fmt_of]. rewrite (located_access _ _ _ _ _ _ _ H). reflexivity.
Qed.

Lemma renew_op m pl q1 q lo hi al r :
  located m pl q lo (hi - lo) al r -> ptr_cap q1 = ptr_cap q ->
  op_res (Renew lo hi r al) A [WPtr q1; WPtr q] m = Some (OpRes (RVal (WPtr q)) m).
Proof using Type.
  intros H E. cbn [op_res op_res_int fmt_of]. rewrite E, cap_eqb_same, (located_access _ _ _ _ _ _ _ H).
  reflexivity.
Qed.

Lemma half_check_op m pl q1 q bd lo hi al r :
  located m pl q lo (hi - lo) al r -> lo < hi -> ptr_cap q1 = ptr_cap q ->
  op_res (HalfCheck bd lo hi r al) A [WPtr q1; WPtr q] m = Some (OpRes (RVal (WPtr q)) m).
Proof using Type.
  intros H Hlt E. cbn [op_res op_res_int fmt_of]. rewrite E, cap_eqb_same, (located_access _ _ _ _ _ _ _ H).
  destruct H as [Hc [Hr Hl] Ha H1 H2 Hs H3 Hw]. rewrite Ha, Hc. unfold half_passes, pl_cap.
  assert (Hb : half_bound bd (ptr_addr q + lo) (hi - lo) (pl_base pl) (r_end (pl_reg pl)) (r_life (pl_reg pl)) = true).
  { destruct bd; cbn [half_bound]; [apply Z.leb_le; lia|]. rewrite Hl.
    assert ((2 ^ 63 <=? ptr_addr q + lo) = false) as -> by (apply Z.leb_gt; lia). apply Z.leb_le. lia. }
  assert (Hm : ((ptr_addr q + lo) mod al =? 0) = true) by (apply Z.eqb_eq; exact H3).
  destruct (pl_ro pl) eqn:Ero; cbv beta zeta; rewrite Hr; cbv beta iota zeta; rewrite Hb, Hm.
  - destruct r; [reflexivity | discriminate (Hw eq_refl)].
  - rewrite andb_false_r. reflexivity.
Qed.

(** * Loads

    A load reads a window of an object's bytes. The checker returns an
    abstract integer for the number those bytes build, and sometimes it
    renames the bytes after a new symbol. The lemmas of this section
    show that the integer stands for the loaded number and that the
    renamed bytes still describe the same contents. *)

Lemma dbytes_bytes ρ bs xs : Forall2 (dbyte guard ρ) bs xs -> Forall is_byte xs.
Proof using Type. induction 1 as [|b x bs xs [H _] _ IH]; constructor; assumption. Qed.

(** Any bytes are described by unknown bytes. *)
Lemma dbyte_BR ρ ys : Forall is_byte ys -> Forall2 (dbyte guard ρ) (repeat BR (length ys)) ys.
Proof using Type. induction 1; cbn [length repeat]; constructor; [split; [assumption | exact I] | assumption]. Qed.

Lemma byte_rng_sound ρ st b x lo hi :
  sat guard ρ st -> wf_byte (length (st_bnd st)) b -> dbyte guard ρ b x -> byte_rng st b = (lo, hi) ->
  lo <= x <= hi.
Proof using Type.
  intros Hs Wb [Hx Hb]. destruct b as [z|s i|l h| |k|s key mask]; cbn [byte_rng]; try (intros [= <- <-]; lia).
  destruct (rng st (S s)) as [l h] eqn:Er. pose proof (rng_sound guard ρ st (S s) l h Hs Wb Er) as Rg. cbn [dint] in Rg.
  destruct (Z.eqb_spec l h) as [->|_].
  - intros [= <- <-]. replace (ρ s) with h in Hb by lia. lia.
  - destruct ((i =? 0) && (0 <=? l) && (h <? 256)) eqn:Eb; intros [= <- <-]; [|lia].
    apply andb_true_iff in Eb as [Eb H3]. apply andb_true_iff in Eb as [H1 H2].
    apply Z.eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. subst i x.
    unfold byte_of. change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r, Z.mod_small by lia. exact Rg.
Qed.

Lemma win_const_sound ρ ws xs z : win_const ws = Some z -> Forall2 (dbyte guard ρ) ws xs -> of_bytes' xs = z.
Proof using Type.
  intros E H. revert z E. induction H as [|b x ws xs [_ Hb] _ IH]; intros z; cbn [win_const of_bytes'].
  - intros [= <-]. reflexivity.
  - destruct b; try discriminate. destruct (win_const ws) as [r|]; [|discriminate]. intros [= <-].
    cbn in Hb. rewrite (IH r eq_refl), Hb. reflexivity.
Qed.

Lemma win_sym_sound ρ s ws xs : forall i, win_sym s i ws = true -> Forall2 (dbyte guard ρ) ws xs ->
  forall j x, nth_error xs j = Some x -> x = byte_of (ρ s) (i + Z.of_nat j).
Proof using Type.
  intros i E H. revert i E. induction H as [|b x ws xs [_ Hb] _ IH]; intros i E j y; [destruct j; discriminate|].
  cbn [win_sym] in E. destruct b as [|t i'| | | |]; try discriminate.
  apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
  apply Nat.eqb_eq in E1. apply Z.eqb_eq in E2. subst t i'. destruct j as [|j]; cbn [nth_error].
  - intros [= <-]. cbn in Hb. rewrite Z.add_0_r. exact Hb.
  - intros Ej. rewrite (IH (i + 1) E3 j y Ej). f_equal. lia.
Qed.

Lemma sym_bytes_sound ρ t xs : forall i,
  Forall is_byte xs -> (forall j x, nth_error xs j = Some x -> x = byte_of (ρ t) (i + Z.of_nat j)) ->
  Forall2 (dbyte guard ρ) (sym_bytes t i (length xs)) xs.
Proof using Type.
  induction xs as [|x xs IH]; intros i Hb H; cbn [sym_bytes length]; constructor.
  - split; [exact (Forall_inv Hb)|]. rewrite (H O x eq_refl). f_equal. cbn. lia.
  - apply IH; [exact (Forall_inv_tail Hb)|]. intros j y E. rewrite (H (Datatypes.S j) y E). f_equal. lia.
Qed.

Lemma sym_bytes_wf n t : forall k i, (t < n)%nat -> Forall (wf_byte n) (sym_bytes t i k).
Proof using Type. induction k; intros i Ht; cbn [sym_bytes]; constructor; auto. Qed.

(** A load of known bytes is correct when three things hold, and
    [load_post] states them. The new state is true under a valuation
    that extends the old one. The integer stands for the number that
    the bytes build. The bytes that the checker writes back describe
    the same contents. *)
Definition load_post (ρ : nat -> Z) (B : list place) (e : env) (X : cont) (st : astate) (xs : list Z)
    (res : aint * astate * option (list abyte)) : Prop :=
  let '(r, st1, back) := res in
  exists ρ', M ρ' B st1 e X /\ step ρ st ρ' st1 /\ wf_int (length (st_bnd st1)) r /\ dint ρ' r = of_bytes' xs /\
    match back with
    | Some bs => Forall (wf_byte (length (st_bnd st1))) bs /\ Forall2 (dbyte guard ρ') bs xs
    | None => True
    end.

Definition load_plain (st : astate) (w : Z) : aint * astate * option (list abyte) :=
  let (t, st') := fresh st 0 (2 ^ (8 * w) - 1) in (S t, st', Some (sym_bytes t 0 (Z.to_nat w))).

Lemma load_plain_sound ρ B st e X xs w :
  M ρ B st e X -> Forall is_byte xs -> Z.of_nat (length xs) = w -> load_post ρ B e X st xs (load_plain st w).
Proof using Type.
  intros HM Hb <-. unfold load_plain. destruct (fresh st 0 (2 ^ (8 * Z.of_nat (length xs)) - 1)) as [t st'] eqn:Ef.
  pose proof (of_bytes'_bound xs Hb) as Bd.
  destruct (fresh_sound _ _ _ ρ B st e X 0 (2 ^ (8 * Z.of_nat (length xs)) - 1) (of_bytes' xs) t st' HM ltac:(lia) Ef) as (ρ' & H1 & H2 & H3 & H4).
  exists ρ'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|].
  rewrite Nat2Z.id. split; [apply sym_bytes_wf; exact H3|]. apply sym_bytes_sound; [exact Hb|].
  intros j x E. rewrite H4, Z.add_0_l. symmetry. apply byte_of_of_bytes'; assumption.
Qed.

Definition flag_step (t : nat) (acc : astate * Z) (b : abyte) : astate * Z :=
  (match b with
   | BGuard k => if (0 <=? k) && (k <? 8) then add_flag (fst acc) t (FBit (8 * snd acc + k)) else fst acc
   | _ => fst acc
   end, snd acc + 1).

Lemma flag_fold ρ B e X t : forall ws st i,
  M ρ B st e X -> (t < length (st_bnd st))%nat -> 0 <= i ->
  (forall j k, nth_error ws j = Some (BGuard k) -> 0 <= k < 8 ->
     Z.testbit (ρ t) (8 * (i + Z.of_nat j) + k) = true -> guard) ->
  M ρ B (fst (fold_left (flag_step t) ws (st, i))) e X /\
  length (st_bnd (fst (fold_left (flag_step t) ws (st, i)))) = length (st_bnd st).
Proof using Type.
  induction ws as [|b ws IH]; intros st i HM Ht Hi H; cbn [fold_left fst]; [auto|].
  assert (H0 : M ρ B (fst (flag_step t (st, i) b)) e X /\
               length (st_bnd (fst (flag_step t (st, i) b))) = length (st_bnd st)).
  { unfold flag_step. cbn [fst snd]. destruct b as [| | | |k|]; try (split; [exact HM | reflexivity]).
    destruct ((0 <=? k) && (k <? 8)) eqn:Ek; [|split; [exact HM | reflexivity]].
    apply andb_true_iff in Ek as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
    split; [|reflexivity]. apply M_add_flag; [exact HM | exact Ht | exact I |]. cbn [dflag].
    intros Hb. apply (H O k eq_refl ltac:(lia)). rewrite <- Hb. f_equal. lia. }
  destruct H0 as [H1 H2]. set (st1 := fst (flag_step t (st, i) b)) in *.
  change (flag_step t (st, i) b) with (st1, i + 1).
  destruct (IH st1 (i + 1) H1 ltac:(lia) ltac:(lia)) as [H3 H4].
  { intros j k Ej Hk Hb. apply (H (Datatypes.S j) k Ej Hk). rewrite <- Hb. f_equal. lia. }
  split; [exact H3 | lia].
Qed.

(** A loaded integer may carry the flags of its bytes. *)
Lemma load_flags_sound ρ B st e X ws xs w t :
  M ρ B st e X -> (t < length (st_bnd st))%nat -> Forall (wf_byte (length (st_bnd st))) ws ->
  Forall2 (dbyte guard ρ) ws xs -> ρ t = of_bytes' xs ->
  M ρ B (load_flags ws w t st) e X /\ length (st_bnd (load_flags ws w t st)) = length (st_bnd st).
Proof using Type.
  intros HM Ht Ww Hd Et. pose proof (dbytes_bytes _ _ _ Hd) as Hb.
  destruct (flag_fold ρ B e X t ws st 0 HM Ht ltac:(lia)) as [H1 H2].
  { intros j k Ej Hk Hbit. pose proof (proj1 (Forall2_nth _ _ _) Hd) as [Hl Hp].
    destruct (nth_error xs j) as [x|] eqn:Ex.
    - destruct (Hp j _ x Ej Ex) as [_ Hg]. cbn in Hg. apply Hg.
      rewrite <- (byte_of_of_bytes' xs j x Hb Ex), testbit_byte_of by lia. rewrite <- Et, <- Hbit. f_equal; lia.
    - apply nth_error_None in Ex. assert (Hs : nth_error ws j <> None) by congruence.
      apply nth_error_Some in Hs. lia. }
  change (load_flags ws w t st) with
    (match ws with
     | BEnd u key mask :: _ =>
         if (0 <=? mask) && (mask <? 256)
         then add_flag (fst (fold_left (flag_step t) ws (st, 0))) t (FEnd u key mask)
         else fst (fold_left (flag_step t) ws (st, 0))
     | _ => fst (fold_left (flag_step t) ws (st, 0))
     end).
  destruct ws as [|b ws']; [exact (conj H1 H2)|]. destruct b as [| | | | |u key mask]; try exact (conj H1 H2).
  destruct ((0 <=? mask) && (mask <? 256)) eqn:Em; [|exact (conj H1 H2)].
  apply andb_true_iff in Em as [M1 M2]. apply Z.leb_le in M1. apply Z.ltb_lt in M2.
  split; [|exact H2]. pose proof (Forall_inv Ww) as Wu. cbn [wf_byte] in Wu.
  apply M_add_flag; [exact H1 | lia | cbn [wf_flag]; lia |].
  inversion Hd as [|? x ? xs' [Hx Hbe] Hd']; subst. cbn [dflag]. intros Hk. rewrite Et. cbn [of_bytes'].
  rewrite land_low_byte by (auto; lia). exact (Hbe Hk).
Qed.

Lemma load_sym_sound ρ B st e X s ws' xs w :
  M ρ B st e X -> Forall (wf_byte (length (st_bnd st))) (BOf s 0 :: ws') ->
  Forall2 (dbyte guard ρ) (BOf s 0 :: ws') xs -> Z.of_nat (length xs) = w ->
  load_post ρ B e X st xs
    (let (lo, hi) := rng st (S s) in
     if win_sym s 1 ws' && (0 <=? lo) && (hi <? 2 ^ (8 * w)) then (S s, st, None) else load_plain st w).
Proof using Type.
  intros HM Ww Hd Hw. pose proof (dbytes_bytes _ _ _ Hd) as Hb.
  destruct (rng st (S s)) as [lo hi] eqn:Er.
  destruct (win_sym s 1 ws' && (0 <=? lo) && (hi <? 2 ^ (8 * w))) eqn:Ec; [|apply load_plain_sound; assumption].
  apply andb_true_iff in Ec as [Ec H3]. apply andb_true_iff in Ec as [H1 H2].
  apply Z.leb_le in H2. apply Z.ltb_lt in H3. subst w.
  pose proof (Forall_inv Ww) as Ws. cbn [wf_byte] in Ws.
  pose proof (rng_sound guard ρ st (S s) lo hi (M_sat _ _ _ _ _ _ _ _ HM) Ws Er) as Rg. cbn [dint] in Rg.
  exists ρ. split; [exact HM|]. split; [apply step_refl|]. split; [exact Ws|]. split; [|exact I].
  cbn [dint]. destruct xs as [|x xs']; [inversion Hd|]. apply Forall2_cons_iff in Hd as [[_ Hx] Hd'].
  cbn [dbyte] in Hx.
  rewrite (of_bytes'_byte_of (ρ s) (x :: xs') 0 ltac:(lia)).
  - change (8 * 0) with 0. rewrite Z.pow_0_r, Z.div_1_r. symmetry. apply Z.mod_small. lia.
  - intros [|j] y; cbn [nth_error].
    + intros [= <-]. exact Hx.
    + intros E. rewrite (win_sym_sound ρ s ws' xs' 1 H1 Hd' j y E). f_equal. lia.
Qed.

Lemma load_one_sound ρ B st e X b xs w :
  M ρ B st e X -> Forall (wf_byte (length (st_bnd st))) [b] -> Forall2 (dbyte guard ρ) [b] xs ->
  load_post ρ B e X st xs
    (let (lo, hi) := byte_rng st b in
     let (t, st') := fresh st lo hi in
     (S t, load_flags [b] w t st', match b with BGuard _ | BEnd _ _ _ => None | _ => Some [BOf t 0] end)).
Proof using Type.
  intros HM Ww Hd. destruct xs as [|x [|x' xs']]; [inversion Hd | | apply Forall2_length in Hd; discriminate Hd].
  apply Forall2_cons_iff in Hd as [Hx _]. pose proof (Forall_inv Ww) as Wb.
  destruct (byte_rng st b) as [lo hi] eqn:Er.
  pose proof (byte_rng_sound ρ st b x lo hi (M_sat _ _ _ _ _ _ _ _ HM) Wb Hx Er) as Rg.
  destruct (fresh st lo hi) as [t st'] eqn:Ef.
  destruct (fresh_sound _ _ _ ρ B st e X lo hi x t st' HM Rg Ef) as (ρ' & H1 & H2 & H3 & H4).
  pose proof H2 as [Ha Hl].
  assert (Hd1 : Forall2 (dbyte guard ρ') [b] [x]).
  { constructor; [|constructor]. eapply dbyte_agree; eauto. }
  assert (Ww1 : Forall (wf_byte (length (st_bnd st'))) [b]).
  { constructor; [|constructor]. eapply wf_byte_mono; eauto. }
  assert (Et : ρ' t = of_bytes' [x]) by (cbn [of_bytes']; lia).
  destruct (load_flags_sound ρ' B st' e X [b] [x] w t H1 H3 Ww1 Hd1 Et) as [H5 H6].
  exists ρ'. split; [exact H5|]. split; [split; [exact Ha | lia]|]. split; [cbn [wf_int]; lia|].
  split; [cbn [dint]; exact Et|]. destruct Hx as [Hxb _].
  assert (Hback : Forall (wf_byte (length (st_bnd (load_flags [b] w t st')))) [BOf t 0] /\
                  Forall2 (dbyte guard ρ') [BOf t 0] [x]).
  { split; (constructor; [|constructor]); [cbn [wf_byte]; lia|].
    split; [exact Hxb|]. rewrite H4. symmetry. apply byte_of_small. exact Hxb. }
  destruct b; try exact Hback; exact I.
Qed.

Lemma load_gen_sound ρ B st e X ws xs w :
  M ρ B st e X -> Forall (wf_byte (length (st_bnd st))) ws -> Forall2 (dbyte guard ρ) ws xs ->
  Z.of_nat (length xs) = w ->
  load_post ρ B e X st xs
    (let (t, st') := fresh st 0 (2 ^ (8 * w) - 1) in
     if has_bx ws then (S t, load_flags ws w t st', None) else (S t, st', Some (sym_bytes t 0 (Z.to_nat w)))).
Proof using Type.
  intros HM Ww Hd Hw. pose proof (dbytes_bytes _ _ _ Hd) as Hb.
  destruct (has_bx ws) eqn:Eh; [|exact (load_plain_sound ρ B st e X xs w HM Hb Hw)].
  subst w. destruct (fresh st 0 (2 ^ (8 * Z.of_nat (length xs)) - 1)) as [t st'] eqn:Ef.
  pose proof (of_bytes'_bound xs Hb) as Bd.
  destruct (fresh_sound _ _ _ ρ B st e X 0 (2 ^ (8 * Z.of_nat (length xs)) - 1) (of_bytes' xs) t st' HM
              ltac:(lia) Ef) as (ρ' & H1 & H2 & H3 & H4).
  pose proof H2 as [Ha Hl].
  assert (Ww1 : Forall (wf_byte (length (st_bnd st'))) ws).
  { eapply Forall_impl; [|exact Ww]. intros b. apply wf_byte_mono. exact Hl. }
  assert (Hd1 : Forall2 (dbyte guard ρ') ws xs) by (eapply dbytes_agree; eauto).
  destruct (load_flags_sound ρ' B st' e X ws xs (Z.of_nat (length xs)) t H1 H3 Ww1 Hd1 H4) as [H5 H6].
  exists ρ'. split; [exact H5|]. split; [split; [exact Ha | lia]|]. split; [cbn [wf_int]; lia|].
  split; [exact H4 | exact I].
Qed.

(** A load at a known offset returns an integer that stands for the
    number in memory. *)
Lemma load_exact_sound ρ B st e X ws xs w :
  M ρ B st e X -> Forall (wf_byte (length (st_bnd st))) ws -> Forall2 (dbyte guard ρ) ws xs ->
  Z.of_nat (length xs) = w -> load_post ρ B e X st xs (load_exact st ws w).
Proof using Type.
  intros HM Ww Hd Hw. unfold load_exact. destruct (win_const ws) as [z|] eqn:Ec.
  - exists ρ. split; [exact HM|]. split; [apply step_refl|]. split; [exact I|]. split; [|exact I].
    cbn [dint]. symmetry. exact (win_const_sound ρ ws xs z Ec Hd).
  - destruct ws as [|b ws']; [discriminate Ec|].
    destruct b as [z|s i|l h| |k|s key mask]; try destruct i; destruct ws';
      first [exact (load_sym_sound ρ B st e X _ _ xs w HM Ww Hd Hw)
            | exact (load_one_sound ρ B st e X _ xs w HM Ww Hd)
            | exact (load_gen_sound ρ B st e X _ xs w HM Ww Hd Hw)].
Qed.

(** The extension that a load's type asks for gives the value that
    the checker binds. *)
Lemma load_ext_sound ρ B st e X t k a v st' u w :
  M ρ B st e X -> wf_int (length (st_bnd st)) a -> dint ρ a = u -> load_size t = Some w ->
  0 <= u < 2 ^ (8 * w) -> load_ext t k a st = Some (v, st') ->
  exists x, match t with LdNarrow n => extended n k u | _ => Some (WInt u) end = Some x /\
            R ρ B e X st st' v x.
Proof using Type.
  intros HM Wa Ea Es Hu. destruct t as [| | | |n]; cbn [load_ext load_size] in *; try discriminate.
  - intros [= <- <-]. exists (WInt u). split; [reflexivity|].
    apply R_same; [exact HM | exact Wa | cbn [dval]; congruence].
  - destruct (modulus_of k) as [md|] eqn:Em; [|discriminate].
    destruct (rng st a) as [lo hi] eqn:Er.
    pose proof (rng_sound guard ρ st a lo hi (M_sat _ _ _ _ _ _ _ _ HM) Wa Er) as Rg.
    assert (Hk : (k = W /\ md = 2 ^ 32) \/ (k = L /\ md = 2 ^ 64)).
    { destruct k; try discriminate; injection Em as <-; auto. }
    injection Es as <-. set (z := extension n u mod md).
    assert (Hx : extended n k u = Some (WInt z)).
    { unfold extended. destruct Hk as [[-> ->]|[-> ->]]; reflexivity. }
    exists (WInt z). split; [exact Hx|].
    match goal with H : (if ?c then _ else _) = _ |- _ => revert H; destruct c eqn:Ek end.
    + intros [= <- <-]. apply R_same; [exact HM | exact Wa|]. cbn [dval]. f_equal. rewrite Ea. subst z.
      exact (extension_keep n k md u hi Hk Hu ltac:(lia) Ek).
    + destruct (mk st 0 (md - 1)) as [r st1] eqn:Emk. intros [= <- <-].
      assert (Hz : 0 <= z <= md - 1).
      { subst z. assert (0 < md) by (destruct Hk as [[_ ->]|[_ ->]]; lia).
        pose proof (Z.mod_pos_bound (extension n u) md). lia. }
      destruct (mk_sound _ _ _ ρ B st e X 0 (md - 1) z r st1 HM Hz Emk) as (ρ' & H1 & H2 & H3 & H4).
      exists ρ'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. cbn [dval]. congruence.
Qed.

(** * Replacing an object

    A load may rename the bytes of an object, and a store changes its
    contents. In both cases one object of the state gets a new
    description, and the contents list changes at most at that object. *)
Lemma M_put_obj ρ B st e X X' o pl ob xs cs :
  M ρ B st e X -> nth_error B o = Some pl ->
  obj_ok ρ B pl ob xs cs -> wf_obj (length (st_bnd st)) (Some ob) ->
  length X' = length X -> nth_error X' o = Some (Some (xs, cs)) ->
  (forall i, i <> o -> nth_error X' i = nth_error X i) ->
  M ρ B (put_obj st o (Some ob)) e X'.
Proof using Type.
  intros (HB & HG & Hs & (We & Wf & Wl & Wo) & He & (L1 & L2 & Ho)) Hp Hok Wob EL Eo Eother.
  split; [exact HB|]. split; [exact HG|]. split; [exact Hs|]. split; [|split; [exact He|]].
  - split; [exact We|]. split; [exact Wf|]. split; [exact Wl|].
    cbn [put_obj set_objs st_objs st_bnd]. apply Forall_nth_error. intros i x. rewrite nth_error_list_set.
    destruct (Nat.eqb_spec i o) as [->|_].
    + destruct (nth_error (st_objs st) o); [intros [= <-]; exact Wob | discriminate].
    + intros E. rewrite Forall_nth_error in Wo. exact (Wo i x E).
  - cbn [put_obj set_objs st_objs]. split; [rewrite length_list_set; exact L1|]. split; [lia|].
    intros i ob0. rewrite nth_error_list_set. destruct (Nat.eqb_spec i o) as [->|Hne].
    + destruct (nth_error (st_objs st) o); [|discriminate]. intros [= <-]. exists pl, xs, cs. auto.
    + intros E. destruct (Ho i ob0 E) as (pl0 & xs0 & cs0 & H1 & H2 & H3). exists pl0, xs0, cs0.
      rewrite (Eother i Hne). auto.
Qed.

Lemma M_wf_obj ρ B st e X o ob :
  M ρ B st e X -> get_obj st o = Some ob -> Forall (wf_byte (length (st_bnd st))) (o_bytes ob).
Proof using Type.
  intros (_ & _ & _ & (_ & _ & _ & Wo) & _) E. unfold get_obj in E.
  destruct (nth_error (st_objs st) o) as [[ob'|]|] eqn:En; try discriminate. injection E as ->.
  rewrite Forall_nth_error in Wo. exact (Wo o (Some ob) En).
Qed.

(** The machine loads the number that a window of an object's bytes builds. *)
Lemma holds_window m pl xs cs k n :
  holds m pl xs cs -> 0 <= k -> 0 <= n -> k + n <= Z.of_nat (length xs) ->
  load_bytes m (pl_base pl + k) n = of_bytes' (window k n xs).
Proof using Type.
  intros (_ & Hb & _) Hk Hn Hl.
  rewrite <- (load_bytes_spec m (pl_base pl + k) (window k n xs)).
  - rewrite length_window by lia. rewrite Z2Nat.id by lia. reflexivity.
  - intros j x E. assert (Hj : (j < Z.to_nat n)%nat).
    { rewrite <- (length_window k n xs) by lia. apply nth_error_Some. congruence. }
    rewrite nth_error_window in E by lia. destruct (Hb _ _ E) as [_ <-]. f_equal. lia.
Qed.

(** A raw load through a located pointer returns the loaded number,
    extended as the load's type says. *)
Lemma raw_load_op m pl q t k off n u x :
  load_size t = Some n -> located m pl q off n 1 Read ->
  load_bytes m (ptr_addr q + off) n = u ->
  match t with LdNarrow nn => extended nn k u | _ => Some (WInt u) end = Some x ->
  op_res (RawLoad t off) k [WPtr q] m = Some (OpRes (RVal x) m).
Proof using Type.
  intros Es Hloc Hu Hx.
  assert (E : op_res (RawLoad t off) k [WPtr q] m = op_res_int (RawLoad t off) k [WPtr q] m)
    by (destruct k; reflexivity).
  rewrite E. cbn [op_res_int]. unfold int_load_res. pose proof (located_access _ _ _ _ _ _ _ Hloc) as Ha.
  pose proof (loc_addr _ _ _ _ _ _ _ Hloc) as Hr.
  destruct t as [| | | |nn]; cbn [load_size] in Es; try discriminate; injection Es as <-; cbv beta iota zeta;
    rewrite Ha; cbv beta iota zeta; rewrite Hr, Hu.
  - injection Hx as <-. reflexivity.
  - rewrite Hx. reflexivity.
Qed.

(** A load that the checker accepts reads an owned object. The machine
    returns a word that the bound value describes. *)
Lemma aload_sound ρ B st e X t k off p w v st' :
  M ρ B st e X -> wf_val (length (st_bnd st)) p -> dval ge ρ B p w ->
  aload t k off p st = Some (v, st') ->
  exists o pl xs cs q x, nth_error B o = Some pl /\ nth_error X o = Some (Some (xs, cs)) /\ w = WPtr q /\
    (forall m, holds m pl xs cs -> op_res (RawLoad t off) k [WPtr q] m = Some (OpRes (RVal x) m)) /\
    R ρ B e X st st' v x.
Proof using Type.
  intros HM Wp Hv. destruct p as [| | |o a| | |]; try discriminate. cbn [aload wf_val] in *.
  destruct (get_obj st o) as [ob|] eqn:Eo; [|discriminate].
  destruct (load_size t) as [n|] eqn:Es; [|discriminate].
  destruct (rng st a) as [lo hi] eqn:Er.
  destruct ((0 <=? lo + off) && (hi + off + n <=? o_size ob)) eqn:Eb; [|discriminate].
  apply andb_true_iff in Eb as [H1 H2]. apply Z.leb_le in H1, H2.
  assert (Hn : 0 < n) by (destruct t as [| | | |[]]; inversion Es; lia).
  destruct (locate ρ B st e X o a ob lo hi off n 1 Read w HM Wp Hv Eo Er H1 H2 ltac:(lia)
              ltac:(discriminate) (or_introl eq_refl)) as (pl & xs & cs & [Hp Hx Hok -> Ra Hb0 Hloc]).
  set (d := dint ρ a) in *. set (q := mkPtr (pl_base pl + d) (pl_cap pl)) in *.
  destruct (obj_ok_len _ _ _ _ _ _ Hok) as [Lx _]. pose proof Hok as (Hbs & Hrest).
  pose proof (dbytes_bytes _ _ _ Hbs) as Hxb.
  set (win := window (d + off) n xs).
  assert (Hlen : Z.of_nat (length win) = n) by (unfold win; rewrite length_window by lia; lia).
  assert (Hwb : Forall is_byte win) by (apply Forall_window; exact Hxb).
  pose proof (of_bytes'_bound win Hwb) as Bd. rewrite Hlen in Bd.
  assert (Hop : forall x, match t with LdNarrow nn => extended nn k (of_bytes' win) | _ => Some (WInt (of_bytes' win)) end = Some x ->
                forall m, holds m pl xs cs -> op_res (RawLoad t off) k [WPtr q] m = Some (OpRes (RVal x) m)).
  { intros x Hx' m Hm. apply (raw_load_op m pl q t k off n (of_bytes' win) x Es); [exact (Hloc m (proj1 Hm)) | | exact Hx'].
    cbn [q ptr_addr]. rewrite <- Z.add_assoc. apply (holds_window m pl xs cs (d + off) n Hm); lia. }
  assert (Hfin : forall ρ1 st2 r, M ρ1 B st2 e X -> step ρ st ρ1 st2 -> wf_int (length (st_bnd st2)) r ->
            dint ρ1 r = of_bytes' win -> load_ext t k r st2 = Some (v, st') ->
            exists x, (forall m, holds m pl xs cs -> op_res (RawLoad t off) k [WPtr q] m = Some (OpRes (RVal x) m)) /\
                      R ρ B e X st st' v x).
  { intros ρ1 st2 r HM1 S1 Wr Er1 El.
    destruct (load_ext_sound ρ1 B st2 e X t k r v st' (of_bytes' win) n HM1 Wr Er1 Es Bd El) as (x & Hx' & HR).
    exists x. split; [exact (Hop x Hx') | exact (R_step _ _ _ _ _ _ _ _ _ _ _ _ _ S1 HR)]. }
  intros Hl. assert (Hgoal : exists x, (forall m, holds m pl xs cs ->
                     op_res (RawLoad t off) k [WPtr q] m = Some (OpRes (RVal x) m)) /\ R ρ B e X st st' v x).
  2:{ destruct Hgoal as (x & G1 & G2). exists o, pl, xs, cs, q, x. auto. }
  destruct (Z.eqb_spec lo hi) as [Elh|_].
  - assert (Ed : lo = d) by lia. assert (Rh : d <= hi) by lia. clear Elh Ra. subst lo. pose proof (M_wf_obj _ _ _ _ _ _ _ HM Eo) as Wob.
    assert (Hpost := load_exact_sound ρ B st e X (window (d + off) n (o_bytes ob)) win n HM
                       (Forall_window _ _ _ _ Wob) (Forall2_window _ _ _ _ _ Hbs) Hlen).
    destruct (load_exact st (window (d + off) n (o_bytes ob)) n) as [[r st1] back].
    destruct Hpost as (ρ1 & HM1 & S1 & Wr & Er1 & Hback). destruct back as [bs|].
    + destruct Hback as [Wbs Hdb]. pose proof (Forall2_length Hdb) as Lb.
      pose proof (proj1 S1) as Ha1. pose proof (proj2 S1) as Hl1.
      assert (Lbs : Z.of_nat (length bs) = n) by lia.
      refine (Hfin ρ1 (put_obj st1 o _) r _ S1 Wr Er1 Hl).
      apply (M_put_obj ρ1 B st1 e X X o pl _ xs cs HM1 Hp); try assumption; try reflexivity.
      * destruct Hrest as (Hax & Hla & Hro & Hmod & Hfit). unfold AbsDen.obj_ok. cbn [o_bytes o_aux o_ro o_align].
        split; [|split; [exact Hax|split; [|split; [exact Hro|split; [exact Hmod|]]]]].
        -- apply Forall2_splice; try lia.
           ++ unfold o_size in *. apply Forall2_length in Hbs. lia.
           ++ eapply dbytes_agree; [exact Ha1 | exact Wob | exact Hbs].
           ++ rewrite Lbs. exact Hdb.
        -- rewrite length_splice; [exact Hla | lia | unfold o_size in *; lia].
        -- unfold o_size in *. cbn [o_bytes]. rewrite length_splice; [exact Hfit | lia | lia].
      * cbn [wf_obj o_bytes]. apply Forall_splice; [exact Wbs|].
        eapply Forall_impl; [|exact Wob]. intros b. apply wf_byte_mono. exact Hl1.
    + exact (Hfin ρ1 st1 r HM1 S1 Wr Er1 Hl).
  - destruct (fresh st 0 (2 ^ (8 * n) - 1)) as [r st1] eqn:Ef.
    destruct (fresh_sound _ _ _ ρ B st e X 0 (2 ^ (8 * n) - 1) (of_bytes' win) r st1 HM ltac:(lia) Ef)
      as (ρ1 & HM1 & S1 & Wr & Er1).
    exact (Hfin ρ1 st1 (S r) HM1 S1 Wr Er1 Hl).
Qed.

(** * Stores

    A store writes the low bytes of a number into an owned object. The
    lemmas of this section say what the machine does and what the
    contents of the object are afterwards. *)

(** A raw store through a located pointer writes the bytes. *)
Lemma raw_store_op m pl q w off n z :
  store_width w = Some n -> located m pl q off n 1 Write ->
  store_res w m (raw_address (ptr_addr q) off) (ptr_cap q) (WInt z) =
  Some (ok, store_bytes m (ptr_addr q + off) n z).
Proof using Type.
  intros Es Hloc. pose proof (located_access _ _ _ _ _ _ _ Hloc) as Ha.
  pose proof (loc_addr _ _ _ _ _ _ _ Hloc) as Hr.
  destruct w; cbn [store_width] in Es; try discriminate; injection Es as <-;
    cbv beta iota zeta delta [store_res width_bytes]; rewrite Ha; cbv beta iota; rewrite Hr; reflexivity.
Qed.

(** After a store of [n] bytes at offset [k], the object holds its old
    bytes with the new ones spliced in. *)
Lemma holds_store_bytes m pl xs cs k n z :
  holds m pl xs cs -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length xs) ->
  holds (store_bytes m (pl_base pl + k) (Z.of_nat n) z) pl (splice k (bytes_of z n) xs) cs.
Proof using Type.
  intros (Hl & Hb & Ha) Hk Hn. split; [exact Hl|]. split; [|exact Ha].
  intros j x. rewrite nth_error_splice by (rewrite ?length_bytes_of; lia). rewrite length_bytes_of.
  destruct ((Z.to_nat k <=? j)%nat && (j <? Z.to_nat k + n)%nat) eqn:Ej.
  - apply andb_true_iff in Ej as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    rewrite nth_error_bytes_of. destruct (Nat.ltb_spec (j - Z.to_nat k) n); [|lia]. intros [= <-].
    assert (Hin : exists y, nth_error xs j = Some y).
    { destruct (nth_error xs j) eqn:E; [eauto|]. apply nth_error_None in E. lia. }
    destruct Hin as [y Ey]. split; [exact (proj1 (Hb j y Ey))|].
    unfold store_bytes; cbn [m_bytes].
    replace ((pl_base pl + k <=? pl_base pl + Z.of_nat j) &&
             (pl_base pl + Z.of_nat j <? pl_base pl + k + Z.of_nat n)) with true
      by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    f_equal. lia.
  - intros E. destruct (Hb j x E) as [H1 H2]. split; [exact H1|]. rewrite store_bytes_other; [exact H2|].
    apply andb_false_iff in Ej. destruct Ej as [E1|E2]; [apply Nat.leb_gt in E1 | apply Nat.ltb_ge in E2]; lia.
Qed.

(** The bytes that the checker writes for a stored integer describe
    the bytes of the number it stands for. *)
Lemma aint_bytes_sound ρ x n : Forall2 (dbyte guard ρ) (aint_bytes x n) (bytes_of (dint ρ x) n).
Proof using Type.
  apply Forall2_nth. split.
  - rewrite length_bytes_of. destruct x; cbn [aint_bytes]; [rewrite length_map, length_seq | rewrite length_sym_bytes]; reflexivity.
  - intros j a b Ea. rewrite nth_error_bytes_of. destruct (Nat.ltb_spec j n) as [Hj|]; [|discriminate]. intros [= <-].
    split; [apply byte_of_range|]. destruct x as [c|s]; cbn [aint_bytes dint] in *.
    + rewrite nth_error_map, nth_error_seq in Ea. destruct (Nat.ltb_spec j n); [|lia]. cbn in Ea.
      injection Ea as <-. reflexivity.
    + rewrite nth_error_sym_bytes in Ea. destruct (Nat.ltb_spec j n); [|lia]. injection Ea as <-.
      cbn. reflexivity.
Qed.

Lemma aint_bytes_wf N x n : wf_int N x -> Forall (wf_byte N) (aint_bytes x n).
Proof using Type.
  intros Wx. destruct x as [c|s]; cbn [aint_bytes]; [|apply sym_bytes_wf; exact Wx].
  apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (i & <- & _). exact I.
Qed.

(** The record [stored] says what a store that the checker accepts
    does. The pointer [q] points [k] bytes into the object at place
    [pl], and the store writes the [n] low bytes of [z] there. The
    state after the store is true of the contents with those bytes
    spliced in. *)
Record stored (ρ : nat -> Z) (B : list place) (e : env) (X : cont) (st st' : astate) (off : Z)
    (wv wp : word) (o : nat) (pl : place) (xs : list Z) (cs : list cap) (q : ptr) (z k : Z) (n : nat) : Prop := {
  sd_place : nth_error B o = Some pl;
  sd_cont : nth_error X o = Some (Some (xs, cs));
  sd_ptr : wp = WPtr q;
  sd_val : wv = WInt z;
  sd_k : 0 <= k;
  sd_n : k + Z.of_nat n <= Z.of_nat (length xs);
  sd_addr : ptr_addr q + off = pl_base pl + k;
  sd_loc : forall m, live_at m (pl_base pl) (pl_reg pl) -> located m pl q off (Z.of_nat n) 1 Write;
  sd_after : exists ρ', M ρ' B st' e (list_set o (Some (splice k (bytes_of z n) xs, cs)) X) /\ step ρ st ρ' st' }.

Lemma astore_sound ρ B st e X w off v p wv wp st' :
  M ρ B st e X -> wf_val (length (st_bnd st)) v -> wf_val (length (st_bnd st)) p ->
  dval ge ρ B v wv -> dval ge ρ B p wp -> astore w off v p st = Some st' ->
  exists o pl xs cs q z k n, store_width w = Some (Z.of_nat n) /\
    stored ρ B e X st st' off wv wp o pl xs cs q z k n.
Proof using Type.
  intros HM Wv Wp Hv Hp. destruct p as [| | |o a| | |]; try discriminate. cbn [astore wf_val] in *.
  destruct (get_obj st o) as [ob|] eqn:Eo; [|discriminate].
  destruct (store_width w) as [n|] eqn:Es; [|discriminate].
  destruct (rng st a) as [lo hi] eqn:Er.
  destruct (negb (o_ro ob) && (0 <=? lo + off) && (hi + off + n <=? o_size ob)) eqn:Eb; [|discriminate].
  apply andb_true_iff in Eb as [Eb H2]. apply andb_true_iff in Eb as [Hro H1]. apply negb_true_iff in Hro.
  apply Z.leb_le in H1, H2.
  assert (Hn : 0 < n) by (destruct w; inversion Es; lia).
  destruct (locate ρ B st e X o a ob lo hi off n 1 Write wp HM Wp Hp Eo Er H1 H2 ltac:(lia) (fun _ => Hro)
              (or_introl eq_refl)) as (pl & xs & cs & [Hpl Hx Hok -> Ra Hb0 Hloc]).
  destruct (as_int v st) as [x0 st1] eqn:Ea.
  destruct (as_int_sound guard ge gobjs ρ B st e X v wv x0 st1 HM Wv Hv Ea) as (ρ1 & HM1 & S1 & Wx & Dx).
  destruct x0 as [x| | | | | |]; try discriminate. intros [= <-]. cbn [dval wf_val] in Dx, Wx.
  set (d := dint ρ a) in *. set (z := dint ρ1 x) in *. set (nn := Z.to_nat n).
  assert (En : Z.of_nat nn = n) by (unfold nn; lia).
  destruct (obj_ok_len _ _ _ _ _ _ Hok) as [Lx Lc]. pose proof Hok as (Hbs & Hax & Hla & Hrob & Hmod & Hfit).
  pose proof (proj1 S1) as Ha1. pose proof (proj2 S1) as Hl1.
  pose proof (M_wf_obj _ _ _ _ _ _ _ HM Eo) as Wob.
  assert (Hbs1 : Forall2 (dbyte guard ρ1) (o_bytes ob) xs) by (eapply dbytes_agree; [exact Ha1 | exact Wob | exact Hbs]).
  assert (Wob1 : Forall (wf_byte (length (st_bnd st1))) (o_bytes ob)).
  { eapply Forall_impl; [|exact Wob]. intros b. apply wf_byte_mono. exact Hl1. }
  pose proof (Forall2_length Hbs) as Lbs.
  exists o, pl, xs, cs, (mkPtr (pl_base pl + d) (pl_cap pl)), z, (d + off), nn. rewrite En. split; [reflexivity|].
  constructor; cbn [ptr_addr]; try assumption; try reflexivity; try lia; [rewrite En; exact Hloc|].
  exists ρ1. split; [|exact S1].
  set (xs' := splice (d + off) (bytes_of z nn) xs).
  assert (Lxs' : length xs' = length xs) by (unfold xs'; apply length_splice; rewrite ?length_bytes_of; lia).
  eapply (M_put_obj ρ1 B st1 e X _ o pl _ xs' cs HM1 Hpl).
  - unfold AbsDen.obj_ok. cbn [o_bytes o_aux o_ro o_align]. unfold o_size in *.
    assert (Hd : Forall2 (dbyte guard ρ1)
              (if lo =? hi then splice (lo + off) (aint_bytes x nn) (o_bytes ob)
               else splice (lo + off) (repeat BR (Z.to_nat (hi - lo + n))) (o_bytes ob)) xs').
    { destruct (Z.eqb_spec lo hi) as [Elh|Hne].
      - replace (lo + off) with (d + off) by lia. apply Forall2_splice2; [exact Hbs1 | apply aint_bytes_sound].
      - apply Forall2_nth. split; [rewrite length_splice by (rewrite ?repeat_length; lia); lia|].
        intros j b y. rewrite nth_error_splice by (rewrite ?repeat_length; lia). rewrite repeat_length.
        unfold xs'. rewrite nth_error_splice by (rewrite ?length_bytes_of; lia). rewrite length_bytes_of.
        destruct ((Z.to_nat (lo + off) <=? j)%nat && (j <? Z.to_nat (lo + off) + Z.to_nat (hi - lo + n))%nat) eqn:Ej.
        + intros Eb Ey. apply andb_true_iff in Ej as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
          rewrite nth_error_repeat in Eb by lia. injection Eb as <-. split; [|exact I].
          destruct ((Z.to_nat (d + off) <=? j)%nat && (j <? Z.to_nat (d + off) + nn)%nat).
          * rewrite nth_error_bytes_of in Ey. destruct (_ <? _)%nat; [|discriminate]. injection Ey as <-.
            apply byte_of_range.
          * pose proof (dbytes_bytes _ _ _ Hbs1) as Hxb. rewrite Forall_nth_error in Hxb. exact (Hxb j y Ey).
        + intros Eb. apply andb_false_iff in Ej.
          replace ((Z.to_nat (d + off) <=? j)%nat && (j <? Z.to_nat (d + off) + nn)%nat) with false.
          * apply Forall2_nth in Hbs1 as [_ Hp1]. exact (Hp1 j b y Eb).
          * symmetry. apply andb_false_iff.
            destruct Ej as [E1|E2]; [left; apply Nat.leb_gt in E1; apply Nat.leb_gt | right; apply Nat.ltb_ge in E2; apply Nat.ltb_ge]; lia. }
    pose proof (Forall2_length Hd) as Ld.
    split; [exact Hd|]. split; [exact Hax|]. split; [lia|]. split; [exact Hrob|]. split; [exact Hmod|].
    cbn [o_bytes]. lia.
  - cbn [wf_obj o_bytes]. destruct (lo =? hi); apply Forall_splice; try exact Wob1.
    + apply aint_bytes_wf. exact Wx.
    + apply Forall_forall. intros b Hb. apply repeat_spec in Hb. subst b. exact I.
  - apply length_list_set.
  - rewrite nth_error_list_set, Nat.eqb_refl, Hx. reflexivity.
  - intros i Hi. rewrite nth_error_list_set. destruct (Nat.eqb_spec i o); [contradiction | reflexivity].
Qed.

(** * Pointer stores

    A pointer store writes the eight address bytes and puts the
    pointer's capability in the shadow slot of the first byte. *)

Lemma holds_store_aux m pl xs cs k c :
  holds m pl xs cs -> 0 <= k < Z.of_nat (length cs) ->
  holds (store_aux m (pl_base pl + k) c) pl xs (splice k [c] cs).
Proof using Type.
  intros (Hl & Hb & Ha) Hk. split; [exact Hl|]. split; [exact Hb|].
  intros j c0. rewrite nth_error_splice by (cbn [length]; lia). cbn [length].
  destruct ((Z.to_nat k <=? j)%nat && (j <? Z.to_nat k + 1)%nat) eqn:Ej.
  - apply andb_true_iff in Ej as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    assert (Ejk : j = Z.to_nat k) by lia. subst j. rewrite Nat.sub_diag. cbn [nth_error]. intros [= <-].
    destruct (nth_error cs (Z.to_nat k)) as [c1|] eqn:E; [|apply nth_error_None in E; lia].
    split; [exact (proj1 (Ha _ _ E))|]. left. rewrite Z2Nat.id by lia. cbn [store_aux m_aux].
    rewrite Z.eqb_refl. reflexivity.
  - intros E. destruct (Ha j c0 E) as [H1 H2]. split; [exact H1|]. unfold aux_holds in *.
    cbn [store_aux m_aux m_regions].
    replace (pl_base pl + Z.of_nat j =? pl_base pl + k) with false; [exact H2|]. symmetry. apply Z.eqb_neq.
    apply andb_false_iff in Ej. destruct Ej as [E1|E2]; [apply Nat.leb_gt in E1 | apply Nat.ltb_ge in E2]; lia.
Qed.

Lemma holds_store_ptr m pl xs cs k xp :
  holds m pl xs cs -> 0 <= k -> k + 8 <= Z.of_nat (length xs) -> k < Z.of_nat (length cs) ->
  holds (store_bytes (store_aux m (pl_base pl + k) (ptr_cap xp)) (pl_base pl + k) 8 (ptr_addr xp)) pl
    (splice k (bytes_of (ptr_addr xp) 8) xs) (splice k [ptr_cap xp] cs).
Proof using Type.
  intros H Hk Hx Hc. apply (holds_store_bytes _ pl xs _ k 8 (ptr_addr xp)); [|exact Hk | exact Hx].
  apply holds_store_aux; [exact H | lia].
Qed.

(** The record [stored_ptr] says what a pointer store that the checker
    accepts does. The pointer [q] points [k] bytes into the object at
    place [pl], and the store writes the pointer [xp] there. *)
Record stored_ptr (ρ : nat -> Z) (B : list place) (e : env) (X : cont) (st' : astate) (off : Z)
    (wv wp : word) (o : nat) (pl : place) (xs : list Z) (cs : list cap) (q xp : ptr) (k : Z) : Prop := {
  ps_place : nth_error B o = Some pl;
  ps_cont : nth_error X o = Some (Some (xs, cs));
  ps_ptr : wp = WPtr q;
  ps_val : wv = WPtr xp;
  ps_k : 0 <= k;
  ps_n : k + 8 <= Z.of_nat (length xs);
  ps_c : k < Z.of_nat (length cs);
  ps_addr : ptr_addr q + off = pl_base pl + k;
  ps_loc : forall m, live_at m (pl_base pl) (pl_reg pl) -> located m pl q off 8 8 Write;
  ps_after : M ρ B st' e (list_set o (Some (splice k (bytes_of (ptr_addr xp) 8) xs, splice k [ptr_cap xp] cs)) X) }.

Lemma ptr_aux_sound ρ B v w ax : ptr_aux v = Some ax -> dval ge ρ B v w -> exists xp, w = WPtr xp /\ daux B ax (ptr_cap xp).
Proof using Type.
  destruct v; cbn [ptr_aux dval]; try discriminate; intros [= <-].
  - intros (x & Hx & ->). eexists. split; [reflexivity|]. cbn. eauto.
  - intros ->. eexists. split; reflexivity.
  - intros (p & ->). exists p. split; [reflexivity | exact I].
  - intros (p & -> & _). exists p. split; [reflexivity | exact I].
Qed.

Lemma astore_ptr_sound ρ B st e X off v p wv wp st' :
  M ρ B st e X -> wf_val (length (st_bnd st)) p -> dval ge ρ B v wv -> dval ge ρ B p wp ->
  astore_ptr off v p st = Some st' ->
  exists o pl xs cs q xp k, stored_ptr ρ B e X st' off wv wp o pl xs cs q xp k.
Proof using Type.
  intros HM Wp Hv Hp. destruct p as [| | |o a| | |]; try discriminate. cbn [astore_ptr wf_val] in *.
  destruct (get_obj st o) as [ob|] eqn:Eo; [|discriminate].
  destruct (ptr_aux v) as [ax|] eqn:Ex; [|discriminate].
  destruct (rng st a) as [lo hi] eqn:Er.
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c eqn:Eb end; [|discriminate].
  apply andb_true_iff in Eb as [Eb H6]. apply andb_true_iff in Eb as [Eb H5]. apply andb_true_iff in Eb as [Eb H4].
  apply andb_true_iff in Eb as [Eb H3]. apply andb_true_iff in Eb as [Hro H2]. apply negb_true_iff in Hro.
  apply Z.eqb_eq in H2, H5, H6. apply Z.leb_le in H3, H4. intros [= <-].
  assert (H7 : hi + off + 8 <= o_size ob) by lia. assert (H8 : 0 < 8) by lia.
  destruct (locate ρ B st e X o a ob lo hi off 8 8 Write wp HM Wp Hp Eo Er H3 H7 ltac:(lia) (fun _ => Hro)
              (or_intror (conj H2 (conj H5 (conj H6 H8))))) as (pl & xs & cs & [Hpl Hx Hok -> Ra Hb0 Hloc]).
  destruct (ptr_aux_sound ρ B v wv ax Ex Hv) as (xp & -> & Hax).
  set (d := dint ρ a) in *. assert (Ed : lo = d) by lia.
  destruct (obj_ok_len _ _ _ _ _ _ Hok) as [Lx Lc]. pose proof Hok as (Hbs & Hxs & Hla & Hrob & Hmod & Hfit).
  pose proof (M_wf_obj _ _ _ _ _ _ _ HM Eo) as Wob. unfold o_size in *.
  pose proof (Forall2_length Hbs) as Lbs. pose proof (Forall2_length Hxs) as Lxs.
  exists o, pl, xs, cs, (mkPtr (pl_base pl + d) (pl_cap pl)), xp, (d + off).
  constructor; cbn [ptr_addr]; try assumption; try reflexivity; try lia.
  rewrite Ed. eapply (M_put_obj ρ B st e X _ o pl _ (splice (d + off) (bytes_of (ptr_addr xp) 8) xs)
                        (splice (d + off) [ptr_cap xp] cs) HM Hpl).
  - unfold AbsDen.obj_ok. cbn [o_bytes o_aux o_ro o_align].
    split; [apply Forall2_splice2; [exact Hbs|]|].
    { exact (dbyte_BR ρ (bytes_of (ptr_addr xp) 8) (bytes_of_bytes _ _)). }
    split; [apply Forall2_splice2; [exact Hxs | constructor; [exact Hax | constructor]]|].
    split; [rewrite !length_splice by (cbn [length]; lia); exact Hla|].
    split; [exact Hrob|]. split; [exact Hmod|]. unfold o_size. cbn [o_bytes].
    rewrite length_splice by (cbn [length]; lia). exact Hfit.
  - cbn [wf_obj o_bytes]. apply Forall_splice; [|exact Wob].
    repeat constructor.
  - apply length_list_set.
  - rewrite nth_error_list_set, Nat.eqb_refl, Hx. reflexivity.
  - intros i Hi. rewrite nth_error_list_set. destruct (Nat.eqb_spec i o); [contradiction | reflexivity].
Qed.

(** * Pointer loads

    A pointer load returns the address in the eight bytes and the
    capability in the shadow slot. The collector may rewrite the slot
    of a freed object, so the checker only accepts a slot that holds
    no capability or the capability of an object the state owns. *)
Lemma aload_ptr_sound ρ B st e X off p w v st' :
  M ρ B st e X -> wf_val (length (st_bnd st)) p -> dval ge ρ B p w ->
  aload_ptr off p st = Some (v, st') ->
  v = VA /\ st' = st /\ exists q x, w = WPtr q /\
    forall m, mholds B X m ->
      op_res (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P [WPtr q] m = Some (OpRes (RVal (WPtr x)) m).
Proof using Type.
  intros HM Wp Hp. destruct p as [| | |o a| | |]; try discriminate. cbn [aload_ptr wf_val] in *.
  destruct (get_obj st o) as [ob|] eqn:Eo; [|discriminate].
  destruct (rng st a) as [lo hi] eqn:Er.
  match goal with |- (if ?c then _ else _) = _ -> _ => destruct c eqn:Eb end; [|discriminate].
  apply andb_true_iff in Eb as [Eb H6]. apply andb_true_iff in Eb as [Eb H5]. apply andb_true_iff in Eb as [Eb H4].
  apply andb_true_iff in Eb as [H2 H3]. apply Z.eqb_eq in H2, H5, H6. apply Z.leb_le in H3, H4.
  assert (H7 : hi + off + 8 <= o_size ob) by lia. assert (H8 : 0 < 8) by lia.
  destruct (locate ρ B st e X o a ob lo hi off 8 8 Read w HM Wp Hp Eo Er H3 H7 ltac:(lia)
              ltac:(discriminate) (or_intror (conj H2 (conj H5 (conj H6 H8)))))
    as (pl & xs & cs & [Hpl Hx Hok -> Ra Hb0 Hloc]).
  set (d := dint ρ a) in *. assert (Ed : lo = d) by lia. assert (Ed' : hi = d) by lia. clear H2 Ra. subst lo hi.
  destruct (obj_ok_len _ _ _ _ _ _ Hok) as [Lx Lc]. pose proof Hok as (Hbs & Hxs & Hla & _). unfold o_size in *.
  set (ax := nth (Z.to_nat (d + off)) (o_aux ob) XAny).
  assert (Eax : nth_error (o_aux ob) (Z.to_nat (d + off)) = Some ax) by (apply nth_error_nth'; lia).
  destruct (nth_error cs (Z.to_nat (d + off))) as [c|] eqn:Ec; [|apply nth_error_None in Ec; lia].
  pose proof (proj2 (proj1 (Forall2_nth _ _ _) Hxs) _ _ _ Eax Ec) as Hc.
  assert (Hfin : (forall m, mholds B X m -> ~ freed_in (m_regions m) c) ->
            exists q x, WPtr (mkPtr (pl_base pl + d) (pl_cap pl)) = WPtr q /\
              forall m, mholds B X m ->
                op_res (RawLoadPointer off [AuxRead; LowerResolve; AddressRead]) P [WPtr q] m =
                Some (OpRes (RVal (WPtr x)) m)).
  { intros Hnf. exists (mkPtr (pl_base pl + d) (pl_cap pl)), (mkPtr (of_bytes' (window (d + off) 8 xs)) c).
    split; [reflexivity|]. intros m Hm. pose proof (Hm o pl xs cs Hpl Hx) as Hh.
    pose proof (Hloc m (proj1 Hh)) as Hl. apply op_raw_load_pointer; [exact (located_access _ _ _ _ _ _ _ Hl)|].
    rewrite pointer_load_plain, (loc_addr _ _ _ _ _ _ _ Hl). cbn [ptr_addr]. rewrite <- Z.add_assoc. f_equal. f_equal.
    - apply (holds_window m pl xs cs (d + off) 8 Hh); lia.
    - unfold aux_at. apply aux_holds_kept; [|exact (Hnf m Hm)]. destruct Hh as (_ & _ & Ha).
      destruct (Ha _ _ Ec) as [_ H]. rewrite Z2Nat.id in H by lia. exact H. }
  destruct ax as [|o'|].
  - intros [= <- <-]. split; [reflexivity|]. split; [reflexivity|]. apply Hfin. cbn [daux] in Hc. subst c.
    intros m _ Hf. destruct Hf as (b & reg & [E|E] & _); discriminate E.
  - destruct (Nat.eqb o o'); [discriminate|]. destruct (get_obj st o') as [ob'|] eqn:Eo'; [|discriminate].
    intros [= <- <-]. split; [reflexivity|]. split; [reflexivity|]. apply Hfin.
    destruct Hc as (pl' & Hpl' & ->). destruct (M_obj _ _ _ _ _ _ _ HM Eo') as (pl2 & xs' & cs' & Hp2 & Hx2 & _).
    rewrite Hpl' in Hp2. injection Hp2 as <-.
    intros m Hm Hf. destruct Hf as (b & reg & Hcb & Hreg & Hfr). destruct (Hm o' pl' xs' cs' Hpl' Hx2) as ([E L] & _).
    assert (Eb : b = pl_base pl') by (unfold pl_cap in Hcb; destruct (pl_ro pl'), Hcb as [Hcb|Hcb]; congruence).
    subst b. rewrite E in Hreg. injection Hreg as <-. congruence.
  - discriminate.
Qed.

(** * Flights

    A flight moves a pointer by a number and keeps the capability of
    another pointer. The checker follows the offset only when both
    pointers point into the same object. *)

Definition ptrish (v : aval) : bool := match v with VP _ _ | VN _ | VA | VF _ => true | _ => false end.

Lemma ptrish_word ρ B v w : ptrish v = true -> dval ge ρ B v w -> exists p, w = WPtr p.
Proof using Type.
  destruct v; try discriminate; intros _; cbn [dval].
  - intros (x & _ & ->). eauto.
  - intros ->. eauto.
  - intros H. exact H.
  - intros (p & -> & _). eauto.
Qed.

Lemma aflight_sound ρ B st e X p x q wp wx wq v st' :
  M ρ B st e X -> wf_val (length (st_bnd st)) p -> wf_int (length (st_bnd st)) x ->
  dval ge ρ B p wp -> dval ge ρ B (VI x) wx -> dval ge ρ B q wq ->
  aflight p (VI x) q st = Some (v, st') ->
  exists pp qq, wp = WPtr pp /\ wq = WPtr qq /\ wx = WInt (dint ρ x) /\
    R ρ B e X st st' v (WPtr (mkPtr ((ptr_addr pp mod 2 ^ 64 + dint ρ x) mod 2 ^ 64) (ptr_cap qq))).
Proof using Type.
  intros HM Wp Wx Hp Hx Hq H.
  assert (Hpt : ptrish p = true /\ ptrish q = true).
  { destruct p, q; cbn [aflight] in H; try discriminate H; split; reflexivity. }
  destruct Hpt as [P1 P2].
  destruct (ptrish_word ρ B p wp P1 Hp) as [pp ->]. destruct (ptrish_word ρ B q wq P2 Hq) as [qq ->].
  exists pp, qq. split; [reflexivity|]. split; [reflexivity|]. split; [exact Hx|]. clear Hx.
  assert (Hva : R ρ B e X st st VA (WPtr (mkPtr ((ptr_addr pp mod 2 ^ 64 + dint ρ x) mod 2 ^ 64) (ptr_cap qq)))).
  { apply R_same; [exact HM | exact I | eexists; reflexivity]. }
  destruct p as [| | |o a| | |]; try discriminate P1; destruct q as [| | |o' a'| | |]; try discriminate P2;
    cbn [aflight] in H; try (injection H as <- <-; exact Hva).
  destruct (Nat.eqb_spec o o') as [<-|_]; [|injection H as <- <-; exact Hva].
  destruct (rng st a) as [alo ahi] eqn:Era. destruct (rng st x) as [xlo xhi] eqn:Erx.
  destruct Hp as (pl & Hpl & [= ->]). destruct Hq as (pl' & Hpl' & [= ->]).
  rewrite Hpl in Hpl'. injection Hpl' as <-. cbn [ptr_addr ptr_cap]. cbn [wf_val] in Wp.
  assert (Hok : place_ok pl).
  { pose proof (proj1 HM) as HB. rewrite Forall_forall in HB. apply HB. eapply nth_error_In. exact Hpl. }
  destruct Hok as [Hb0 _].
  pose proof (rng_sound guard ρ st a alo ahi (M_sat _ _ _ _ _ _ _ _ HM) Wp Era) as Ra.
  pose proof (rng_sound guard ρ st x xlo xhi (M_sat _ _ _ _ _ _ _ _ HM) Wx Erx) as Rx.
  assert (Hmk : forall lo hi δ r st1, mk st lo hi = (r, st1) -> lo <= dint ρ a + δ <= hi -> 0 <= lo -> hi <= 2 ^ 62 ->
            (dint ρ x - δ) mod 2 ^ 64 = 0 ->
            R ρ B e X st st1 (VP o r)
              (WPtr (mkPtr (((pl_base pl + dint ρ a) mod 2 ^ 64 + dint ρ x) mod 2 ^ 64) (pl_cap pl)))).
  { intros lo hi δ r st1 Emk Hr H0 H1 Hδ.
    destruct (mk_sound _ _ _ ρ B st e X lo hi (dint ρ a + δ) r st1 HM Hr Emk) as (ρ' & G1 & G2 & G3 & G4).
    exists ρ'. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. cbn [dval]. exists pl.
    split; [exact Hpl|]. rewrite G4. f_equal. f_equal. apply flight_addr; [exact Hb0 | lia | exact Hδ]. }
  destruct a as [za|sa], x as [zx|sx]; cbv beta iota zeta in H;
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Ec end;
    try (injection H as <- <-; exact Hva);
    apply andb_true_iff in Ec as [E1 E2]; apply Z.leb_le in E1, E2.
  - injection H as <- <-. apply R_same; [exact HM | exact I|]. cbn [dval dint]. exists pl. split; [exact Hpl|].
    f_equal. f_equal. apply flight_addr; [exact Hb0 | lia | apply signed64_mod].
  - destruct (mk st (alo + xlo) (ahi + xhi)) as [r st1] eqn:Emk. injection H as <- <-.
    apply (Hmk _ _ (dint ρ (S sx)) r st1 Emk); [lia | lia | lia | rewrite Z.sub_diag; reflexivity].
  - destruct (mk st (alo + signed64 zx) (ahi + signed64 zx)) as [r st1] eqn:Emk. injection H as <- <-.
    apply (Hmk _ _ (signed64 zx) r st1 Emk); [lia | lia | lia | apply signed64_mod].
  - destruct (mk st (alo + xlo) (ahi + xhi)) as [r st1] eqn:Emk. injection H as <- <-.
    apply (Hmk _ _ (dint ρ (S sx)) r st1 Emk); [lia | lia | lia | rewrite Z.sub_diag; reflexivity].
Qed.

(** * Binding a result *)

(** Binding a name to a value that describes a word keeps the state
    true of the environment that binds the name to that word. *)
Lemma M_bind ρ B st e X d v w :
  M ρ B st e X -> wf_val (length (st_bnd st)) v -> dval ge ρ B v w -> M ρ B (bind st d v) (put d w e) X.
Proof using Type.
  intros (HB & HG & Hs & (We & Wf & Wl & Wo) & He & Ho) Wv Hv.
  split; [exact HB|]. split; [exact HG|]. split; [exact Hs|]. split; [|split; [|exact Ho]].
  - split; [|split; [exact Wf | split; [exact Wl | exact Wo]]]. constructor; [exact Wv | exact We].
  - intros n v0. cbn [bind set_env st_env lookup]. rewrite lookup_put_name.
    destruct (name_eqb n d); [intros [= <-]; exists w; auto | apply He].
Qed.

(** A step that produced a value binds it and gives a true state. *)
Lemma R_bind ρ B e X st st' v w d :
  R ρ B e X st st' v w -> exists ρ', M ρ' B (bind st' d v) (put d w e) X /\ step ρ st ρ' (bind st' d v).
Proof using Type.
  intros (ρ' & HM & S1 & Wv & Hv). exists ρ'. split; [apply M_bind; assumption | exact S1].
Qed.

(** * Allocation

    An allocation gives the state one more object, at a place that the
    allocator chooses. The lists of places and of contents grow by one,
    and everything that was true of the old places stays true. *)

Lemma dval_app ρ B B1 v w : dval ge ρ B v w -> dval ge ρ (B ++ B1) v w.
Proof using Type.
  destruct v; cbn [dval]; auto. intros (x & Hx & E). exists x. split; [|exact E].
  rewrite nth_error_app1; [exact Hx | apply nth_error_Some; congruence].
Qed.

Lemma daux_app B B1 x c : daux B x c -> daux (B ++ B1) x c.
Proof using Type.
  destruct x; cbn [daux]; auto. intros (pl & Hp & E). exists pl. split; [|exact E].
  rewrite nth_error_app1; [exact Hp | apply nth_error_Some; congruence].
Qed.

Lemma obj_ok_app ρ B B1 pl ob xs cs : obj_ok ρ B pl ob xs cs -> obj_ok ρ (B ++ B1) pl ob xs cs.
Proof using Type.
  intros (H1 & H2 & H3). split; [exact H1|]. split; [|exact H3].
  eapply Forall2_impl; [|exact H2]. intros x c. apply daux_app.
Qed.

(** A true state stays true when one owned object is added at the end. *)
Lemma M_app_obj ρ B st e X pl ob xs cs :
  M ρ B st e X -> place_ok pl -> obj_ok ρ (B ++ [pl]) pl ob xs cs -> wf_obj (length (st_bnd st)) (Some ob) ->
  M ρ (B ++ [pl]) (set_objs st (st_objs st ++ [Some ob])) e (X ++ [Some (xs, cs)]).
Proof using Type.
  intros (HB & HG & Hs & (We & Wf & Wl & Wo) & He & (L1 & L2 & Ho)) Hpl Hok Wob.
  split; [apply Forall_app; split; [exact HB | constructor; [exact Hpl | constructor]]|].
  split.
  { intros i g Hi. destruct (HG i g Hi) as (pl0 & H1 & H2). exists pl0. split; [|exact H2].
    rewrite nth_error_app1; [exact H1 | apply nth_error_Some; congruence]. }
  split; [exact Hs|]. split; [|split].
  - split; [exact We|]. split; [exact Wf|]. split; [exact Wl|]. cbn [set_objs st_objs st_bnd].
    apply Forall_app. split; [exact Wo | constructor; [exact Wob | constructor]].
  - intros n v Hn. destruct (He n v Hn) as (w & H1 & H2). exists w. split; [exact H1 | apply dval_app; exact H2].
  - cbn [set_objs st_objs]. split; [rewrite !length_app; cbn [length]; lia|].
    split; [rewrite !length_app; cbn [length]; lia|]. intros i ob0 Hi.
    destruct (Nat.lt_ge_cases i (length (st_objs st))) as [Hlt|Hge].
    + rewrite nth_error_app1 in Hi by exact Hlt. destruct (Ho i ob0 Hi) as (pl0 & xs0 & cs0 & H1 & H2 & H3).
      exists pl0, xs0, cs0. rewrite !nth_error_app1 by (apply nth_error_Some; congruence).
      split; [exact H1|]. split; [exact H2 | apply obj_ok_app; exact H3].
    + rewrite nth_error_app2 in Hi by exact Hge.
      destruct (i - length (st_objs st))%nat as [|n] eqn:En; cbn [nth_error] in Hi; [|destruct n; discriminate].
      injection Hi as <-. exists pl, xs, cs. rewrite !nth_error_app2 by lia.
      replace (i - length B)%nat with O by lia. replace (i - length X)%nat with O by lia. auto.
Qed.

(** The state after an allocation is true of the old places followed
    by the new object's place, and the pointer that the allocation
    returns points to the start of the new object. *)
Lemma M_alloc ρ B st e X al n base :
  M ρ B st e X -> 0 <= n -> 0 < base -> base mod Z.max al 16 = 0 -> base + (n + 15) / 16 * 16 <= 2 ^ 48 ->
  let N := Z.to_nat ((n + 15) / 16 * 16) in
  let pl := mkPlace base (mkRegion base (base + (n + 15) / 16 * 16) Heap Live) false in
  M ρ (B ++ [pl]) (set_objs st (st_objs st ++ [Some (new_obj al n)])) e (X ++ [Some (repeat 0 N, repeat CNone N)]) /\
  dval ge ρ (B ++ [pl]) (VP (length (st_objs st)) (K 0)) (WPtr (mkPtr base (Obj base))).
Proof using Type.
  intros HM Hn Hb Hmod Hend N pl.
  assert (Hex : 0 <= (n + 15) / 16 * 16) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
  split.
  - apply M_app_obj; [exact HM | split; cbn [pl pl_base pl_reg r_end]; lia | |].
    + unfold AbsDen.obj_ok, new_obj. cbn [o_bytes o_aux o_ro o_align pl pl_ro pl_base pl_reg r_end]. fold N.
      split; [apply Forall2_repeat; split; [unfold is_byte; lia | reflexivity]|].
      split; [apply Forall2_repeat; reflexivity|]. split; [rewrite !repeat_length; reflexivity|].
      split; [reflexivity|]. split; [exact Hmod|]. unfold o_size. cbn [o_bytes]. rewrite repeat_length. lia.
    + unfold new_obj. cbn [wf_obj o_bytes]. apply Forall_forall. intros b Hin. apply repeat_spec in Hin.
      subst b. exact I.
  - cbn [dval dint]. exists pl. destruct HM as (_ & _ & _ & _ & _ & (L1 & _)).
    split; [rewrite nth_error_app2, L1, Nat.sub_diag by lia; reflexivity|].
    cbn [pl pl_base pl_cap pl_ro]. unfold pl_cap. cbn [pl_ro pl_base]. rewrite Z.add_0_r. reflexivity.
Qed.

End mem.
