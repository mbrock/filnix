(** The checker of [AbsRun](AbsRun.v) computes with abstract values,
    and a proof about a program needs to know what those values say
    about real words and real memory. This module gives that meaning
    without mentioning the program logic, so that every fact about
    symbols, ranges and bytes is an ordinary proposition.

    An abstract state names unknown numbers by symbols and names
    objects by numbers. Three choices connect it to a real run. A
    valuation gives every symbol a number. A list of places gives
    every numbered object a real object. A list of contents gives
    every owned object its bytes and its shadow slots. The predicate
    [M] says that these three choices make an abstract state true of a
    real environment.

    The lemmas of this module show that the checker's steps on symbols
    and ranges keep [D]. The proof that the checker is sound is being
    written on top of them. *)

From Stdlib Require Import String ZArith List Bool Lia PeanoNat.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Symbolic AbsRun.
Import ListNotations.
Open Scope Z_scope.

(** * Places

    The checker numbers the objects a function can touch. A place is
    the real object behind one number: its base address, its region,
    and whether the program may only read it. *)

Record place : Type := mkPlace { pl_base : Z; pl_reg : region; pl_ro : bool }.

(** A pointer into a place carries the capability of its object. *)
Definition pl_cap (x : place) : cap := if pl_ro x then Ro (pl_base x) else Obj (pl_base x).

(** Address arithmetic on a pointer into a place must not wrap, so a
    place lies below 2^62. *)
Definition place_ok (x : place) : Prop := 0 <= pl_base x <= 2 ^ 62 /\ r_end (pl_reg x) <= 2 ^ 62.

(** The contents of the objects are their bytes and their shadow
    slots. An object that the state does not own has no contents. *)
Definition cont : Type := list (option (list Z * list cap)).

(** * The meaning of values

    A valuation ρ gives every symbol a number. The definitions of this
    section read abstract integers, values, bytes and flags under one
    valuation and one list of places. The proposition [guard] is what
    the checker's guard stands for. *)

Section den.
Variable guard : Prop.
Variable ge : genv.
Variable gobjs : list name.
Variable fnames : list (name * (list class * ret_type)).

Definition dint (ρ : nat -> Z) (a : aint) : Z := match a with K z => z | S s => ρ s end.

(** An abstract value describes a word. A [VP] is a pointer at a known
    offset into a numbered object, a [VN] is a pointer without a
    capability, a [VA] is any pointer, and a [VF] is the address of a
    named function. *)
Definition dval (ρ : nat -> Z) (B : list place) (v : aval) (w : word) : Prop :=
  match v with
  | VI a => w = WInt (dint ρ a)
  | VC c k a b => exists r, cond_bit c k (dint ρ a) (dint ρ b) = Some r /\ w = WInt r
  | VJ => exists n, w = WInt n
  | VP o a => exists x, nth_error B o = Some x /\ w = WPtr (mkPtr (pl_base x + dint ρ a) (pl_cap x))
  | VN a => w = WPtr (mkPtr (dint ρ a) CNone)
  | VA => exists p, w = WPtr p
  | VF g => exists p, w = WPtr p /\ lookup g (ge_globals ge) = Some p /\ ptr_cap p = Fn g
  end.

(** Every abstract byte describes a number below 256. *)
Definition dbyte (ρ : nat -> Z) (b : abyte) (x : Z) : Prop :=
  0 <= x < 256 /\
  match b with
  | BK z => x = z
  | BOf s i => x = byte_of (ρ s) i
  | BIn lo hi => lo <= x <= hi
  | BR => True
  | BGuard k => Z.testbit x k = true -> guard
  | BEnd s key mask => ρ s = key -> Z.land x mask = 0
  end.

(** The shadow slot of a byte holds no capability, the capability of a
    numbered object, or anything. *)
Definition daux (B : list place) (x : aaux) (c : cap) : Prop :=
  match x with
  | XNone => c = CNone
  | XObj o => exists pl, nth_error B o = Some pl /\ c = pl_cap pl
  | XAny => True
  end.

Definition dflag (ρ : nat -> Z) (s : nat) (fl : flag) : Prop :=
  match fl with
  | FBit n => Z.testbit (ρ s) n = true -> guard
  | FNz => ρ s <> 0 -> guard
  | FEnd u key mask => ρ u = key -> Z.land (ρ s) mask = 0
  | FEndNz u key => ρ u = key -> ρ s = 0
  end.

(** A valuation satisfies a state when every symbol lies in its range
    and every flag, every recorded difference and the guard bit tell
    the truth. *)
Definition sat (ρ : nat -> Z) (st : astate) : Prop :=
  (forall s lo hi, nth_error (st_bnd st) s = Some (lo, hi) -> lo <= ρ s <= hi) /\
  (forall s fl, In (s, fl) (st_flags st) -> dflag ρ s fl) /\
  (forall t s c, In (t, s, c) (st_lin st) -> ρ t = ρ s + c) /\
  (st_guard st = true -> guard).

(** The real environment gives every name of the abstract environment
    a word that its abstract value describes. *)
Definition denv (ρ : nat -> Z) (B : list place) (st : astate) (e : env) : Prop :=
  forall n v, lookup n (st_env st) = Some v -> exists w, lookup n e = Some w /\ dval ρ B v w.

(** * Well-formed states

    A new symbol takes the next free number, which is the length of the
    range table. That is sound only when nothing in the state already
    mentions that number, so every state the checker reaches must
    mention only symbols that have a range. *)

Definition wf_int (n : nat) (a : aint) : Prop := match a with K _ => True | S s => (s < n)%nat end.

Definition wf_val (n : nat) (v : aval) : Prop :=
  match v with
  | VI a | VP _ a | VN a => wf_int n a
  | VC _ _ a b => wf_int n a /\ wf_int n b
  | VJ | VA | VF _ => True
  end.

Definition wf_byte (n : nat) (b : abyte) : Prop :=
  match b with BOf s _ | BEnd s _ _ => (s < n)%nat | _ => True end.

Definition wf_flag (n : nat) (fl : flag) : Prop :=
  match fl with FEnd s _ _ | FEndNz s _ => (s < n)%nat | _ => True end.

Definition wf_obj (n : nat) (o : option aobj) : Prop :=
  match o with Some ob => Forall (wf_byte n) (o_bytes ob) | None => True end.

Definition wf (st : astate) : Prop :=
  let n := length (st_bnd st) in
  Forall (fun nv => wf_val n (snd nv)) (st_env st) /\
  Forall (fun f => (fst f < n)%nat /\ wf_flag n (snd f)) (st_flags st) /\
  Forall (fun l => (fst (fst l) < n)%nat /\ (snd (fst l) < n)%nat) (st_lin st) /\
  Forall (wf_obj n) (st_objs st).

(** * Objects

    An abstract object describes the contents of a real object at its
    place. The bytes and the shadow slots are described one by one.
    The object fits its place, and the base of the place is a multiple
    of the object's alignment. *)

Definition obj_ok (ρ : nat -> Z) (B : list place) (pl : place) (ob : aobj) (xs : list Z) (cs : list cap) : Prop :=
  Forall2 (dbyte ρ) (o_bytes ob) xs /\ Forall2 (daux B) (o_aux ob) cs /\
  length (o_aux ob) = length (o_bytes ob) /\ pl_ro pl = o_ro ob /\
  pl_base pl mod o_align ob = 0 /\ pl_base pl + o_size ob <= r_end (pl_reg pl).

(** Every object of a state has a place and contents that it
    describes. The three lists number the same objects. *)
Definition objs_ok (ρ : nat -> Z) (B : list place) (os : list (option aobj)) (X : cont) : Prop :=
  length os = length B /\ length X = length B /\
  forall i ob, nth_error os i = Some (Some ob) ->
    exists pl xs cs, nth_error B i = Some pl /\ nth_error X i = Some (Some (xs, cs)) /\ obj_ok ρ B pl ob xs cs.

(** The global objects come first in every list of places, and the
    program's symbol table agrees with them. *)
Definition globals_ok (B : list place) : Prop :=
  forall i g, nth_error gobjs i = Some g ->
    exists pl, nth_error B i = Some pl /\
               lookup g (ge_globals ge) = Some (mkPtr (pl_base pl) (pl_cap pl)).

(** A name in [fnames] is a function symbol of the program, and a
    function with that name has the parameter classes and the return
    type that [fnames] gives it. *)
Definition fnames_ok : Prop :=
  forall g ks rt, lookup g fnames = Some (ks, rt) ->
    (exists p, lookup g (ge_globals ge) = Some p /\ ptr_cap p = Fn g) /\
    (forall gf, find_fn ge g = Some (Defined gf) ->
       map fst (fn_params gf) = ks /\ fn_ret gf = rt /\ variadic_func gf = false).

(** * Closed values

    A specification and an invariant mention no symbol. A closed value
    describes a word by a range alone. *)

Definition dcval (B : list place) (c : cval) (w : word) : Prop :=
  match c with
  | CI lo hi => exists n, lo <= n <= hi /\ w = WInt n
  | CJ => exists n, w = WInt n
  | CP o lo hi => exists x off, nth_error B o = Some x /\ lo <= off <= hi /\
                                w = WPtr (mkPtr (pl_base x + off) (pl_cap x))
  | CN lo hi => exists n, lo <= n <= hi /\ w = WPtr (mkPtr n CNone)
  | CA => exists p, w = WPtr p
  | CF g => exists p, w = WPtr p /\ lookup g (ge_globals ge) = Some p /\ ptr_cap p = Fn g
  end.

(** A function returns nothing when its specification names no result,
    and otherwise it returns one word that the result describes. *)
Definition dret (B : list place) (r : option cval) (out : outcome) : Prop :=
  match r with
  | None => out = RetVoid
  | Some c => exists w, out = Ret w /\ dcval B c w
  end.

(** * States

    A valuation, a list of places and a list of contents make a state
    true of a real environment. *)
Definition M (ρ : nat -> Z) (B : list place) (st : astate) (e : env) (X : cont) : Prop :=
  Forall place_ok B /\ globals_ok B /\ sat ρ st /\ wf st /\ denv ρ B st e /\ objs_ok ρ B (st_objs st) X.

(** An instruction reads its operands before it acts, so the proof
    needs a state together with the operands already read. The
    predicate [D] says that one valuation makes the state true and
    makes each value of [vs] describe the word of [ws] at the same
    position. *)
Definition D (B : list place) (st : astate) (e : env) (X : cont) (vs : list aval) (ws : list word) : Prop :=
  exists ρ, M ρ B st e X /\ Forall (wf_val (length (st_bnd st))) vs /\ Forall2 (dval ρ B) vs ws.

(** * Valuations that agree

    Two valuations agree below n when they give the same number to
    every symbol below n. Anything that mentions only symbols below n
    means the same under both. *)

Definition agree (n : nat) (ρ ρ' : nat -> Z) : Prop := forall s, (s < n)%nat -> ρ' s = ρ s.

Definition upd (ρ : nat -> Z) (n : nat) (z : Z) : nat -> Z := fun s => if Nat.eqb s n then z else ρ s.

Lemma agree_upd ρ n z : agree n ρ (upd ρ n z).
Proof using Type. intros s Hs. unfold upd. destruct (Nat.eqb_spec s n); [lia | reflexivity]. Qed.

Lemma upd_same ρ n z : upd ρ n z n = z.
Proof using Type. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma agree_refl n ρ : agree n ρ ρ.
Proof using Type. intros s _. reflexivity. Qed.

Lemma agree_trans n n' ρ1 ρ2 ρ3 : (n <= n')%nat -> agree n ρ1 ρ2 -> agree n' ρ2 ρ3 -> agree n ρ1 ρ3.
Proof using Type. intros Hn H1 H2 s Hs. rewrite H2 by lia. apply H1. exact Hs. Qed.

Lemma dint_agree n ρ ρ' a : agree n ρ ρ' -> wf_int n a -> dint ρ' a = dint ρ a.
Proof using Type. intros Ha Hw. destruct a as [z|s]; [reflexivity | exact (Ha s Hw)]. Qed.

Lemma dval_agree n ρ ρ' B v w : agree n ρ ρ' -> wf_val n v -> dval ρ B v w -> dval ρ' B v w.
Proof using Type.
  intros Ha Hw. destruct v as [a|c k a b| |o a|a| |g]; cbn [dval wf_val] in *; try (intros H; exact H).
  - rewrite (dint_agree n ρ ρ' a Ha Hw). auto.
  - destruct Hw as [Hwa Hwb]. rewrite (dint_agree n ρ ρ' a Ha Hwa), (dint_agree n ρ ρ' b Ha Hwb). auto.
  - rewrite (dint_agree n ρ ρ' a Ha Hw). auto.
  - rewrite (dint_agree n ρ ρ' a Ha Hw). auto.
Qed.

Lemma dvals_agree n ρ ρ' B vs ws :
  agree n ρ ρ' -> Forall (wf_val n) vs -> Forall2 (dval ρ B) vs ws -> Forall2 (dval ρ' B) vs ws.
Proof using Type.
  intros Ha Hw H. induction H as [|v w vs ws Hv _ IH]; constructor.
  - inversion_clear Hw. eapply dval_agree; eauto.
  - inversion_clear Hw. auto.
Qed.

Lemma dbyte_agree n ρ ρ' b x : agree n ρ ρ' -> wf_byte n b -> dbyte ρ b x -> dbyte ρ' b x.
Proof using Type.
  intros Ha Hw [Hr H]. split; [exact Hr|]. destruct b; cbn [wf_byte] in *; try exact H.
  - rewrite (Ha s Hw). exact H.
  - rewrite (Ha s Hw). exact H.
Qed.

Lemma dflag_agree n ρ ρ' s fl : agree n ρ ρ' -> (s < n)%nat -> wf_flag n fl -> dflag ρ s fl -> dflag ρ' s fl.
Proof using Type.
  intros Ha Hs Hw H. destruct fl; cbn [dflag wf_flag] in *; rewrite ?(Ha s Hs); try exact H.
  - rewrite (Ha s0 Hw). exact H.
  - rewrite (Ha s0 Hw). exact H.
Qed.

Lemma wf_int_mono n n' a : (n <= n')%nat -> wf_int n a -> wf_int n' a.
Proof using Type. destruct a; cbn; [auto | lia]. Qed.

Lemma wf_val_mono n n' v : (n <= n')%nat -> wf_val n v -> wf_val n' v.
Proof using Type.
  intros Hn. destruct v; cbn; try tauto; try apply (wf_int_mono n n'); auto.
  intros [H1 H2]. split; eapply wf_int_mono; eauto.
Qed.

Lemma wf_byte_mono n n' b : (n <= n')%nat -> wf_byte n b -> wf_byte n' b.
Proof using Type. destruct b; cbn; try tauto; lia. Qed.

Lemma wf_flag_mono n n' fl : (n <= n')%nat -> wf_flag n fl -> wf_flag n' fl.
Proof using Type. destruct fl; cbn; try tauto; lia. Qed.

Lemma wf_obj_mono n n' o : (n <= n')%nat -> wf_obj n o -> wf_obj n' o.
Proof using Type.
  intros Hn. destruct o as [ob|]; cbn; [|auto]. apply Forall_impl. intros b. apply wf_byte_mono. exact Hn.
Qed.

Lemma dbytes_agree n ρ ρ' bs xs :
  agree n ρ ρ' -> Forall (wf_byte n) bs -> Forall2 (dbyte ρ) bs xs -> Forall2 (dbyte ρ') bs xs.
Proof using Type.
  intros Ha Hw H. induction H as [|b x bs xs Hbx _ IH]; constructor.
  - inversion_clear Hw. eapply dbyte_agree; eauto.
  - inversion_clear Hw. auto.
Qed.

Lemma obj_ok_agree n ρ ρ' B pl ob xs cs :
  agree n ρ ρ' -> wf_obj n (Some ob) -> obj_ok ρ B pl ob xs cs -> obj_ok ρ' B pl ob xs cs.
Proof using Type.
  intros Ha Hw (Hb & Hrest). split; [|exact Hrest]. eapply dbytes_agree; eauto.
Qed.

Lemma objs_ok_agree n ρ ρ' B os X :
  agree n ρ ρ' -> Forall (wf_obj n) os -> objs_ok ρ B os X -> objs_ok ρ' B os X.
Proof using Type.
  intros Ha Hw (H1 & H2 & H). split; [exact H1|]. split; [exact H2|]. intros i ob Hi.
  destruct (H i ob Hi) as (pl & xs & cs & Hp & Hx & Ho). exists pl, xs, cs. split; [exact Hp|]. split; [exact Hx|].
  eapply obj_ok_agree; [exact Ha | | exact Ho]. rewrite Forall_forall in Hw. apply (Hw (Some ob)).
  eapply nth_error_In. exact Hi.
Qed.

Lemma denv_agree n ρ ρ' B st e :
  agree n ρ ρ' -> Forall (fun nv => wf_val n (snd nv)) (st_env st) -> denv ρ B st e -> denv ρ' B st e.
Proof using Type.
  intros Ha Hw H m v Hm. destruct (H m v Hm) as (w & Hl & Hv). exists w. split; [exact Hl|].
  eapply dval_agree; [exact Ha | | exact Hv]. rewrite Forall_forall in Hw.
  assert (Hin : exists k, In (k, v) (st_env st)).
  { clear - Hm. induction (st_env st) as [|[k v'] l IH]; cbn in Hm; [discriminate|].
    destruct (name_eqb m k); [injection Hm as ->; exists k; left; reflexivity|].
    destruct (IH Hm) as [k' Hk]. exists k'. right. exact Hk. }
  destruct Hin as [k Hk]. exact (Hw _ Hk).
Qed.

(** * New symbols *)

(** A new symbol may take any number in its range. The state with the
    new symbol is true under the valuation that gives it that number. *)
Lemma M_fresh ρ B st e X lo hi z :
  M ρ B st e X -> lo <= z <= hi ->
  M (upd ρ (length (st_bnd st)) z) B (snd (fresh st lo hi)) e X.
Proof using Type.
  intros (HB & HG & (Hbnd & Hfl & Hlin & Hg) & (We & Wf & Wl & Wo) & He & Ho) Hz.
  set (n := length (st_bnd st)) in *. pose proof (agree_upd ρ n z) as Ha.
  unfold fresh. cbn [snd]. split; [exact HB|]. split; [exact HG|]. split; [|split; [|split]].
  - split; [|split; [|split]]; cbn [st_bnd st_flags st_lin st_guard].
    + intros s l h Hs. destruct (Nat.lt_ge_cases s n) as [Hlt|Hge].
      * rewrite nth_error_app1 in Hs by exact Hlt. rewrite (Ha s Hlt). eauto.
      * rewrite nth_error_app2 in Hs by exact Hge. fold n in Hs.
        destruct (s - n)%nat as [|k] eqn:E; cbn in Hs; [|destruct k; discriminate].
        injection Hs as <- <-. replace s with n by lia. rewrite upd_same. exact Hz.
    + intros s fl Hin. rewrite Forall_forall in Wf. destruct (Wf _ Hin) as [Hs Hw]. cbn in Hs, Hw.
      eapply dflag_agree; eauto.
    + intros t s c Hin. rewrite Forall_forall in Wl. destruct (Wl _ Hin) as [Ht Hs]. cbn in Ht, Hs.
      rewrite (Ha t Ht), (Ha s Hs). eauto.
    + exact Hg.
  - unfold wf. cbn [st_bnd st_env st_flags st_lin st_objs]. rewrite length_app. cbn [length]. fold n.
    assert (Hn : (n <= n + 1)%nat) by lia.
    split; [|split; [|split]].
    + eapply Forall_impl; [|exact We]. intros nv. apply wf_val_mono. exact Hn.
    + eapply Forall_impl; [|exact Wf]. intros f [H1 H2]. split; [lia | eapply wf_flag_mono; eauto].
    + eapply Forall_impl; [|exact Wl]. intros l [H1 H2]. lia.
    + eapply Forall_impl; [|exact Wo]. intros o. apply wf_obj_mono. exact Hn.
  - eapply denv_agree; [exact Ha | exact We | exact He].
  - eapply objs_ok_agree; [exact Ha | exact Wo | exact Ho].
Qed.

(** * Ranges *)

Lemma length_list_set {A : Type} n (x : A) l : length (list_set n x l) = length l.
Proof using Type. revert l. induction n as [|n IH]; intros [|y l]; cbn; auto. Qed.

Lemma nth_error_list_set {A : Type} n (x : A) l m :
  nth_error (list_set n x l) m =
  if Nat.eqb m n then match nth_error l m with Some _ => Some x | None => None end else nth_error l m.
Proof using Type.
  revert l m. induction n as [|n IH]; intros [|y l] [|m]; cbn; auto.
  destruct (Nat.eqb m n); reflexivity.
Qed.

(** A range table is true of a valuation when every symbol lies in its range. *)
Definition bok (ρ : nat -> Z) (bnd : list (Z * Z)) : Prop :=
  forall s lo hi, nth_error bnd s = Some (lo, hi) -> lo <= ρ s <= hi.

Lemma bok_set ρ bnd s lo hi : bok ρ bnd -> lo <= ρ s <= hi -> bok ρ (list_set s (lo, hi) bnd).
Proof using Type.
  intros Hb Hs m l h. rewrite nth_error_list_set. destruct (Nat.eqb_spec m s) as [->|_]; [|apply Hb].
  destruct (nth_error bnd s); [|discriminate]. intros [= <- <-]. exact Hs.
Qed.

Lemma bok_meet ρ bnd s lo hi : bok ρ bnd -> lo <= ρ s <= hi -> bok ρ (meet s lo hi bnd).
Proof using Type.
  intros Hb Hs. unfold meet. destruct (nth s bnd (0, 0)) as [l h] eqn:E.
  intros m l' h'. rewrite nth_error_list_set. destruct (Nat.eqb_spec m s) as [->|_]; [|apply Hb].
  destruct (nth_error bnd s) as [[l0 h0]|] eqn:E'; [|discriminate]. intros [= <- <-].
  rewrite (nth_error_nth _ _ _ E') in E. injection E as <- <-. pose proof (Hb _ _ _ E'). lia.
Qed.

Lemma length_meet s lo hi bnd : length (meet s lo hi bnd) = length bnd.
Proof using Type. unfold meet. destruct (nth s bnd (0, 0)). apply length_list_set. Qed.

Lemma rng_sound ρ st a lo hi :
  sat ρ st -> wf_int (length (st_bnd st)) a -> rng st a = (lo, hi) -> lo <= dint ρ a <= hi.
Proof using Type.
  intros (Hb & _) Hw. destruct a as [z|s]; cbn [rng dint wf_int] in *.
  - intros [= <- <-]. lia.
  - intros E. apply Hb. rewrite <- E. apply nth_error_nth'. exact Hw.
Qed.

(** A state that differs from a true state only in its ranges, flags,
    differences and guard is true when those four parts are. *)
Lemma M_same ρ B st st' e X :
  M ρ B st e X -> st_env st' = st_env st -> st_objs st' = st_objs st ->
  length (st_bnd st') = length (st_bnd st) -> sat ρ st' ->
  Forall (fun f => (fst f < length (st_bnd st))%nat /\ wf_flag (length (st_bnd st)) (snd f)) (st_flags st') ->
  Forall (fun l => (fst (fst l) < length (st_bnd st))%nat /\ (snd (fst l) < length (st_bnd st))%nat) (st_lin st') ->
  M ρ B st' e X.
Proof using Type.
  intros (HB & HG & _ & (We & _ & _ & Wo) & He & Ho) Ee Eo El Hs Wf Wl.
  split; [exact HB|]. split; [exact HG|]. split; [exact Hs|]. split; [|split].
  - unfold wf. rewrite El, Ee, Eo. auto.
  - unfold denv. rewrite Ee. exact He.
  - rewrite Eo. exact Ho.
Qed.

Lemma M_wf_flags ρ B st e X : M ρ B st e X ->
  Forall (fun f => (fst f < length (st_bnd st))%nat /\ wf_flag (length (st_bnd st)) (snd f)) (st_flags st).
Proof using Type. intros (_ & _ & _ & (_ & W & _) & _). exact W. Qed.

Lemma M_wf_lin ρ B st e X : M ρ B st e X ->
  Forall (fun l => (fst (fst l) < length (st_bnd st))%nat /\ (snd (fst l) < length (st_bnd st))%nat) (st_lin st).
Proof using Type. intros (_ & _ & _ & (_ & _ & W & _) & _). exact W. Qed.

Lemma M_sat ρ B st e X : M ρ B st e X -> sat ρ st.
Proof using Type. intros (_ & _ & H & _). exact H. Qed.

Lemma M_set_bnd ρ B st e X bnd :
  M ρ B st e X -> length bnd = length (st_bnd st) -> bok ρ bnd -> M ρ B (set_bnd st bnd) e X.
Proof using Type.
  intros HM El Hb. pose proof (M_sat _ _ _ _ _ HM) as (_ & Hf & Hl & Hg).
  apply (M_same ρ B st); auto.
  - split; [exact Hb|]. auto.
  - exact (M_wf_flags _ _ _ _ _ HM).
  - exact (M_wf_lin _ _ _ _ _ HM).
Qed.

(** Narrowing the range of a symbol to an interval that holds its
    number keeps the state true. *)
Lemma set_rng_sound ρ B st e X a lo hi :
  M ρ B st e X -> lo <= dint ρ a <= hi ->
  M ρ B (set_rng st a lo hi) e X /\ length (st_bnd (set_rng st a lo hi)) = length (st_bnd st).
Proof using Type.
  intros HM Ha. destruct a as [z|s]; cbn [set_rng dint] in *; [auto|].
  pose proof (M_sat _ _ _ _ _ HM) as (Hb & _ & Hl & _).
  set (f := fun (bnd : list (Z * Z)) (l : nat * nat * Z) =>
              let '(t, u, c) := l in
              if Nat.eqb u s then meet t (lo + c) (hi + c) bnd
              else if Nat.eqb t s then meet u (lo - c) (hi - c) bnd else bnd).
  assert (H : forall l bnd, (forall x, In x l -> In x (st_lin st)) -> bok ρ bnd ->
                bok ρ (fold_left f l bnd) /\ length (fold_left f l bnd) = length bnd).
  { induction l as [|[[t u] c] l IH]; intros bnd Hin Hbk; cbn [fold_left]; [auto|].
    assert (Hstep : bok ρ (f bnd (t, u, c)) /\ length (f bnd (t, u, c)) = length bnd).
    { pose proof (Hl t u c (Hin _ (or_introl eq_refl))) as E. cbn [f].
      destruct (Nat.eqb_spec u s) as [->|_]; [split; [apply bok_meet; [exact Hbk | lia] | apply length_meet]|].
      destruct (Nat.eqb_spec t s) as [->|_]; [split; [apply bok_meet; [exact Hbk | lia] | apply length_meet]|].
      auto. }
    destruct Hstep as [H1 H2]. destruct (IH (f bnd (t, u, c))) as [H3 H4]; [intros x Hx; apply Hin; right; exact Hx | exact H1 |].
    split; [exact H3 | congruence]. }
  destruct (H (st_lin st) (list_set s (lo, hi) (st_bnd st))) as [H1 H2]; [auto | apply bok_set; [exact Hb | exact Ha] |].
  rewrite length_list_set in H2. split; [|exact H2]. apply M_set_bnd; assumption.
Qed.

Lemma M_add_flag ρ B st e X s fl :
  M ρ B st e X -> (s < length (st_bnd st))%nat -> wf_flag (length (st_bnd st)) fl -> dflag ρ s fl ->
  M ρ B (add_flag st s fl) e X.
Proof using Type.
  intros HM Hs Hw Hd. pose proof (M_sat _ _ _ _ _ HM) as (Hb & Hf & Hl & Hg).
  apply (M_same ρ B st); auto.
  - split; [exact Hb|]. split; [|auto]. intros s' fl' [[= <- <-]|Hin]; [exact Hd | apply Hf; exact Hin].
  - constructor; [auto | exact (M_wf_flags _ _ _ _ _ HM)].
  - exact (M_wf_lin _ _ _ _ _ HM).
Qed.

Lemma M_add_lin ρ B st e X t s c :
  M ρ B st e X -> (t < length (st_bnd st))%nat -> (s < length (st_bnd st))%nat -> ρ t = ρ s + c ->
  M ρ B (add_lin st t s c) e X.
Proof using Type.
  intros HM Ht Hs Hd. pose proof (M_sat _ _ _ _ _ HM) as (Hb & Hf & Hl & Hg).
  apply (M_same ρ B st); auto.
  - split; [exact Hb|]. split; [exact Hf|]. split; [|exact Hg].
    intros t' s' c' [[= <- <- <-]|Hin]; [exact Hd | apply Hl; exact Hin].
  - exact (M_wf_flags _ _ _ _ _ HM).
  - constructor; [auto | exact (M_wf_lin _ _ _ _ _ HM)].
Qed.

Lemma M_set_guard ρ B st e X b : M ρ B st e X -> (b = true -> guard) -> M ρ B (set_guard st b) e X.
Proof using Type.
  intros HM Hb. pose proof (M_sat _ _ _ _ _ HM) as (Hbd & Hf & Hl & Hg).
  apply (M_same ρ B st); auto.
  - split; [exact Hbd|]. auto.
  - exact (M_wf_flags _ _ _ _ _ HM).
  - exact (M_wf_lin _ _ _ _ _ HM).
Qed.

(** * Substitution

    When two symbols have the same number, the checker replaces one
    by the other everywhere. The state means the same afterwards. *)

Lemma sub_sym_val (ρ : nat -> Z) s t u : ρ s = ρ t -> ρ (sub_sym s t u) = ρ u.
Proof using Type. intros E. unfold sub_sym. destruct (Nat.eqb_spec u s) as [->|_]; auto. Qed.

Lemma sub_sym_lt n s t u : (t < n)%nat -> (u < n)%nat -> (sub_sym s t u < n)%nat.
Proof using Type. intros Ht Hu. unfold sub_sym. destruct (Nat.eqb u s); assumption. Qed.

Lemma dint_sub ρ s t a : ρ s = ρ t -> dint ρ (sub_aint s t a) = dint ρ a.
Proof using Type. intros E. destruct a as [z|u]; cbn; [reflexivity|]. destruct (Nat.eqb_spec u s) as [->|_]; cbn; auto. Qed.

Lemma wf_int_sub n s t a : (t < n)%nat -> wf_int n a -> wf_int n (sub_aint s t a).
Proof using Type. intros Ht. destruct a as [z|u]; cbn; [auto|]. destruct (Nat.eqb u s); cbn; auto. Qed.

Lemma dval_sub ρ B s t v w : ρ s = ρ t -> dval ρ B v w -> dval ρ B (sub_aval s t v) w.
Proof using Type. intros E. destruct v; cbn [dval sub_aval]; rewrite ?(dint_sub ρ s t) by exact E; auto. Qed.

Lemma wf_val_sub n s t v : (t < n)%nat -> wf_val n v -> wf_val n (sub_aval s t v).
Proof using Type.
  intros Ht. destruct v; cbn [wf_val sub_aval]; auto using wf_int_sub.
  intros [H1 H2]. auto using wf_int_sub.
Qed.

Lemma dbyte_sub ρ s t b x : ρ s = ρ t -> dbyte ρ b x -> dbyte ρ (sub_byte s t b) x.
Proof using Type.
  intros E [Hr H]. split; [exact Hr|]. destruct b; cbn [sub_byte]; rewrite ?(sub_sym_val ρ s t) by exact E; exact H.
Qed.

Lemma wf_byte_sub n s t b : (t < n)%nat -> wf_byte n b -> wf_byte n (sub_byte s t b).
Proof using Type. intros Ht. destruct b; cbn [wf_byte sub_byte]; auto using sub_sym_lt. Qed.

Lemma dflag_sub ρ s t u fl : ρ s = ρ t -> dflag ρ u fl -> dflag ρ (sub_sym s t u) (sub_flag s t fl).
Proof using Type. intros E. destruct fl; cbn [dflag sub_flag]; rewrite !(sub_sym_val ρ s t) by exact E; auto. Qed.

Lemma wf_flag_sub n s t fl : (t < n)%nat -> wf_flag n fl -> wf_flag n (sub_flag s t fl).
Proof using Type. intros Ht. destruct fl; cbn [wf_flag sub_flag]; auto using sub_sym_lt. Qed.

Lemma lookup_map_snd {X Y : Type} (f : X -> Y) n (l : list (name * X)) :
  lookup n (map (fun nv => (fst nv, f (snd nv))) l) = option_map f (lookup n l).
Proof using Type. induction l as [|[k v] l IH]; cbn; [reflexivity|]. destruct (name_eqb n k); [reflexivity | exact IH]. Qed.

Lemma Forall2_map_left {X Y Z' : Type} (R : Y -> Z' -> Prop) (f : X -> Y) l l' :
  Forall2 (fun x => R (f x)) l l' -> Forall2 R (map f l) l'.
Proof using Type. induction 1; cbn; constructor; auto. Qed.

Lemma M_sub ρ B st e X s t :
  M ρ B st e X -> ρ s = ρ t -> (t < length (st_bnd st))%nat -> M ρ B (sub_state s t st) e X.
Proof using Type.
  intros (HB & HG & (Hb & Hf & Hl & Hg) & (We & Wf & Wl & Wo) & He & (L1 & L2 & Ho)) E Ht.
  split; [exact HB|]. split; [exact HG|]. unfold sub_state. split; [|split; [|split]].
  - split; [exact Hb|]. split; [|split; [|exact Hg]]; cbn [st_flags st_lin].
    + intros s' fl' Hin. apply in_map_iff in Hin as ([u fl] & [= <- <-] & Hin). apply dflag_sub; auto.
    + intros t' s' c' Hin. apply in_map_iff in Hin as ([[u v] c] & [= <- <- <-] & Hin).
      rewrite !(sub_sym_val ρ s t) by exact E. auto.
  - unfold wf. cbn [st_bnd st_env st_flags st_lin st_objs]. rewrite Forall_forall in We, Wf, Wl, Wo.
    split; [|split; [|split]]; apply Forall_forall.
    + intros nv Hin. apply in_map_iff in Hin as (nv0 & <- & Hin). cbn. apply wf_val_sub; auto.
    + intros f Hin. apply in_map_iff in Hin as ([u fl] & <- & Hin). destruct (Wf _ Hin). cbn in *.
      split; [apply sub_sym_lt | apply wf_flag_sub]; auto.
    + intros l Hin. apply in_map_iff in Hin as ([[u v] c] & <- & Hin). destruct (Wl _ Hin). cbn in *.
      split; apply sub_sym_lt; auto.
    + intros o Hin. apply in_map_iff in Hin as (o0 & <- & Hin). pose proof (Wo _ Hin) as W.
      destruct o0 as [ob|]; cbn in *; [|exact I]. rewrite Forall_forall in W. apply Forall_forall.
      intros b Hb'. apply in_map_iff in Hb' as (b0 & <- & Hb'). apply wf_byte_sub; auto.
  - intros n v. cbn [st_env]. rewrite lookup_map_snd. destruct (lookup n (st_env st)) as [v0|] eqn:E0; [|discriminate].
    intros [= <-]. destruct (He n v0 E0) as (w & Hw & Hv). exists w. split; [exact Hw | apply dval_sub; auto].
  - cbn [st_objs]. split; [rewrite length_map; exact L1|]. split; [exact L2|]. intros i ob Hi.
    rewrite nth_error_map in Hi. destruct (nth_error (st_objs st) i) as [[ob0|]|] eqn:E0; try discriminate.
    injection Hi as <-. destruct (Ho i ob0 E0) as (pl & xs & cs & Hp & Hx & (Hbs & Hrest)).
    exists pl, xs, cs. split; [exact Hp|]. split; [exact Hx|]. split.
    + cbn [sub_obj o_bytes]. apply Forall2_map_left. eapply Forall2_impl; [|exact Hbs].
      intros b x. apply dbyte_sub. exact E.
    + unfold o_size in *. cbn [sub_obj o_bytes o_aux o_ro o_align]. rewrite length_map. exact Hrest.
Qed.

(** * Refinement by a comparison

    A branch tells the checker that a comparison is true or false. The
    refined state is true of every valuation that agrees with the
    outcome, and it exists whenever the outcome is possible. *)

Lemma ref_le_sound ρ B st e X a b :
  M ρ B st e X -> wf_int (length (st_bnd st)) a -> wf_int (length (st_bnd st)) b -> dint ρ a <= dint ρ b ->
  exists st', ref_le st a b = Some st' /\ M ρ B st' e X /\ length (st_bnd st') = length (st_bnd st).
Proof using Type.
  intros HM Wa Wb Hab. unfold ref_le.
  destruct (rng st a) as [alo ahi] eqn:Ea. destruct (rng st b) as [blo bhi] eqn:Eb.
  pose proof (rng_sound _ _ _ _ _ (M_sat _ _ _ _ _ HM) Wa Ea) as Ra.
  pose proof (rng_sound _ _ _ _ _ (M_sat _ _ _ _ _ HM) Wb Eb) as Rb.
  destruct (Z.ltb_spec bhi alo); [lia|].
  destruct (set_rng_sound ρ B st e X a alo (Z.min ahi bhi) HM ltac:(lia)) as [H1 L1].
  destruct (set_rng_sound ρ B _ e X b (Z.max blo alo) bhi H1 ltac:(lia)) as [H2 L2].
  eexists. split; [reflexivity|]. split; [exact H2 | congruence].
Qed.

Lemma ref_lt_sound ρ B st e X a b :
  M ρ B st e X -> wf_int (length (st_bnd st)) a -> wf_int (length (st_bnd st)) b -> dint ρ a < dint ρ b ->
  exists st', ref_lt st a b = Some st' /\ M ρ B st' e X /\ length (st_bnd st') = length (st_bnd st).
Proof using Type.
  intros HM Wa Wb Hab. unfold ref_lt.
  destruct (rng st a) as [alo ahi] eqn:Ea. destruct (rng st b) as [blo bhi] eqn:Eb.
  pose proof (rng_sound _ _ _ _ _ (M_sat _ _ _ _ _ HM) Wa Ea) as Ra.
  pose proof (rng_sound _ _ _ _ _ (M_sat _ _ _ _ _ HM) Wb Eb) as Rb.
  destruct (Z.leb_spec bhi alo); [lia|].
  destruct (set_rng_sound ρ B st e X a alo (Z.min ahi (bhi - 1)) HM ltac:(lia)) as [H1 L1].
  destruct (set_rng_sound ρ B _ e X b (Z.max blo (alo + 1)) bhi H1 ltac:(lia)) as [H2 L2].
  eexists. split; [reflexivity|]. split; [exact H2 | congruence].
Qed.

Lemma ref_eq_sound ρ B st e X a b :
  M ρ B st e X -> wf_int (length (st_bnd st)) a -> wf_int (length (st_bnd st)) b -> dint ρ a = dint ρ b ->
  exists st', ref_eq st a b = Some st' /\ M ρ B st' e X /\ length (st_bnd st') = length (st_bnd st).
Proof using Type.
  intros HM Wa Wb Hab. unfold ref_eq.
  destruct (rng st a) as [alo ahi] eqn:Ea. destruct (rng st b) as [blo bhi] eqn:Eb.
  pose proof (rng_sound _ _ _ _ _ (M_sat _ _ _ _ _ HM) Wa Ea) as Ra.
  pose proof (rng_sound _ _ _ _ _ (M_sat _ _ _ _ _ HM) Wb Eb) as Rb.
  destruct (Z.ltb_spec (Z.min ahi bhi) (Z.max alo blo)); [lia|].
  destruct (set_rng_sound ρ B st e X a (Z.max alo blo) (Z.min ahi bhi) HM ltac:(lia)) as [H1 L1].
  destruct (set_rng_sound ρ B _ e X b (Z.max alo blo) (Z.min ahi bhi) H1 ltac:(lia)) as [H2 L2].
  eexists. split; [reflexivity|].
  destruct a as [za|s]; [split; [exact H2 | congruence]|].
  destruct b as [zb|t]; [split; [exact H2 | congruence]|].
  cbn [dint wf_int] in *. destruct (Nat.eqb s t); [split; [exact H2 | congruence]|].
  destruct (Nat.ltb s t).
  - split; [apply M_sub; [exact H2 | auto | lia] | cbn [sub_state st_bnd]; congruence].
  - split; [apply M_sub; [exact H2 | auto | lia] | cbn [sub_state st_bnd]; congruence].
Qed.

Lemma ref_ne_sound ρ B st e X a b :
  M ρ B st e X -> wf_int (length (st_bnd st)) a -> wf_int (length (st_bnd st)) b -> dint ρ a <> dint ρ b ->
  exists st', ref_ne st a b = Some st' /\ M ρ B st' e X /\ length (st_bnd st') = length (st_bnd st).
Proof using Type.
  intros HM Wa Wb Hab. unfold ref_ne.
  destruct (rng st a) as [alo ahi] eqn:Ea. destruct (rng st b) as [blo bhi] eqn:Eb.
  pose proof (rng_sound _ _ _ _ _ (M_sat _ _ _ _ _ HM) Wa Ea) as Ra.
  pose proof (rng_sound _ _ _ _ _ (M_sat _ _ _ _ _ HM) Wb Eb) as Rb.
  destruct (Z.eqb_spec alo ahi) as [E1|E1]; destruct (Z.eqb_spec blo bhi) as [E2|E2];
    destruct (Z.eqb_spec alo blo) as [E3|E3]; cbn [andb]; try lia;
    repeat match goal with
           | |- context [Z.eqb ?x ?y] => destruct (Z.eqb_spec x y)
           end;
    try (eexists; split; [reflexivity|]; split; [exact HM | reflexivity]);
    try (eexists; split; [reflexivity|]; apply set_rng_sound; [exact HM | lia]).
Qed.

Lemma In_flag_picks {Y : Type} st s (pick : flag -> option Y) x :
  In x (flag_picks st s pick) -> exists fl, In (s, fl) (st_flags st) /\ pick fl = Some x.
Proof using Type.
  unfold flag_picks. intros Hin. apply in_flat_map in Hin as ([u fl] & Hin & Hx). cbn [fst snd] in Hx.
  destruct (Nat.eqb_spec u s) as [->|_]; [|destruct Hx]. destruct (pick fl) as [y|] eqn:E; [|destruct Hx].
  destruct Hx as [<-|[]]. exists fl. auto.
Qed.

Lemma flag_eqb_eq a b : flag_eqb a b = true -> a = b.
Proof using Type.
  destruct a, b; cbn; try discriminate; auto.
  - intros H. apply Z.eqb_eq in H. congruence.
  - intros H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
    apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2, H3. congruence.
  - intros H. apply andb_true_iff in H as [H1 H2]. apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. congruence.
Qed.

Lemma has_flag_In st s fl : has_flag st s fl = true -> In (s, fl) (st_flags st).
Proof using Type.
  unfold has_flag. intros H. apply existsb_exists in H as ([u fl'] & Hin & H). cbn [fst snd] in H.
  apply andb_true_iff in H as [H1 H2]. apply Nat.eqb_eq in H1. apply flag_eqb_eq in H2. subst. exact Hin.
Qed.

(** The checker learns from a branch that a number is not zero. This
    lemma shows that what it records is true. If the number is a
    symbol with the flag [FNz], then the guard holds. If the symbol
    has the flag [FEndNz], then the symbol that the flag names differs
    from the flag's key. *)
Lemma note_nonzero_sound ρ B st e X a :
  M ρ B st e X -> wf_int (length (st_bnd st)) a -> dint ρ a <> 0 ->
  exists st', note_nonzero st a = Some st' /\ M ρ B st' e X /\ length (st_bnd st') = length (st_bnd st).
Proof using Type.
  intros HM Wa Ha. destruct a as [z|s]; cbn [note_nonzero dint wf_int] in *; [eauto|].
  pose proof (M_sat _ _ _ _ _ HM) as (_ & Hf & _). pose proof (M_wf_flags _ _ _ _ _ HM) as Wf.
  set (picks := flag_picks st s (fun fl => match fl with FEndNz u key => Some (u, key) | _ => None end)).
  assert (Hp : forall uk, In uk picks -> ρ (fst uk) <> snd uk /\ (fst uk < length (st_bnd st))%nat).
  { intros [u key] Hin. apply In_flag_picks in Hin as (fl & Hin & E). destruct fl; try discriminate.
    injection E as <- <-. pose proof (Hf _ _ Hin) as H. cbn [dflag] in H. rewrite Forall_forall in Wf.
    destruct (Wf _ Hin) as [_ W]. cbn in W. cbn [fst snd]. split; [intros E; apply Ha, H, E | exact W]. }
  assert (H0 : exists st0, Some (if has_flag st s FNz then set_guard st true else st) = Some st0 /\
                           M ρ B st0 e X /\ length (st_bnd st0) = length (st_bnd st)).
  { eexists. split; [reflexivity|]. destruct (has_flag st s FNz) eqn:E; [|auto].
    split; [|reflexivity]. apply M_set_guard; [exact HM|]. intros _.
    exact (Hf _ _ (has_flag_In _ _ _ E) Ha). }
  revert H0. generalize (Some (if has_flag st s FNz then set_guard st true else st)).
  clearbody picks. induction picks as [|[u key] picks IH]; intros acc (st0 & E0 & H0 & L0); cbn [fold_left].
  - exists st0. auto.
  - apply IH; [intros uk Hin; apply Hp; right; exact Hin|]. rewrite E0.
    destruct (Hp (u, key) (or_introl eq_refl)) as [Hne Hu]. cbn [fst snd] in *.
    destruct (ref_ne_sound ρ B st0 e X (S u) (K key) H0) as (st1 & E1 & H1 & L1); [cbn; lia | exact I | exact Hne |].
    exists st1. split; [exact E1|]. split; [exact H1 | congruence].
Qed.

Lemma cond_bit_01 c k x y r : cond_bit c k x y = Some r -> r = 0 \/ r = 1.
Proof using Type.
  destruct c; cbn; try discriminate; destruct (signed k x); try discriminate; destruct (signed k y); try discriminate;
    intros [= <-]; match goal with |- context [if ?b then _ else _] => destruct b end; auto.
Qed.

Lemma cond_bit_negate c k x y : cond_bit c k x y = Some 0 -> cond_bit (negate c) k x y = Some 1.
Proof using Type.
  destruct c; cbn; try discriminate; destruct (signed k x) as [sx|]; try discriminate;
    destruct (signed k y) as [sy|]; try discriminate;
    repeat match goal with
           | |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b)
           | |- context [Z.ltb ?a ?b] => destruct (Z.ltb_spec a b)
           | |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b)
           end; cbn; try discriminate; try reflexivity; lia.
Qed.

Lemma sign_extension_small m h u : 0 <= u < h -> h <= m -> sign_extension m h u = u.
Proof using Type. intros Hu Hm. unfold sign_extension. rewrite Z.mod_small by lia. destruct (Z.leb_spec h u); lia. Qed.

Lemma nonneg_half_sound ρ st k a sx :
  sat ρ st -> wf_int (length (st_bnd st)) a -> nonneg_half st k a = true ->
  signed k (dint ρ a) = Some sx -> sx = dint ρ a.
Proof using Type.
  intros Hs Wa. unfold nonneg_half. destruct (rng st a) as [lo hi] eqn:E.
  pose proof (rng_sound _ _ _ _ _ Hs Wa E) as R. intros H. apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold signed, half in *.
  destruct k; try discriminate; intros [= <-]; apply sign_extension_small; try lia; compute; discriminate.
Qed.

Lemma refine1_sound ρ B st e X c k a b :
  M ρ B st e X -> wf_int (length (st_bnd st)) a -> wf_int (length (st_bnd st)) b ->
  cond_bit c k (dint ρ a) (dint ρ b) = Some 1 ->
  exists st', refine1 st c k a b = Some st' /\ M ρ B st' e X /\ length (st_bnd st') = length (st_bnd st).
Proof using Type.
  intros HM Wa Wb. pose proof (M_sat _ _ _ _ _ HM) as Hs.
  destruct c; cbn [cond_bit refine1]; try discriminate.
  - destruct (Z.eqb_spec (dint ρ a) (dint ρ b)); [|discriminate]. intros _. apply ref_eq_sound; auto.
  - destruct (Z.eqb_spec (dint ρ a) (dint ρ b)); [discriminate|]. intros _.
    destruct (ref_ne_sound ρ B st e X a b HM Wa Wb) as (st1 & E1 & H1 & L1); [assumption|]. rewrite E1.
    assert (Hdef : exists st', Some st1 = Some st' /\ M ρ B st' e X /\ length (st_bnd st') = length (st_bnd st)) by eauto.
    destruct b as [[| |]|]; try exact Hdef. cbn [dint] in *.
    destruct (note_nonzero_sound ρ B st1 e X a H1) as (st2 & E2 & H2 & L2); [rewrite L1; exact Wa | assumption |].
    exists st2. split; [exact E2|]. split; [exact H2 | congruence].
  - destruct (signed k (dint ρ a)) as [sx|] eqn:Ex; [|discriminate].
    destruct (signed k (dint ρ b)) as [sy|] eqn:Ey; [|discriminate].
    destruct (Z.leb_spec sx sy); [|discriminate]. intros _.
    destruct (nonneg_half st k a && nonneg_half st k b) eqn:En; [|eauto].
    apply andb_true_iff in En as [Na Nb]. pose proof (nonneg_half_sound _ _ _ _ _ Hs Wa Na Ex).
    pose proof (nonneg_half_sound _ _ _ _ _ Hs Wb Nb Ey). apply ref_le_sound; auto; lia.
  - destruct (signed k (dint ρ a)) as [sx|] eqn:Ex; [|discriminate].
    destruct (signed k (dint ρ b)) as [sy|] eqn:Ey; [|discriminate].
    destruct (Z.ltb_spec sx sy); [|discriminate]. intros _.
    destruct (nonneg_half st k a && nonneg_half st k b) eqn:En; [|eauto].
    apply andb_true_iff in En as [Na Nb]. pose proof (nonneg_half_sound _ _ _ _ _ Hs Wa Na Ex).
    pose proof (nonneg_half_sound _ _ _ _ _ Hs Wb Nb Ey). apply ref_lt_sound; auto; lia.
  - destruct (signed k (dint ρ a)) as [sx|] eqn:Ex; [|discriminate].
    destruct (signed k (dint ρ b)) as [sy|] eqn:Ey; [|discriminate].
    destruct (Z.leb_spec sy sx); [|discriminate]. intros _.
    destruct (nonneg_half st k a && nonneg_half st k b) eqn:En; [|eauto].
    apply andb_true_iff in En as [Na Nb]. pose proof (nonneg_half_sound _ _ _ _ _ Hs Wa Na Ex).
    pose proof (nonneg_half_sound _ _ _ _ _ Hs Wb Nb Ey). apply ref_le_sound; auto; lia.
  - destruct (signed k (dint ρ a)) as [sx|] eqn:Ex; [|discriminate].
    destruct (signed k (dint ρ b)) as [sy|] eqn:Ey; [|discriminate].
    destruct (Z.ltb_spec sy sx); [|discriminate]. intros _.
    destruct (nonneg_half st k a && nonneg_half st k b) eqn:En; [|eauto].
    apply andb_true_iff in En as [Na Nb]. pose proof (nonneg_half_sound _ _ _ _ _ Hs Wa Na Ex).
    pose proof (nonneg_half_sound _ _ _ _ _ Hs Wb Nb Ey). apply ref_lt_sound; auto; lia.
  - destruct (Z.leb_spec (dint ρ a) (dint ρ b)); [|discriminate]. intros _. apply ref_le_sound; auto.
  - destruct (Z.ltb_spec (dint ρ a) (dint ρ b)); [|discriminate]. intros _. apply ref_lt_sound; auto.
  - destruct (Z.leb_spec (dint ρ b) (dint ρ a)); [|discriminate]. intros _. apply ref_le_sound; auto.
  - destruct (Z.ltb_spec (dint ρ b) (dint ρ a)); [|discriminate]. intros _. apply ref_lt_sound; auto.
Qed.

(** A comparison whose result is r refines the state on the side that
    r selects. In particular that side of the branch is not ruled out. *)
Lemma refine_sound ρ B st e X c k a b r :
  M ρ B st e X -> wf_int (length (st_bnd st)) a -> wf_int (length (st_bnd st)) b ->
  cond_bit c k (dint ρ a) (dint ρ b) = Some r ->
  exists st', refine st c k a b (negb (r =? 0)) = Some st' /\ M ρ B st' e X /\
              length (st_bnd st') = length (st_bnd st).
Proof using Type.
  intros HM Wa Wb Hc. unfold refine. destruct (cond_bit_01 _ _ _ _ _ Hc) as [-> | ->]; cbn [Z.eqb negb].
  - apply refine1_sound; auto. apply cond_bit_negate. exact Hc.
  - apply refine1_sound; auto.
Qed.

(** * Steps that add symbols

    A step of the checker may add symbols. The valuation after the step
    agrees with the valuation before it on the old symbols, so every
    value read before the step keeps its meaning. *)

Definition step (ρ : nat -> Z) (st : astate) (ρ' : nat -> Z) (st' : astate) : Prop :=
  agree (length (st_bnd st)) ρ ρ' /\ (length (st_bnd st) <= length (st_bnd st'))%nat.

Lemma step_refl ρ st : step ρ st ρ st.
Proof using Type. split; [apply agree_refl | lia]. Qed.

Lemma step_same ρ st st' : length (st_bnd st') = length (st_bnd st) -> step ρ st ρ st'.
Proof using Type. intros E. split; [apply agree_refl | lia]. Qed.

Lemma step_trans ρ1 st1 ρ2 st2 ρ3 st3 : step ρ1 st1 ρ2 st2 -> step ρ2 st2 ρ3 st3 -> step ρ1 st1 ρ3 st3.
Proof using Type. intros [A1 L1] [A2 L2]. split; [eapply agree_trans; eauto | lia]. Qed.

Lemma step_val ρ st ρ' st' B v w :
  step ρ st ρ' st' -> wf_val (length (st_bnd st)) v -> dval ρ B v w ->
  wf_val (length (st_bnd st')) v /\ dval ρ' B v w.
Proof using Type. intros [Ha Hl] Wv Hv. split; [eapply wf_val_mono; eauto | eapply dval_agree; eauto]. Qed.

Lemma step_vals ρ st ρ' st' B vs ws :
  step ρ st ρ' st' -> Forall (wf_val (length (st_bnd st))) vs -> Forall2 (dval ρ B) vs ws ->
  Forall (wf_val (length (st_bnd st'))) vs /\ Forall2 (dval ρ' B) vs ws.
Proof using Type.
  intros [Ha Hl] Wv Hv. split; [|eapply dvals_agree; eauto].
  eapply Forall_impl; [|exact Wv]. intros v. apply wf_val_mono. exact Hl.
Qed.

Lemma step_int ρ st ρ' st' a :
  step ρ st ρ' st' -> wf_int (length (st_bnd st)) a ->
  wf_int (length (st_bnd st')) a /\ dint ρ' a = dint ρ a.
Proof using Type. intros [Ha Hl] Wa. split; [eapply wf_int_mono; eauto | eapply dint_agree; eauto]. Qed.

(** The result [R] of a step is a new state, true under a valuation
    that extends the old one, together with a value that describes the
    word the step produced. *)
Definition R (ρ : nat -> Z) (B : list place) (e : env) (X : cont) (st st' : astate) (x : aval) (w : word) : Prop :=
  exists ρ', M ρ' B st' e X /\ step ρ st ρ' st' /\ wf_val (length (st_bnd st')) x /\ dval ρ' B x w.

Lemma fresh_sound ρ B st e X lo hi z s st' :
  M ρ B st e X -> lo <= z <= hi -> fresh st lo hi = (s, st') ->
  exists ρ', M ρ' B st' e X /\ step ρ st ρ' st' /\ (s < length (st_bnd st'))%nat /\ ρ' s = z.
Proof using Type.
  intros HM Hz E. pose proof (M_fresh ρ B st e X lo hi z HM Hz) as H. unfold fresh in *. injection E as <- <-.
  exists (upd ρ (length (st_bnd st)) z). split; [exact H|]. unfold step. cbn [st_bnd]. rewrite length_app. cbn [length].
  split; [split; [apply agree_upd | lia]|]. split; [lia | apply upd_same].
Qed.

Lemma mk_sound ρ B st e X lo hi z a st' :
  M ρ B st e X -> lo <= z <= hi -> mk st lo hi = (a, st') ->
  exists ρ', M ρ' B st' e X /\ step ρ st ρ' st' /\ wf_int (length (st_bnd st')) a /\ dint ρ' a = z.
Proof using Type.
  intros HM Hz. unfold mk. destruct (Z.eqb_spec lo hi) as [Elh|_].
  - intros [= <- <-]. exists ρ. split; [exact HM|]. split; [apply step_refl|]. split; [exact I | cbn; lia].
  - destruct (fresh st lo hi) as [s st1] eqn:E. intros [= <- <-].
    destruct (fresh_sound ρ B st e X lo hi z s st1 HM Hz E) as (ρ' & H1 & H2 & H3 & H4). exists ρ'. auto.
Qed.

Lemma lookup_In {Y : Type} n (l : list (name * Y)) v : lookup n l = Some v -> exists k, In (k, v) l.
Proof using Type.
  induction l as [|[k v'] l IH]; cbn; [discriminate|].
  destruct (name_eqb n k); [intros [= ->]; exists k; auto|].
  intros H. destruct (IH H) as [k' Hk]. exists k'. auto.
Qed.

Lemma M_env ρ B st e X n v :
  M ρ B st e X -> lookup n (st_env st) = Some v ->
  wf_val (length (st_bnd st)) v /\ exists w, lookup n e = Some w /\ dval ρ B v w.
Proof using Type.
  intros (_ & _ & _ & (We & _) & He & _) E. split; [|exact (He n v E)].
  destruct (lookup_In _ _ _ E) as [k Hk]. rewrite Forall_forall in We. exact (We _ Hk).
Qed.

(** * Reading operands *)

(** An integer operand read at a class of modulus m is reduced modulo m. *)
Definition int_at (m : Z) (v : aval) (st : astate) : option (aval * astate) :=
  match v with
  | VI a => let (lo, hi) := rng st a in
            if (0 <=? lo) && (hi <? m) then Some (v, st)
            else let (s, st') := fresh st 0 (m - 1) in Some (VI (S s), st')
  | VC _ _ _ _ => Some (v, st)
  | VJ => let (s, st') := fresh st 0 (m - 1) in Some (VI (S s), st')
  | _ => None
  end.

Lemma int_at_sound ρ B st e X m v w x st' :
  1 < m -> M ρ B st e X -> wf_val (length (st_bnd st)) v -> dval ρ B v w -> int_at m v st = Some (x, st') ->
  exists n, w = WInt n /\ R ρ B e X st st' x (WInt (n mod m)).
Proof using Type.
  intros Hm HM Wv Hv. pose proof (M_sat _ _ _ _ _ HM) as Hs.
  destruct v as [a|c k a b| |o a|a| |g]; cbn [int_at dval wf_val] in *; try discriminate.
  - destruct (rng st a) as [lo hi] eqn:E. pose proof (rng_sound _ _ _ _ _ Hs Wv E) as Rg.
    destruct ((0 <=? lo) && (hi <? m)) eqn:Eb.
    + apply andb_true_iff in Eb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. intros [= <- <-].
      exists (dint ρ a). split; [exact Hv|].
      exists ρ. split; [exact HM|]. split; [apply step_refl|]. split; [exact Wv|]. cbn [dval].
      rewrite Z.mod_small by lia. reflexivity.
    + destruct (fresh st 0 (m - 1)) as [s st1] eqn:Ef. intros [= <- <-].
      exists (dint ρ a). split; [exact Hv|].
      destruct (fresh_sound ρ B st e X 0 (m - 1) (dint ρ a mod m) s st1 HM) as (ρ' & H1 & H2 & H3 & H4);
        [pose proof (Z.mod_pos_bound (dint ρ a) m); lia | exact Ef |].
      exists ρ'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. cbn [dval dint]. congruence.
  - destruct Hv as (r & Hc & ->). intros [= <- <-]. exists r. split; [reflexivity|].
    exists ρ. split; [exact HM|]. split; [apply step_refl|]. split; [exact Wv|]. cbn [dval]. exists r.
    split; [exact Hc|]. rewrite Z.mod_small; [reflexivity|]. destruct (cond_bit_01 _ _ _ _ _ Hc); lia.
  - destruct Hv as (n & ->).
    destruct (fresh st 0 (m - 1)) as [s st1] eqn:Ef. intros [= <- <-]. exists n. split; [reflexivity|].
    destruct (fresh_sound ρ B st e X 0 (m - 1) (n mod m) s st1 HM) as (ρ' & H1 & H2 & H3 & H4);
      [pose proof (Z.mod_pos_bound n m); lia | exact Ef |].
    exists ρ'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. cbn [dval dint]. congruence.
Qed.

Lemma tmp_at_sound ρ B st e X k v w x st' :
  M ρ B st e X -> wf_val (length (st_bnd st)) v -> dval ρ B v w -> tmp_at k v st = Some (x, st') ->
  exists w', word_at_class k w = Some w' /\ R ρ B e X st st' x w'.
Proof using Type.
  intros HM Wv Hv. destruct k; try discriminate.
  - change (tmp_at W v st) with (int_at (2 ^ 32) v st). intros E.
    destruct (int_at_sound ρ B st e X (2 ^ 32) v w x st' ltac:(reflexivity) HM Wv Hv E) as (n & -> & H).
    eexists. split; [reflexivity | exact H].
  - change (tmp_at L v st) with (int_at (2 ^ 64) v st). intros E.
    destruct (int_at_sound ρ B st e X (2 ^ 64) v w x st' ltac:(reflexivity) HM Wv Hv E) as (n & -> & H).
    eexists. split; [reflexivity | exact H].
  - intros [= <- <-]. exists w. split; [reflexivity|]. exists ρ. split; [exact HM|]. split; [apply step_refl | auto].
  - intros [= <- <-]. exists w. split; [reflexivity|]. exists ρ. split; [exact HM|]. split; [apply step_refl | auto].
  - intros [= <- <-]. exists w. split; [reflexivity|]. exists ρ. split; [exact HM|]. split; [apply step_refl | auto].
Qed.

Lemma index_of_nth n l i : index_of n l = Some i -> nth_error l i = Some n.
Proof using Type.
  revert i. induction l as [|x l IH]; cbn; [discriminate|]. intros i.
  destruct (name_eqb n x) eqn:E.
  - intros [= <-]. apply term_eqb_eq in E. subst. reflexivity.
  - destruct (index_of n l) as [j|]; [|discriminate]. intros [= <-]. cbn. apply IH. reflexivity.
Qed.

Hypothesis Hfn : fnames_ok.

Lemma R_same ρ B e X st x w : M ρ B st e X -> wf_val (length (st_bnd st)) x -> dval ρ B x w -> R ρ B e X st st x w.
Proof using Type. intros HM Wx Hx. exists ρ. split; [exact HM|]. split; [apply step_refl | auto]. Qed.

(** An operand that the checker reads describes the word that the
    program reads. *)
Lemma avalue_sound ρ B st e X k v x st' :
  M ρ B st e X -> avalue gobjs fnames k v st = Some (x, st') ->
  exists w, value_x ge e k v = Some w /\ R ρ B e X st st' x w.
Proof using Hfn.
  intros HM. destruct v as [n|n|s]; cbn [avalue value_x].
  - destruct (lookup n (st_env st)) as [x0|] eqn:E; [|discriminate]. intros Ht.
    destruct (M_env _ _ _ _ _ _ _ HM E) as (W0 & w0 & El & Hv). rewrite El.
    exact (tmp_at_sound ρ B st e X k x0 w0 x st' HM W0 Hv Ht).
  - destruct k; try discriminate; intros [= <- <-]; (eexists; split; [reflexivity|]);
      apply R_same; try exact HM; try exact I; reflexivity.
  - destruct (index_of s gobjs) as [o|] eqn:E.
    + intros [= <- <-]. apply index_of_nth in E. destruct HM as (HB & HG & HM').
      destruct (HG o s E) as (pl & Hp & Hl). rewrite Hl. eexists. split; [reflexivity|].
      apply R_same; [exact (conj HB (conj HG HM')) | exact I |]. exists pl. split; [exact Hp|].
      cbn [dint]. rewrite Z.add_0_r. reflexivity.
    + destruct (lookup s fnames) as [[ks rt]|] eqn:E'; intros [= <- <-].
      * destruct (Hfn s ks rt E') as [(p & Hl & Hc) _]. rewrite Hl. eexists. split; [reflexivity|].
        apply R_same; [exact HM | exact I |]. exists p. auto.
      * destruct (lookup s (ge_globals ge)); (eexists; split; [reflexivity|]);
          (apply R_same; [exact HM | exact I |]); eexists; reflexivity.
Qed.

(** The result of several steps is a list of values under one valuation. *)
Definition Rs (ρ : nat -> Z) (B : list place) (e : env) (X : cont) (st st' : astate) (xs : list aval) (ws : list word) : Prop :=
  exists ρ', M ρ' B st' e X /\ step ρ st ρ' st' /\ Forall (wf_val (length (st_bnd st'))) xs /\ Forall2 (dval ρ' B) xs ws.

Lemma avalues_sound ρ B st e X ks vs xs st' :
  M ρ B st e X -> avalues gobjs fnames ks vs st = Some (xs, st') ->
  exists ws, map2_option (value_x ge e) ks vs = Some ws /\ Rs ρ B e X st st' xs ws.
Proof using Hfn.
  revert ρ st vs xs st'. induction ks as [|k ks IH]; intros ρ st [|v vs] xs st' HM; cbn [avalues map2_option]; try discriminate.
  - intros [= <- <-]. exists []. split; [reflexivity|]. exists ρ. split; [exact HM|]. split; [apply step_refl|]. auto.
  - destruct (avalue gobjs fnames k v st) as [[x st1]|] eqn:E1; [|discriminate].
    destruct (avalues gobjs fnames ks vs st1) as [[xs' st2]|] eqn:E2; [|discriminate]. intros [= <- <-].
    destruct (avalue_sound ρ B st e X k v x st1 HM E1) as (w & Ev & ρ1 & H1 & S1 & W1 & D1).
    destruct (IH ρ1 st1 vs xs' st2 H1 E2) as (ws & Evs & ρ2 & H2 & S2 & W2 & D2). rewrite Ev, Evs.
    exists (w :: ws). split; [reflexivity|]. exists ρ2. split; [exact H2|]. split; [eapply step_trans; eauto|].
    destruct (step_val _ _ _ _ B x w S2 W1 D1). split; constructor; auto.
Qed.

(** * Arithmetic *)

(** A comparison result used as a number is 0 or 1. *)
Lemma as_int_sound ρ B st e X v w x st' :
  M ρ B st e X -> wf_val (length (st_bnd st)) v -> dval ρ B v w -> as_int v st = (x, st') ->
  R ρ B e X st st' x w.
Proof using Type.
  intros HM Wv Hv. destruct v as [a|c k a b| |o a|a| |g]; cbn [as_int];
    try (intros [= <- <-]; apply R_same; assumption).
  cbn [dval wf_val] in *. destruct Hv as (r & Hc & ->). destruct Wv as [Wa Wb].
  destruct (refine_sound ρ B st e X c k a b r HM Wa Wb Hc) as (st1 & E1 & _).
  destruct (cond_bit_01 _ _ _ _ _ Hc) as [-> | ->]; cbn [Z.eqb negb] in E1; rewrite E1.
  - destruct (refine st c k a b true) eqn:Et.
    + destruct (fresh st 0 1) as [s st2] eqn:Ef. intros [= <- <-].
      destruct (fresh_sound ρ B st e X 0 1 0 s st2 HM ltac:(lia) Ef) as (ρ' & H1 & H2 & H3 & H4).
      exists ρ'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. cbn [dval dint]. congruence.
    + intros [= <- <-]. apply R_same; [exact HM | exact I | reflexivity].
  - destruct (refine st c k a b false) eqn:Et.
    + destruct (fresh st 0 1) as [s st2] eqn:Ef. intros [= <- <-].
      destruct (fresh_sound ρ B st e X 0 1 1 s st2 HM ltac:(lia) Ef) as (ρ' & H1 & H2 & H3 & H4).
      exists ρ'. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. cbn [dval dint]. congruence.
    + intros [= <- <-]. apply R_same; [exact HM | exact I | reflexivity].
Qed.

Lemma as_ints_sound ρ B st e X vs ws xs st' :
  M ρ B st e X -> Forall (wf_val (length (st_bnd st))) vs -> Forall2 (dval ρ B) vs ws ->
  as_ints vs st = (xs, st') -> Rs ρ B e X st st' xs ws.
Proof using Type.
  revert ρ st ws xs st'. induction vs as [|v vs IH]; intros ρ st ws xs st' HM Wv Hv; cbn [as_ints].
  - intros [= <- <-]. inversion Hv; subst. exists ρ. split; [exact HM|]. split; [apply step_refl|]. auto.
  - destruct (as_int v st) as [x st1] eqn:E1. destruct (as_ints vs st1) as [xs' st2] eqn:E2. intros [= <- <-].
    inversion Hv as [|? w ? ws' Hv1 Hv2]; subst. inversion Wv as [|? ? Wv1 Wv2]; subst.
    destruct (as_int_sound ρ B st e X v w x st1 HM Wv1 Hv1 E1) as (ρ1 & H1 & S1 & W1 & D1).
    destruct (step_vals _ _ _ _ B vs ws' S1 Wv2 Hv2) as [Wv2' Hv2'].
    destruct (IH ρ1 st1 ws' xs' st2 H1 Wv2' Hv2' E2) as (ρ2 & H2 & S2 & W2 & D2).
    exists ρ2. split; [exact H2|]. split; [eapply step_trans; eauto|].
    destruct (step_val _ _ _ _ B x w S2 W1 D1). split; constructor; auto.
Qed.

Lemma land_le x y : 0 <= x -> 0 <= y -> 0 <= Z.land x y <= y.
Proof using Type.
  intros Hx Hy. split; [apply Z.land_nonneg; auto|].
  apply (Z.ldiff_le _ _ Hy). apply Z.bits_inj'. intros i Hi.
  rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0. destruct (Z.testbit x i), (Z.testbit y i); reflexivity.
Qed.

Lemma lor_bound a b h : 0 <= a <= h -> 0 <= b <= h -> 0 <= Z.lor a b <= 2 ^ (Z.log2 h + 1) - 1.
Proof using Type.
  intros Ha Hb. assert (H0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia). split; [exact H0|].
  pose proof (Z.log2_nonneg h) as Hl.
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hne]; [pose proof (Z.pow_pos_nonneg 2 (Z.log2 h + 1)); lia|].
  assert (Hlt : Z.lor a b < 2 ^ (Z.log2 h + 1)).
  { apply Z.log2_lt_pow2; [lia|]. rewrite Z.log2_lor by lia.
    pose proof (Z.log2_le_mono a h). pose proof (Z.log2_le_mono b h). lia. }
  lia.
Qed.

Lemma lxor_bound a b h : 0 <= a <= h -> 0 <= b <= h -> 0 <= Z.lxor a b <= 2 ^ (Z.log2 h + 1) - 1.
Proof using Type.
  intros Ha Hb. assert (H0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia). split; [exact H0|].
  pose proof (Z.log2_nonneg h) as Hl.
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hne]; [pose proof (Z.pow_pos_nonneg 2 (Z.log2 h + 1)); lia|].
  assert (Hlt : Z.lxor a b < 2 ^ (Z.log2 h + 1)).
  { apply Z.log2_lt_pow2; [lia|]. pose proof (Z.log2_lxor a b).
    pose proof (Z.log2_le_mono a h). pose proof (Z.log2_le_mono b h). lia. }
  lia.
Qed.

(** The two integer classes share one proof. The record [icls] lists
    what the proof needs to know about a class: its modulus m, its
    sign threshold h and its width in bits. *)
Record icls (k : class) (m h bits : Z) : Prop := mkIcls {
  ic_mod : modulus k = Some m;
  ic_half : half_modulus k = Some h;
  ic_bits : class_bits k = Some bits;
  ic_halfk : half k = h;
  ic_sh : match k with W => 32 | _ => 64 end = bits;
  ic_m : m = 2 * h;
  ic_h : 1 <= h;
  ic_b : 0 < bits;
  ic_le : m <= 2 ^ 64;
  ic_fmt : fmt_of k = None;
  ic_k : k = W \/ k = L
}.

Lemma icls_of k m : modulus_of k = Some m -> exists h bits, icls k m h bits.
Proof using Type.
  destruct k; cbn [modulus_of]; try discriminate; intros [= <-].
  - exists (2 ^ 31), 32. split; try reflexivity; try easy. auto.
  - exists (2 ^ 63), 64. split; try reflexivity; try easy. auto.
Qed.

Lemma clamp_sound ρ B st e X m lo hi v a st' :
  0 < m -> M ρ B st e X -> lo <= v <= hi -> clamp st m lo hi = (a, st') ->
  exists ρ', M ρ' B st' e X /\ step ρ st ρ' st' /\ wf_int (length (st_bnd st')) a /\ dint ρ' a = v mod m.
Proof using Type.
  intros Hm HM Hv. unfold clamp. destruct ((0 <=? lo) && (hi <? m)) eqn:E.
  - apply andb_true_iff in E as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    rewrite Z.mod_small by lia. apply mk_sound; assumption.
  - apply mk_sound; [exact HM|]. pose proof (Z.mod_pos_bound v m). lia.
Qed.

(** An arithmetic step of the checker is correct when it agrees with
    the machine. The machine computes the number [z]. The checker
    returns a new state and an abstract result. The new state must be
    true under a valuation that extends the old one, and the result
    must stand for [z] under that valuation. *)
Definition Ri (ρ : nat -> Z) (B : list place) (e : env) (X : cont) (st st' : astate) (r : aint) (z : Z) : Prop :=
  exists ρ', M ρ' B st' e X /\ step ρ st ρ' st' /\ wf_int (length (st_bnd st')) r /\ dint ρ' r = z.

Lemma fin_mk ρ B st e X lo hi z r st' :
  M ρ B st e X -> lo <= z <= hi -> Some (mk st lo hi) = Some (r, st') -> Ri ρ B e X st st' r z.
Proof using Type. intros HM Hz [= E]. exact (mk_sound ρ B st e X lo hi z r st' HM Hz E). Qed.

Lemma fin_clamp ρ B st e X m lo hi v r st' :
  0 < m -> M ρ B st e X -> lo <= v <= hi -> Some (clamp st m lo hi) = Some (r, st') ->
  Ri ρ B e X st st' r (v mod m).
Proof using Type. intros Hm HM Hz [= E]. exact (clamp_sound ρ B st e X m lo hi v r st' Hm HM Hz E). Qed.

Lemma abin_rng_sound ρ B st e X o k m h bits x y r st' :
  icls k m h bits -> M ρ B st e X ->
  wf_int (length (st_bnd st)) x -> wf_int (length (st_bnd st)) y ->
  abin_rng o k m x y st = Some (r, st') ->
  exists z, alu o k [WInt (dint ρ x); WInt (dint ρ y)] = Some (WInt z) /\ Ri ρ B e X st st' r z.
Proof using Type.
  intros [Hmod Hhalf Hbits Hhk Hsh Hm Hh Hb Hle _ _] HM Wx Wy. pose proof (M_sat _ _ _ _ _ HM) as Hs. unfold abin_rng.
  destruct (rng st x) as [xlo xhi] eqn:Ex. destruct (rng st y) as [ylo yhi] eqn:Ey.
  pose proof (rng_sound _ _ _ _ _ Hs Wx Ex) as Rx. pose proof (rng_sound _ _ _ _ _ Hs Wy Ey) as Ry.
  destruct ((0 <=? xlo) && (xhi <? m) && (0 <=? ylo) && (yhi <? 2 ^ 64)) eqn:Ec; cbn [negb]; [|discriminate].
  apply andb_true_iff in Ec as [Ec H4]. apply andb_true_iff in Ec as [Ec H3]. apply andb_true_iff in Ec as [H1 H2].
  apply Z.leb_le in H1, H3. apply Z.ltb_lt in H2, H4. rewrite Hsh, Hhk.
  assert (Hm0 : 0 < m) by lia.
  assert (Hp : forall c, 0 < 2 ^ (c mod bits)).
  { intros c. apply Z.pow_pos_nonneg; [lia|]. pose proof (Z.mod_pos_bound c bits Hb). lia. }
  destruct o; try discriminate; cbn [alu]; unfold shift_factor, signed_division, signed, unsigned_division;
    rewrite ?Hmod, ?Hhalf, ?Hbits.
  - (* Add *) intros E. eexists. split; [reflexivity|]. refine (fin_clamp ρ B st e X m _ _ _ r st' Hm0 HM _ E). lia.
  - (* Sub *) intros E. eexists. split; [reflexivity|]. refine (fin_clamp ρ B st e X m _ _ _ r st' Hm0 HM _ E). lia.
  - (* Mul *) intros E. eexists. split; [reflexivity|]. refine (fin_clamp ρ B st e X m _ _ _ r st' Hm0 HM _ E). nia.
  - (* Div *)
    destruct ((xhi <? h) && (yhi <? h)) eqn:Eh; intros E; (eexists; split; [reflexivity|]).
    + apply andb_true_iff in Eh as [Hx Hy]. apply Z.ltb_lt in Hx, Hy.
      rewrite !sign_extension_small by lia. refine (fin_mk ρ B st e X _ _ _ r st' HM _ E).
      destruct (Z.eqb_spec (dint ρ y) 0); [lia|].
      pose proof (Z.quot_pos (dint ρ x) (dint ρ y) ltac:(lia) ltac:(lia)).
      pose proof (Z.quot_le_upper_bound (dint ρ x) (dint ρ y) (dint ρ x) ltac:(lia) ltac:(nia)).
      rewrite Z.mod_small by lia. lia.
    + refine (fin_mk ρ B st e X _ _ _ r st' HM _ E).
      destruct (_ =? 0); [lia|]. match goal with |- _ <= ?a mod m <= _ => pose proof (Z.mod_pos_bound a m) end. lia.
  - (* Udiv *) intros E. eexists. split; [reflexivity|]. refine (fin_mk ρ B st e X _ _ _ r st' HM _ E).
    destruct (Z.eqb_spec (dint ρ y) 0); [lia|].
    pose proof (Z.div_pos (dint ρ x) (dint ρ y) ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (dint ρ x) (dint ρ y) (dint ρ x) ltac:(lia) ltac:(nia)). lia.
  - (* And *) intros E. eexists. split; [reflexivity|]. refine (fin_mk ρ B st e X _ _ _ r st' HM _ E).
    pose proof (land_le (dint ρ x) (dint ρ y) ltac:(lia) ltac:(lia)).
    pose proof (land_le (dint ρ y) (dint ρ x) ltac:(lia) ltac:(lia)). rewrite (Z.land_comm (dint ρ y)) in *. lia.
  - (* Or *) intros E. eexists. split; [reflexivity|]. refine (fin_mk ρ B st e X _ _ _ r st' HM _ E).
    apply lor_bound; lia.
  - (* Xor *) intros E. eexists. split; [reflexivity|]. refine (fin_mk ρ B st e X _ _ _ r st' HM _ E).
    apply lxor_bound; lia.
  - (* Shr *) destruct y as [c|t]; intros E; (eexists; split; [reflexivity|]); cbn [dint] in *.
    + refine (fin_mk ρ B st e X _ _ _ r st' HM _ E). pose proof (Hp c).
      split; apply Z.div_le_mono; lia.
    + refine (fin_mk ρ B st e X _ _ _ r st' HM _ E). pose proof (Hp (ρ t)).
      pose proof (Z.div_pos (dint ρ x) (2 ^ (ρ t mod bits)) ltac:(lia) ltac:(lia)).
      pose proof (Z.div_le_upper_bound (dint ρ x) (2 ^ (ρ t mod bits)) (dint ρ x) ltac:(lia) ltac:(nia)). lia.
  - (* Shl *) destruct y as [c|t]; intros E; (eexists; split; [reflexivity|]); cbn [dint] in *.
    + refine (fin_clamp ρ B st e X m _ _ _ r st' Hm0 HM _ E). pose proof (Hp c). nia.
    + refine (fin_mk ρ B st e X _ _ _ r st' HM _ E).
      match goal with |- _ <= ?a mod m <= _ => pose proof (Z.mod_pos_bound a m) end. lia.
Qed.

Lemma abin_sound ρ B st e X o k x y r st' :
  M ρ B st e X -> wf_int (length (st_bnd st)) x -> wf_int (length (st_bnd st)) y ->
  abin o k x y st = Some (r, st') ->
  (k = W \/ k = L) /\
  exists z, alu o k [WInt (dint ρ x); WInt (dint ρ y)] = Some (WInt z) /\ Ri ρ B e X st st' r z.
Proof using Type.
  intros HM Wx Wy. unfold abin. destruct (modulus_of k) as [m|] eqn:Em; [|discriminate].
  destruct (icls_of k m Em) as (h & bits & Hc). intros E. split; [exact (ic_k _ _ _ _ Hc)|]. revert E.
  assert (Hg : abin_rng o k m x y st = Some (r, st') ->
               exists z, alu o k [WInt (dint ρ x); WInt (dint ρ y)] = Some (WInt z) /\ Ri ρ B e X st st' r z)
    by (apply (abin_rng_sound ρ B st e X o k m h bits); assumption).
  destruct x as [a|s]; [|exact Hg]. destruct y as [b|t]; [|exact Hg]. cbn [dint].
  destruct (alu o k [WInt a; WInt b]) as [[z| |]|]; try discriminate. intros [= <- <-].
  exists z. split; [reflexivity|]. exists ρ. split; [exact HM|]. split; [apply step_refl|]. split; [exact I | reflexivity].
Qed.

Lemma R_step ρ ρ1 B e X st st1 st' x w :
  step ρ st ρ1 st1 -> R ρ1 B e X st1 st' x w -> R ρ B e X st st' x w.
Proof using Type. intros S1 (ρ' & H & S2 & W & D'). exists ρ'. split; [exact H|]. split; [eapply step_trans; eauto | auto]. Qed.

Lemma land_pow2_bit a n : 0 <= n -> Z.land a (2 ^ n) <> 0 -> Z.testbit a n = true.
Proof using Type.
  intros Hn Hne. destruct (Z.testbit a n) eqn:E; [reflexivity|]. exfalso. apply Hne.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by exact Hn.
  destruct (Z.eqb_spec n i) as [<-|_]; [rewrite E; reflexivity | apply andb_false_r].
Qed.

(** The flags that an "and" or an addition adds to its result are true. *)
Lemma aflags_sound ρ ρ' B st st' e X o k a b r z :
  M ρ B st e X -> M ρ' B st' e X -> step ρ st ρ' st' ->
  wf_int (length (st_bnd st)) a -> wf_int (length (st_bnd st)) b -> wf_int (length (st_bnd st')) r ->
  alu o k [WInt (dint ρ a); WInt (dint ρ b)] = Some (WInt z) -> dint ρ' r = z ->
  M ρ' B (aflags o k a b r st st') e X /\ length (st_bnd (aflags o k a b r st st')) = length (st_bnd st').
Proof using Type.
  intros HM HM' [Ha Hl] Wa Wb Wr Halu Hr.
  pose proof (M_sat _ _ _ _ _ HM) as (Hbnd & Hf & _). pose proof (M_wf_flags _ _ _ _ _ HM) as Wf.
  rewrite Forall_forall in Wf.
  destruct o; try (cbn [aflags]; split; [exact HM' | reflexivity]);
    destruct a as [za|s]; try (cbn [aflags]; split; [exact HM' | reflexivity]);
    destruct b as [c|tb]; try (cbn [aflags]; split; [exact HM' | reflexivity]);
    destruct r as [zr|t]; try (cbn [aflags]; split; [exact HM' | reflexivity]);
    cbn [aflags dint wf_int alu] in *.
  - (* Add *)
    destruct (modulus_of k) as [m|] eqn:Em; [|split; [exact HM' | reflexivity]].
    destruct (icls_of k m Em) as (h & bits & Hc). rewrite (ic_mod _ _ _ _ Hc) in Halu. injection Halu as <-.
    destruct (rng st (S s)) as [lo hi] eqn:E. cbn [rng] in E.
    assert (Rg : lo <= ρ s <= hi) by (apply Hbnd; rewrite <- E; apply nth_error_nth'; exact Wa).
    destruct ((0 <=? lo + c) && (hi + c <? m)) eqn:Eb; [|split; [exact HM' | reflexivity]].
    apply andb_true_iff in Eb as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
    split; [|reflexivity]. apply M_add_lin; [exact HM' | exact Wr | lia |].
    rewrite Hr, (Ha s Wa). apply Z.mod_small. lia.
  - (* And *)
    injection Halu as <-.
    set (bits := flag_picks st s (fun fl => match fl with FBit n => Some n | _ => None end)).
    set (st1 := if existsb (fun n => (0 <=? n) && (c =? 2 ^ n)) bits then add_flag st' t FNz else st').
    assert (H1 : M ρ' B st1 e X /\ length (st_bnd st1) = length (st_bnd st')).
    { subst st1. destruct (existsb _ bits) eqn:Ex; [|auto]. split; [|reflexivity].
      apply M_add_flag; [exact HM' | exact Wr | exact I |]. cbn [dflag]. rewrite Hr. intros Hne.
      apply existsb_exists in Ex as (n & Hin & Hn). apply andb_true_iff in Hn as [Hn0 Hn1].
      apply Z.leb_le in Hn0. apply Z.eqb_eq in Hn1. subst c.
      apply In_flag_picks in Hin as (fl & Hin & Ef). destruct fl; try discriminate. injection Ef as ->.
      exact (Hf _ _ Hin (land_pow2_bit _ _ Hn0 Hne)). }
    clearbody st1.
    set (picks := flag_picks st s (fun fl => match fl with
                                             | FEnd u key mask => if mask =? c then Some (u, key) else None
                                             | _ => None
                                             end)).
    assert (Hp : forall uk, In uk picks -> (fst uk < length (st_bnd st))%nat /\ (ρ (fst uk) = snd uk -> ρ' t = 0)).
    { intros [u key] Hin. apply In_flag_picks in Hin as (fl & Hin & Ef). destruct fl; try discriminate.
      destruct (Z.eqb_spec mask c) as [->|_]; [|discriminate]. injection Ef as <- <-. cbn [fst snd].
      destruct (Wf _ Hin) as [_ Wu]. cbn in Wu. split; [exact Wu|]. intros Ek. rewrite Hr.
      exact (Hf _ _ Hin Ek). }
    clearbody picks. revert st1 H1. induction picks as [|[u key] picks IH]; intros st1 [H1 L1]; cbn [fold_left].
    + auto.
    + apply IH; [intros uk Hin; apply Hp; right; exact Hin|]. split; [|exact L1].
      destruct (Hp (u, key) (or_introl eq_refl)) as [Wu Hk]. cbn [fst snd] in *.
      apply M_add_flag; [exact H1 | rewrite L1; exact Wr | cbn; rewrite L1; lia |].
      cbn [dflag]. rewrite (Ha u Wu). exact Hk.
Qed.

Lemma op_res_alu2 o k x y w m :
  (k = W \/ k = L) -> (forall c ck, o <> Cmp c ck) -> alu o k [WInt x; WInt y] = Some w ->
  op_res o k [WInt x; WInt y] m = Some (OpRes (RVal w) m).
Proof using Type.
  intros Hk Hc Ha. destruct o; try discriminate Ha; try (exfalso; eapply Hc; reflexivity);
    destruct Hk as [-> | ->]; unfold op_res, op_res_int; cbn [fmt_of additive_res]; rewrite Ha; reflexivity.
Qed.

Lemma abinop_sound ρ B st e X o k a b ws v st' :
  (forall c ck, o <> Cmp c ck) -> M ρ B st e X ->
  Forall (wf_val (length (st_bnd st))) [VI a; VI b] -> Forall2 (dval ρ B) [VI a; VI b] ws ->
  (let? (r, st1) := abin o k a b st in Some (VI r, aflags o k a b r st st1)) = Some (v, st') ->
  exists w, (forall m, op_res o k ws m = Some (OpRes (RVal w) m)) /\ R ρ B e X st st' v w.
Proof using Type.
  intros Hc HM Wv Hv. inversion Wv as [|? ? Wa Wv']; subst. inversion Wv' as [|? ? Wb _]; subst.
  inversion Hv as [|? wa ? ws' Ha Hv']; subst. inversion Hv' as [|? wb ? ws'' Hb Hv'']; subst. inversion Hv''; subst.
  cbn [dval wf_val] in *. subst wa wb.
  destruct (abin o k a b st) as [[r st1]|] eqn:E; [|discriminate]. intros [= <- <-].
  destruct (abin_sound ρ B st e X o k a b r st1 HM Wa Wb E) as (Hk & z & Halu & ρ' & H1 & S1 & W1 & D1).
  exists (WInt z). split; [intros m; apply op_res_alu2; assumption|].
  destruct (aflags_sound ρ ρ' B st st1 e X o k a b r z HM H1 S1 Wa Wb W1 Halu D1) as [H2 L2].
  exists ρ'. split; [exact H2|]. split; [destruct S1 as [A1 L1]; split; [exact A1 | lia]|].
  split; [cbn [wf_val]; rewrite L2; exact W1 | cbn [dval]; congruence].
Qed.

Lemma cond_bit_int c ck x y :
  int_cond c = true -> (ck = W \/ ck = L) -> exists r, cond_bit c ck x y = Some r.
Proof using Type. intros Hc [-> | ->]; destruct c; try discriminate; cbn; eauto. Qed.

Lemma aop_int_sound ρ B st e X o k xs ws v st' :
  M ρ B st e X -> Forall (wf_val (length (st_bnd st))) xs -> Forall2 (dval ρ B) xs ws ->
  aop_int o k xs st = Some (v, st') ->
  exists w, (forall m, op_res o k ws m = Some (OpRes (RVal w) m)) /\ R ρ B e X st st' v w.
Proof using Type.
  intros HM Wv Hv. pose proof (M_sat _ _ _ _ _ HM) as Hs.
  assert (Hgen : (forall c ck, o <> Cmp c ck) -> forall a b, xs = [VI a; VI b] ->
            (let? (r, st1) := abin o k a b st in Some (VI r, aflags o k a b r st st1)) = Some (v, st') ->
            exists w, (forall m, op_res o k ws m = Some (OpRes (RVal w) m)) /\ R ρ B e X st st' v w).
  { intros Hc a b ->. apply abinop_sound; assumption. }
  destruct o; cbn [aop_int];
    try (destruct xs as [|[xa| | | | | |] [|[xb| | | | | |] [|]]]; try discriminate;
         apply Hgen; [intros ? ?; discriminate | reflexivity]).
  - (* Neg *)
    destruct xs as [|[a| | | | | |] [|[b| | | | | |] [|]]]; try discriminate;
      [|apply Hgen; [intros ? ?; discriminate | reflexivity]].
    inversion Wv as [|? ? Wa _]; subst. inversion Hv as [|? wa ? ws' Ha Hv']; subst. inversion Hv'; subst.
    cbn [dval wf_val] in *. subst wa.
    destruct (modulus_of k) as [m|] eqn:Em; [|discriminate]. destruct (icls_of k m Em) as (h & bits & Hc).
    pose proof (ic_mod _ _ _ _ Hc) as Hmod. pose proof (ic_fmt _ _ _ _ Hc) as Hfmt.
    assert (Hop : forall m0, op_res Neg k [WInt (dint ρ a)] m0 = Some (OpRes (RVal (WInt ((- dint ρ a) mod m))) m0)).
    { intros m0. destruct (ic_k _ _ _ _ Hc) as [-> | ->]; injection Hmod as <-; reflexivity. }
    destruct a as [z|s].
    + intros [= <- <-]. eexists. split; [exact Hop|]. apply R_same; [exact HM | exact I | reflexivity].
    + destruct (mk st 0 (m - 1)) as [r st1] eqn:Ek. intros [= <- <-]. eexists. split; [exact Hop|].
      destruct (mk_sound ρ B st e X 0 (m - 1) ((- dint ρ (S s)) mod m) r st1 HM) as (ρ' & H1 & S1 & W1 & D1);
        [pose proof (Z.mod_pos_bound (- dint ρ (S s)) m); pose proof (ic_h _ _ _ _ Hc); pose proof (ic_m _ _ _ _ Hc); lia | exact Ek |].
      exists ρ'. split; [exact H1|]. split; [exact S1|]. split; [exact W1 | cbn [dval]; congruence].
  - (* Cmp *)
    destruct xs as [|[a| | | | | |] [|[b| | | | | |] [|]]]; try discriminate.
    inversion Wv as [|? ? Wa Wv']; subst. inversion Wv' as [|? ? Wb _]; subst.
    inversion Hv as [|? wa ? ws' Ha Hv']; subst. inversion Hv' as [|? wb ? ws'' Hb Hv'']; subst. inversion Hv''; subst.
    cbn [dval wf_val] in *. subst wa wb.
    destruct (int_cond c && match k0 with W | L => true | _ => false end) eqn:Ec; [|discriminate].
    apply andb_true_iff in Ec as [Hc Hk]. intros [= <- <-].
    assert (Hk' : k0 = W \/ k0 = L) by (destruct k0; try discriminate; auto).
    destruct (cond_bit_int c k0 (dint ρ a) (dint ρ b) Hc Hk') as [r Hr].
    exists (WInt r). split.
    + intros m. unfold op_res. assert (Hf : fmt_of k0 = None) by (destruct Hk' as [-> | ->]; reflexivity).
      destruct (fmt_of k); rewrite Hf; unfold op_res_int; cbn [alu]; rewrite Hr; reflexivity.
    + apply R_same; [exact HM | cbn; auto | exists r; auto].
  - (* Ext *)
    destruct xs as [|[a| | | | | |] [|[b| | | | | |] [|]]]; try discriminate;
      [|apply Hgen; [intros ? ?; discriminate | reflexivity]].
    inversion Wv as [|? ? Wa _]; subst. inversion Hv as [|? wa ? ws' Ha Hv']; subst. inversion Hv'; subst.
    cbn [dval wf_val] in *. subst wa.
    destruct (modulus_of k) as [m|] eqn:Em; [|discriminate]. destruct (icls_of k m Em) as (h & bits & Hc).
    pose proof (ic_mod _ _ _ _ Hc) as Hmod.
    assert (Hop : forall m0, op_res (Ext t) k [WInt (dint ρ a)] m0
                             = Some (OpRes (RVal (WInt (extension t (dint ρ a) mod m))) m0)).
    { intros m0. destruct (ic_k _ _ _ _ Hc) as [-> | ->]; injection Hmod as <-; reflexivity. }
    destruct (rng st a) as [lo hi] eqn:Er. pose proof (rng_sound _ _ _ _ _ Hs Wa Er) as Rg.
    destruct ((0 <=? lo) && (hi <? 2 ^ 32) && ext_keep t k hi) eqn:Ek.
    + intros [= <- <-]. eexists. split; [exact Hop|]. apply R_same; [exact HM | exact Wa |]. cbn [dval]. f_equal.
      apply andb_true_iff in Ek as [Ek H3]. apply andb_true_iff in Ek as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2. symmetry.
      destruct (ic_k _ _ _ _ Hc) as [-> | ->]; injection Hmod as <-; destruct t; cbn [ext_keep extension] in *;
        unfold sign_extension;
        change (2 ^ 31) with 2147483648 in *; change (2 ^ 32) with 4294967296 in *;
        change (2 ^ 64) with 18446744073709551616 in *;
        repeat match goal with
               | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
               end;
        rewrite ?(Z.mod_small (dint ρ a)) by lia;
        repeat match goal with
               | |- context [Z.leb ?u ?v] => destruct (Z.leb_spec u v)
               end; try (rewrite Z.mod_small by lia; lia); try lia.
      * (* sign extension of a 32-bit word at class W *)
        rewrite <- (Z.mod_add _ 1 4294967296) by lia. rewrite Z.mod_small by lia. lia.
    + destruct (mk st 0 (ext_top t k m)) as [r st1] eqn:Emk. intros [= <- <-]. eexists. split; [exact Hop|].
      destruct (mk_sound ρ B st e X 0 (ext_top t k m) (extension t (dint ρ a) mod m) r st1 HM) as (ρ' & H1 & S1 & W1 & D1);
        [|exact Emk|exists ρ'; split; [exact H1|]; split; [exact S1|]; split; [exact W1 | cbn [dval]; congruence]].
      pose proof (ic_h _ _ _ _ Hc). pose proof (ic_m _ _ _ _ Hc).
      pose proof (Z.mod_pos_bound (extension t (dint ρ a)) m ltac:(lia)).
      destruct (ic_k _ _ _ _ Hc) as [-> | ->]; injection Hmod as <-; destruct t; cbn [ext_top extension] in *;
        change (2 ^ 32) with 4294967296 in *; change (2 ^ 64) with 18446744073709551616 in *; try lia;
        match goal with
        | |- _ <= (?u mod ?d) mod _ <= _ => pose proof (Z.mod_pos_bound u d ltac:(lia)); rewrite Z.mod_small by lia; lia
        end.
Qed.

Lemma aop_sound ρ B st e X o k xs ws v st' :
  M ρ B st e X -> Forall (wf_val (length (st_bnd st))) xs -> Forall2 (dval ρ B) xs ws ->
  aop o k xs st = Some (v, st') ->
  exists w, (forall m, op_res o k ws m = Some (OpRes (RVal w) m)) /\ R ρ B e X st st' v w.
Proof using Type.
  intros HM Wv Hv.
  assert (Hgen : (let (xs', st1) := as_ints xs st in aop_int o k xs' st1) = Some (v, st') ->
            exists w, (forall m, op_res o k ws m = Some (OpRes (RVal w) m)) /\ R ρ B e X st st' v w).
  { destruct (as_ints xs st) as [xs' st1] eqn:E. intros Ho.
    destruct (as_ints_sound ρ B st e X xs ws xs' st1 HM Wv Hv E) as (ρ1 & H1 & S1 & W1 & D1).
    destruct (aop_int_sound ρ1 B st1 e X o k xs' ws v st' H1 W1 D1 Ho) as (w & Hop & HR).
    exists w. split; [exact Hop | eapply R_step; eauto]. }
  destruct o; cbn [aop]; try exact Hgen.
  - (* Copy *)
    destruct xs as [|x [|]]; try discriminate.
    inversion Wv as [|? ? Wx _]; subst. inversion Hv as [|? w ? ws' Hx Hv']; subst. inversion Hv'; subst.
    destruct k; try discriminate; intros [= <- <-]; exists w; (split; [reflexivity|]); apply R_same; assumption.
  - (* Ptoi *)
    destruct xs as [|x [|]]; try discriminate; [|destruct x; discriminate].
    inversion Wv as [|? ? Wx _]; subst. inversion Hv as [|? w ? ws' Hx Hv']; subst. inversion Hv'; subst.
    destruct x as [a|c ck a b| |ob a|a| |g]; try discriminate; intros [= <- <-]; cbn [dval] in Hx.
    + destruct Hx as (pl & _ & ->). eexists. split; [intros m; destruct k; reflexivity|].
      apply R_same; [exact HM | exact I | eexists; reflexivity].
    + subst w. eexists. split; [intros m; destruct k; reflexivity|]. apply R_same; [exact HM | exact Wx | reflexivity].
    + destruct Hx as (p & ->). eexists. split; [intros m; destruct k; reflexivity|].
      apply R_same; [exact HM | exact I | eexists; reflexivity].
    + destruct Hx as (p & -> & _). eexists. split; [intros m; destruct k; reflexivity|].
      apply R_same; [exact HM | exact I | eexists; reflexivity].
Qed.

End den.
