(** A function meets the rest of the program at four places: where it
    is entered, where it returns, where a loop comes back to a cut
    point, and where it calls another function. At each of them the
    checker of [AbsRun](AbsRun.v) compares an abstract state with a
    closed description that mentions no symbol, which is a
    specification or a cut invariant. This module shows that each
    comparison is sound. The lemmas here are pure, and
    [AbsSound](AbsSound.v) adds the ownership of memory.

    A function is checked once, but it runs many times, so a
    specification cannot name the particular numbers of one run. It
    gives each number a range instead. When the checker starts from a
    specification, it invents a fresh unknown for every range. The
    lemmas in this module show that this loses nothing: whatever real
    state the specification allows, the checker's starting state
    allows too. The same argument is used where a loop returns to its
    head, where a function is entered, and where it returns. The last
    section treats a call, where the caller lends objects to the
    callee and gets them back. *)

From Stdlib Require Import String ZArith List Bool Lia PeanoNat.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Ops Semantics Symbolic Pieces StepRules
  AbsRun AbsInfer AbsDen AbsMem AbsStep.
Import ListNotations.
Open Scope Z_scope.

Section call.
Variable guard : Prop.
Variable ge : genv.
Variable gobjs : list name.

Local Notation M := (M guard ge gobjs).
Local Notation R := (R guard ge gobjs).
Local Notation nglob := (nglob gobjs).

(** * Closed values *)

(** The closed form of a value describes every word that the value
    describes. *)
Lemma close_val_sound ρ B st v w :
  sat guard ρ st -> wf_val (length (st_bnd st)) v -> dval ge ρ B v w -> dcval ge B (close_val st v) w.
Proof using Type.
  intros Hs Wv Hv. destruct v as [a|c k a b| |o a|a| |g]; cbn [close_val dval wf_val] in *.
  - destruct (rng st a) as [lo hi] eqn:Er. exists (dint ρ a).
    split; [exact (rng_sound guard ρ st a lo hi Hs Wv Er) | exact Hv].
  - destruct Hv as (r & Hr & ->). exists r. split; [destruct (cond_bit_01 _ _ _ _ _ Hr); lia | reflexivity].
  - exact Hv.
  - destruct (rng st a) as [lo hi] eqn:Er. destruct Hv as (x & Hx & ->). exists x, (dint ρ a).
    split; [exact Hx|]. split; [exact (rng_sound guard ρ st a lo hi Hs Wv Er) | reflexivity].
  - destruct (rng st a) as [lo hi] eqn:Er. exists (dint ρ a).
    split; [exact (rng_sound guard ρ st a lo hi Hs Wv Er) | exact Hv].
  - exact Hv.
  - exact Hv.
Qed.

(** A value that passes [val_le] against a closed value describes only
    words that the closed value describes. *)
Lemma val_le_sound ρ B st v c w :
  sat guard ρ st -> wf_val (length (st_bnd st)) v -> dval ge ρ B v w -> val_le st v c = true ->
  dcval ge B c w.
Proof using Type.
  intros Hs Wv Hv Hle. pose proof (close_val_sound ρ B st v w Hs Wv Hv) as Hc. unfold val_le in Hle.
  destruct (close_val st v) as [lo hi| |o lo hi|lo hi| |g], c as [lo' hi'| |o' lo' hi'|lo' hi'| |g'];
    try discriminate; cbn [dcval] in *.
  - destruct Hc as (n & Hn & ->). apply andb_prop in Hle as [H1 H2]. exists n. split; [lia | reflexivity].
  - destruct Hc as (n & _ & ->). eauto.
  - exact Hc.
  - destruct Hc as (x & off & Hx & Hoff & ->). apply andb_prop in Hle as [H12 H3]. apply andb_prop in H12 as [H1 H2].
    apply Nat.eqb_eq in H1. subst o'. exists x, off. split; [exact Hx|]. split; [lia | reflexivity].
  - destruct Hc as (x & off & _ & _ & ->). eauto.
  - destruct Hc as (n & Hn & ->). apply andb_prop in Hle as [H1 H2]. exists n. split; [lia | reflexivity].
  - destruct Hc as (n & _ & ->). eauto.
  - exact Hc.
  - destruct Hc as (p & -> & _). eauto.
  - apply term_eqb_eq in Hle. subst g'. exact Hc.
Qed.

(** Opening a closed value gives its range a new symbol, and the
    opened value describes any word that the closed value describes. *)
Lemma open_val_sound ρ B st e X c w v st' :
  M ρ B st e X -> dcval ge B c w -> open_val c st = (v, st') -> R ρ B e X st st' v w.
Proof using Type.
  intros HM Hc. destruct c as [lo hi| |o lo hi|lo hi| |g]; cbn [open_val dcval] in *.
  - destruct Hc as (n & Hn & ->). destruct (mk st lo hi) as [a st1] eqn:Em. intros [= <- <-].
    destruct (mk_sound guard ge gobjs ρ B st e X lo hi n a st1 HM Hn Em) as (ρ' & HM' & S1 & Wa & Da).
    exists ρ'. split; [exact HM'|]. split; [exact S1|]. split; [exact Wa|]. cbn [dval]. congruence.
  - intros [= <- <-]. exists ρ. split; [exact HM|]. split; [apply step_refl|]. split; [exact I | exact Hc].
  - destruct Hc as (x & off & Hx & Hoff & ->). destruct (mk st lo hi) as [a st1] eqn:Em. intros [= <- <-].
    destruct (mk_sound guard ge gobjs ρ B st e X lo hi off a st1 HM Hoff Em) as (ρ' & HM' & S1 & Wa & Da).
    exists ρ'. split; [exact HM'|]. split; [exact S1|]. split; [exact Wa|]. cbn [dval]. exists x. rewrite Da. auto.
  - destruct Hc as (n & Hn & ->). destruct (mk st lo hi) as [a st1] eqn:Em. intros [= <- <-].
    destruct (mk_sound guard ge gobjs ρ B st e X lo hi n a st1 HM Hn Em) as (ρ' & HM' & S1 & Wa & Da).
    exists ρ'. split; [exact HM'|]. split; [exact S1|]. split; [exact Wa|]. cbn [dval]. congruence.
  - intros [= <- <-]. exists ρ. split; [exact HM|]. split; [apply step_refl|]. split; [exact I | exact Hc].
  - intros [= <- <-]. exists ρ. split; [exact HM|]. split; [apply step_refl|]. split; [exact I | exact Hc].
Qed.

(** * Closed objects *)

Lemma all2_Forall2 {X Y : Type} (f : X -> Y -> bool) xs ys :
  all2 f xs ys = true -> Forall2 (fun x y => f x y = true) xs ys.
Proof using Type.
  revert ys. induction xs as [|x xs IH]; intros [|y ys]; cbn [all2]; try discriminate; [constructor|].
  intros H. apply andb_prop in H as [H1 H2]. constructor; [exact H1 | exact (IH ys H2)].
Qed.

Lemma all2_length {X Y : Type} (f : X -> Y -> bool) xs ys : all2 f xs ys = true -> length xs = length ys.
Proof using Type. intros H. exact (Forall2_length (all2_Forall2 f xs ys H)). Qed.

Lemma Forall2_impl_in {X Y : Type} (P Q : X -> Y -> Prop) l l' :
  Forall2 P l l' -> (forall a b, In a l -> P a b -> Q a b) -> Forall2 Q l l'.
Proof using Type.
  induction 1 as [|a b l l' Hab _ IH]; intros HPQ; constructor.
  - apply HPQ; [left; reflexivity | exact Hab].
  - apply IH. intros a' b' Hin. apply HPQ. right. exact Hin.
Qed.

(** An alignment that divides another alignment is kept by every
    address that the other one fits. *)
Lemma mod_chain0 base oa al : base mod oa = 0 -> oa mod al = 0 -> base mod al = 0.
Proof using Type.
  intros H1 H2. destruct (Z.eq_dec al 0) as [->|Hal].
  - rewrite Z.mod_0_r in H2. subst oa. exact H1.
  - destruct (Z.eq_dec oa 0) as [->|Hoa].
    + rewrite Z.mod_0_r in H1. subst base. apply Z.mod_0_l. exact Hal.
    + apply Z.mod_divide in H1; [|exact Hoa]. apply Z.mod_divide in H2; [|exact Hal].
      apply Z.mod_divide; [exact Hal|]. eapply Z.divide_trans; eauto.
Qed.

Lemma small_testbit x k : 0 <= x < 2 ^ k -> Z.testbit x k = false.
Proof using Type.
  intros Hx. destruct (Z.ltb_spec k 0) as [Hk|Hk]; [apply Z.testbit_neg_r; exact Hk|].
  rewrite <- (Z.mod_small x (2 ^ k) Hx). apply Z.mod_pow2_bits_high. lia.
Qed.

(** A byte that passes [byte_le] against a closed byte has only
    values that the closed byte allows. The opened byte mentions no
    symbol, so it may be read under any valuation. *)
Lemma byte_le_sound ρ ρ0 st b t x :
  sat guard ρ st -> wf_byte (length (st_bnd st)) b -> dbyte guard ρ b x -> byte_le st b t = true ->
  dbyte guard ρ0 (open_byte t) x.
Proof using Type.
  intros Hs Wb Hb Hle. pose proof (proj1 Hb) as Hx. split; [exact Hx|].
  destruct t as [z|s i|lo' hi'| |k|s key mask]; cbn [byte_le open_byte] in *; try discriminate.
  - destruct (byte_rng st b) as [lo hi] eqn:Er.
    pose proof (byte_rng_sound guard ρ st b x lo hi Hs Wb Hb Er) as Rg.
    destruct b; try discriminate; apply andb_prop in Hle as [H1 H2]; lia.
  - destruct (byte_rng st b) as [lo hi] eqn:Er.
    pose proof (byte_rng_sound guard ρ st b x lo hi Hs Wb Hb Er) as Rg.
    apply andb_prop in Hle as [H1 H2]. lia.
  - exact I.
  - assert (Hg : st_guard st = true -> guard) by exact (proj2 (proj2 (proj2 Hs))).
    assert (Hr : st_guard st || (let (lo, hi) := byte_rng st b in (0 <=? lo) && (hi <? 2 ^ k)) = true ->
                 Z.testbit x k = true -> guard).
    { intros H Hbit. apply orb_prop in H as [H|H]; [exact (Hg H)|].
      destruct (byte_rng st b) as [lo hi] eqn:Er.
      pose proof (byte_rng_sound guard ρ st b x lo hi Hs Wb Hb Er) as Rg. apply andb_prop in H as [H1 H2].
      rewrite small_testbit in Hbit; [discriminate | lia]. }
    destruct b as [z|s i|lo hi| |k'|s key mask]; try exact (Hr Hle).
    apply Z.eqb_eq in Hle. subst k'. exact (proj2 Hb).
Qed.

Lemma bytes_le_sound ρ ρ0 st bs ts xs :
  sat guard ρ st -> Forall (wf_byte (length (st_bnd st))) bs -> Forall2 (dbyte guard ρ) bs xs ->
  all2 (byte_le st) bs ts = true -> Forall2 (dbyte guard ρ0) (map open_byte ts) xs.
Proof using Type.
  intros Hs Wb Hb. revert ts Wb. induction Hb as [|b x bs xs Hbx Hb IH]; intros [|t ts] Wb; cbn [all2 map];
    try discriminate; [constructor|].
  intros H. apply andb_prop in H as [H1 H2]. inversion Wb; subst.
  constructor; [eapply byte_le_sound; eauto | apply IH; assumption].
Qed.

(** A pointer stored in memory carries a capability, and the checker
    tracks which object that capability belongs to. This lemma covers
    the comparison of those tracked capabilities against a
    specification. If the comparison succeeds, the real capability is
    one that the specification allows. *)
Lemma auxs_le_sound B B' xs ts cs :
  Forall2 (daux B) xs cs -> all2 aux_le xs ts = true ->
  (forall o, In (XObj o) ts -> nth_error B' o = nth_error B o) -> Forall2 (daux B') ts cs.
Proof using Type.
  intros Hd. revert ts. induction Hd as [|x c xs cs Hxc Hd IH]; intros [|t ts]; cbn [all2];
    try discriminate; [constructor|].
  intros H HB. apply andb_prop in H as [H1 H2]. constructor.
  - destruct t as [|o|], x as [|o'|]; cbn [aux_le daux] in *; try discriminate; try exact I; try exact Hxc.
    apply Nat.eqb_eq in H1. subst o'. rewrite (HB o (or_introl eq_refl)). exact Hxc.
  - apply IH; [exact H2|]. intros o Hin. apply HB. right. exact Hin.
Qed.

(** An object that passes [obj_le] against a closed object has contents
    that the opened closed object describes. *)
Lemma obj_le_sound ρ ρ0 B B' st pl ob t xs cs :
  sat guard ρ st -> Forall (wf_byte (length (st_bnd st))) (o_bytes ob) ->
  obj_ok guard ρ B pl ob xs cs -> obj_le st ob t = true ->
  (forall o, In (XObj o) (o_aux t) -> nth_error B' o = nth_error B o) ->
  obj_ok guard ρ0 B' pl (open_obj t) xs cs.
Proof using Type.
  intros Hs Wb (Hb & Ha & Hl & Hro & Hal & Hsz) Hle HB. unfold obj_le in Hle.
  apply andb_prop in Hle as [Hle Hax]. apply andb_prop in Hle as [Hle Hby].
  apply andb_prop in Hle as [Hle Hmod]. apply andb_prop in Hle as [Hr _].
  pose proof (all2_length _ _ _ Hby) as Lb. pose proof (all2_length _ _ _ Hax) as La.
  split; [exact (bytes_le_sound ρ ρ0 st _ _ _ Hs Wb Hb Hby)|].
  split; [exact (auxs_le_sound B B' _ _ _ Ha Hax HB)|]. cbn [open_obj o_aux o_bytes o_ro o_align].
  split; [rewrite length_map; congruence|]. split; [apply Bool.eqb_prop in Hr; congruence|].
  split; [apply Z.eqb_eq in Hmod; exact (mod_chain0 _ _ _ Hal Hmod)|].
  unfold o_size in *. cbn [open_obj o_bytes]. rewrite length_map, <- Lb. exact Hsz.
Qed.

(** An opened object mentions no symbol, so it describes the same
    contents under every valuation, and under every list of places
    that agrees on the objects its shadow slots name. *)
Lemma open_obj_ok ρ ρ' B B' pl t xs cs :
  obj_ok guard ρ B pl (open_obj t) xs cs ->
  (forall o, In (XObj o) (o_aux t) -> nth_error B' o = nth_error B o) ->
  obj_ok guard ρ' B' pl (open_obj t) xs cs.
Proof using Type.
  intros (Hb & Ha & Rest) HB. split; [|split; [|exact Rest]].
  - cbn [open_obj o_bytes] in *. remember (map open_byte (o_bytes t)) as bs eqn:Eb.
    eapply Forall2_impl_in; [exact Hb|]. intros b x Hin [Hx Hd]. split; [exact Hx|]. subst bs.
    apply in_map_iff in Hin as (b0 & <- & _). destruct b0; exact Hd.
  - cbn [open_obj o_aux] in *. eapply Forall2_impl_in; [exact Ha|]. intros a c Hin Hd.
    destruct a as [|o|]; cbn [daux] in *; try exact Hd. rewrite (HB o Hin). exact Hd.
Qed.

Lemma open_obj_wf n t : wf_obj n (Some (open_obj t)).
Proof using Type.
  cbn [wf_obj open_obj o_bytes]. apply Forall_forall. intros b Hin.
  apply in_map_iff in Hin as (b0 & <- & _). destruct b0; exact I.
Qed.

(** * Opened states

    A closed state is opened on an empty table of symbols. Its objects
    are opened byte by byte, and its values are opened one name at a
    time. The lemma [M_base] makes the state with the opened objects
    and no names true, and [open_env_sound] adds the names. *)

Lemma M_base ρ B X e os g :
  Forall place_ok B -> globals_ok ge gobjs B -> (g = true -> guard) ->
  length os = length B -> length X = length B ->
  (forall i t, nth_error os i = Some (Some t) ->
     exists pl xs cs, nth_error B i = Some pl /\ nth_error X i = Some (Some (xs, cs)) /\
                      obj_ok guard ρ B pl (open_obj t) xs cs) ->
  M ρ B (mkSt [] [] [] [] (map (option_map open_obj) os) g) e X.
Proof using Type.
  intros HB HG Hg L1 L2 Ho. split; [exact HB|]. split; [exact HG|]. split; [|split; [|split]].
  - split; [intros s lo hi H; destruct s; discriminate|]. split; [intros s fl []|].
    split; [intros t s c [] | exact Hg].
  - split; [constructor|]. split; [constructor|]. split; [constructor|]. cbn [st_objs st_bnd length].
    apply Forall_forall. intros o Hin. apply in_map_iff in Hin as ([t|] & <- & _); [apply open_obj_wf | exact I].
  - intros n v H. discriminate.
  - cbn [st_objs]. split; [rewrite length_map; exact L1|]. split; [exact L2|]. intros i ob Hi.
    rewrite nth_error_map in Hi. destruct (nth_error os i) as [[t|]|] eqn:E; try discriminate.
    injection Hi as <-. exact (Ho i t E).
Qed.

(** A name can be given a value without changing the real
    environment, when the environment already holds a word that the
    value describes. *)
Lemma M_bind_same ρ B st e X d v w :
  M ρ B st e X -> wf_val (length (st_bnd st)) v -> dval ge ρ B v w -> lookup d e = Some w ->
  M ρ B (bind st d v) e X.
Proof using Type.
  intros (HB & HG & Hs & (We & Wf & Wl & Wo) & He & Ho) Wv Hv Hd.
  split; [exact HB|]. split; [exact HG|]. split; [exact Hs|]. split; [|split; [|exact Ho]].
  - split; [|split; [exact Wf | split; [exact Wl | exact Wo]]]. constructor; [exact Wv | exact We].
  - intros n v0. cbn [bind set_env st_env lookup]. destruct (name_eqb n d) eqn:En; [|apply He].
    intros [= <-]. apply term_eqb_eq in En. subst n. exists w. auto.
Qed.

Lemma open_env_sound B e X : forall te ρ st,
  M ρ B st e X ->
  Forall (fun nc => exists w, lookup (fst nc) e = Some w /\ dcval ge B (snd nc) w) te ->
  exists ρ', M ρ' B (open_env te st) e X.
Proof using Type.
  induction te as [|[n c] te IH]; intros ρ st HM Hte; cbn [open_env]; [exists ρ; exact HM|].
  inversion Hte as [|? ? (w & Hw & Hc) Hte']; subst. cbn [fst snd] in *.
  destruct (IH ρ st HM Hte') as (ρ1 & HM1).
  destruct (open_val c (open_env te st)) as [v st2] eqn:Eo.
  destruct (open_val_sound ρ1 B _ e X c w v st2 HM1 Hc Eo) as (ρ2 & HM2 & _ & Wv & Dv).
  exists ρ2. exact (M_bind_same ρ2 B st2 e X n v w HM2 Wv Dv Hw).
Qed.

(** A closed value keeps its meaning under another list of places
    that has the same place for the object it points into. *)
Lemma dcval_places B B' c w :
  dcval ge B c w -> (forall o lo hi, c = CP o lo hi -> nth_error B' o = nth_error B o) -> dcval ge B' c w.
Proof using Type.
  intros Hc HB. destruct c; cbn [dcval] in *; try exact Hc.
  destruct Hc as (x & off & Hx & Hoff & ->). exists x, off. rewrite (HB _ _ _ eq_refl). auto.
Qed.

Lemma nth_error_firstn_lt {X : Type} (l : list X) n i : (i < n)%nat -> nth_error (firstn n l) i = nth_error l i.
Proof using Type. revert n i. induction l as [|x l IH]; intros [|n] [|i] H; cbn; try reflexivity; try lia. apply IH. lia. Qed.

Lemma objs_le_nth st : forall ts os i t,
  objs_le st os ts = true -> nth_error ts i = Some (Some t) ->
  exists ob, nth_error os i = Some (Some ob) /\ obj_le st ob t = true.
Proof using Type.
  induction ts as [|[t0|] ts IH]; intros os i t H Hi.
  - destruct i; discriminate.
  - destruct os as [|[ob|] os]; cbn [objs_le] in H; try discriminate. apply andb_prop in H as [H1 H2].
    destruct i; cbn [nth_error] in *; [injection Hi as <-; eauto | exact (IH os i t H2 Hi)].
  - destruct os as [|o os]; cbn [objs_le] in H; try discriminate.
    destruct i; cbn [nth_error] in *; [discriminate | exact (IH os i t H Hi)].
Qed.

Lemma objs_le_length st : forall ts os, objs_le st os ts = true -> (length ts <= length os)%nat.
Proof using Type.
  induction ts as [|[t0|] ts IH]; intros os H; cbn [length]; [lia| |].
  - destruct os as [|[ob|] os]; cbn [objs_le] in H; try discriminate. apply andb_prop in H as [_ H2].
    specialize (IH os H2). cbn [length]. lia.
  - destruct os as [|o os]; cbn [objs_le] in H; try discriminate. specialize (IH os H). cbn [length]. lia.
Qed.

(** * Cut points

    A loop may run any number of times, so the checker examines its
    body once, starting from an invariant that holds each time the
    loop returns to its head. This is sound only if every state that
    returns to the head satisfies the invariant. The lemma below
    shows that the checker's comparison guarantees this. An invariant
    may leave out objects that the loop no longer needs, and those
    objects are dropped. *)
Lemma entails_sound ρ B st e X t n0 :
  M ρ B st e X -> entails st t = true -> cstate_ok n0 t = true -> (nglob <= n0)%nat ->
  let n := length (cs_objs t) in
  (n0 <= n <= length B)%nat /\ exists ρ', M ρ' (firstn n B) (open_state t) e (firstn n X).
Proof using Type.
  intros HM He Hok Hn0 n. unfold entails in He. apply andb_prop in He as [He Hg].
  apply andb_prop in He as [Henv Hobj]. unfold cstate_ok in Hok. apply andb_prop in Hok as [Hok Haux].
  apply andb_prop in Hok as [Hlen Hin]. apply Nat.leb_le in Hlen. fold n in Hlen, Hin, Haux.
  pose proof HM as (HB & HG & Hs & Hwf & Hden & (L1 & L2 & Ho)).
  pose proof (objs_le_length st _ _ Hobj) as Ln. rewrite L1 in Ln. fold n in Ln. split; [lia|].
  assert (Hpre : forall i, (i < n)%nat -> nth_error (firstn n B) i = nth_error B i)
    by (intros; apply nth_error_firstn_lt; assumption).
  unfold open_state. apply open_env_sound with (ρ := ρ).
  - apply M_base.
    + apply Forall_firstn'. exact HB.
    + intros i g Hi. destruct (HG i g Hi) as (pl & H1 & H2). exists pl. split; [|exact H2].
      assert (i < length gobjs)%nat by (apply nth_error_Some; congruence). unfold AbsRun.nglob in Hn0.
      rewrite Hpre; [exact H1 | lia].
    + intros Hc. rewrite Hc in Hg. exact (proj2 (proj2 (proj2 Hs)) Hg).
    + rewrite firstn_length_le; [reflexivity | lia].
    + rewrite !firstn_length_le; [reflexivity | lia | lia].
    + intros i tob Hi. destruct (objs_le_nth st _ _ i tob Hobj Hi) as (ob & Hob & Hle).
      destruct (Ho i ob Hob) as (pl & xs & cs & Hp & Hx & Hok).
      assert (Hi' : (i < n)%nat) by (apply nth_error_Some; congruence).
      exists pl, xs, cs. rewrite Hpre, nth_error_firstn_lt by exact Hi'.
      split; [exact Hp|]. split; [exact Hx|].
      apply (obj_le_sound ρ ρ B (firstn n B) st pl ob tob xs cs Hs); [|exact Hok | exact Hle|].
      * apply (M_wf_obj guard ge gobjs ρ B st e X i ob HM). unfold get_obj. rewrite Hob. reflexivity.
      * intros o Ho'. apply Hpre. rewrite forallb_forall in Haux.
        specialize (Haux _ (nth_error_In _ _ Hi)). cbn beta iota in Haux. rewrite forallb_forall in Haux.
        specialize (Haux _ Ho'). apply Nat.ltb_lt in Haux. exact Haux.
  - apply Forall_forall. intros [nm c] Hc. cbn [fst snd]. unfold env_le in Henv.
    rewrite forallb_forall in Henv. pose proof (Henv _ Hc) as Hle. cbn [fst snd] in Hle.
    destruct (lookup nm (st_env st)) as [v|] eqn:El; [|discriminate].
    destruct (M_env guard ge gobjs ρ B st e X nm v HM El) as (Wv & w & Hw & Dv). exists w. split; [exact Hw|].
    apply dcval_places with (B := B); [exact (val_le_sound ρ B st v c w Hs Wv Dv Hle)|].
    intros o lo hi ->. apply Hpre. rewrite forallb_forall in Hin. specialize (Hin _ Hc). cbn [snd cval_in] in Hin.
    apply Nat.ltb_lt in Hin. exact Hin.
Qed.

(** * Entry

    A function is entered with one word for each parameter. The
    checker starts from the state [entry_state], which opens the
    specification's arguments one parameter at a time, and the machine
    binds the words in the same order. *)

Lemma open_args_sound B X : forall (params : list (class * name)) cs ws ρ st e,
  M ρ B st e X -> Forall2 (dcval ge B) cs ws -> length params = length cs ->
  exists ρ', M ρ' B
    (fold_left (fun st pc => let (v, st') := open_val (snd pc) st in bind st' (snd (fst pc)) v)
               (combine params cs) st)
    (fold_left (fun e px => put (snd (fst px)) (snd px) e) (combine params ws) e) X.
Proof using Type.
  induction params as [|[k d] params IH]; intros cs ws ρ st e HM Hc Hl; [exists ρ; exact HM|].
  destruct Hc as [|c w cs ws Hcw Hc]; [discriminate|]. cbn [combine fold_left fst snd].
  destruct (open_val c st) as [v st1] eqn:Eo.
  destruct (R_bind guard ge gobjs ρ B e X st st1 v w d (open_val_sound ρ B st e X c w v st1 HM Hcw Eo))
    as (ρ1 & HM1 & _).
  apply (IH cs ws ρ1 _ _ HM1 Hc). cbn [length] in Hl. lia.
Qed.

(** A usable specification names one object for every global and one
    for every argument, its postcondition has the shape of its
    precondition, and its capabilities and its result stay among the
    globals. *)
Lemma spec_ok_inv sp : spec_ok gobjs sp = true ->
  length (sp_pre sp) = (nglob + length (sp_args sp))%nat /\ length (sp_post sp) = length (sp_pre sp) /\
  (forall i t o, nth_error (sp_pre sp) i = Some (Some t) -> In (XObj o) (o_aux t) -> (o < nglob)%nat) /\
  (forall i t o, nth_error (sp_post sp) i = Some (Some t) -> In (XObj o) (o_aux t) -> (o < nglob)%nat) /\
  (forall o lo hi, sp_ret sp = Some (CP o lo hi) -> (o < nglob)%nat).
Proof using Type.
  unfold spec_ok. intros H. apply andb_prop in H as [H Hret]. apply andb_prop in H as [H Hpost].
  apply andb_prop in H as [H Hpre]. apply andb_prop in H as [Hlen Hshape].
  assert (Hg : forall os i t o, forallb (obj_global gobjs) os = true -> nth_error os i = Some (Some t) ->
                 In (XObj o) (o_aux t) -> (o < nglob)%nat).
  { intros os i t o Hall Hi Hin. rewrite forallb_forall in Hall. specialize (Hall _ (nth_error_In _ _ Hi)).
    cbn [obj_global] in Hall. rewrite forallb_forall in Hall. specialize (Hall _ Hin).
    apply Nat.ltb_lt in Hall. exact Hall. }
  split; [apply Nat.eqb_eq; exact Hlen|]. split; [symmetry; exact (all2_length _ _ _ Hshape)|].
  split; [intros i t o; exact (Hg _ i t o Hpre)|]. split; [intros i t o; exact (Hg _ i t o Hpost)|].
  intros o lo hi E. rewrite E in Hret. apply Nat.ltb_lt in Hret. exact Hret.
Qed.

Lemma entry_sound B X f sp ws :
  spec_ok gobjs sp = true -> length (sp_args sp) = length (fn_params f) ->
  length B = length (sp_pre sp) -> length X = length B -> Forall place_ok B -> globals_ok ge gobjs B ->
  Forall2 (dcval ge B) (sp_args sp) ws -> (sp_guard sp = true -> guard) ->
  (forall i t, nth_error (sp_pre sp) i = Some (Some t) ->
     exists pl xs cs, nth_error B i = Some pl /\ nth_error X i = Some (Some (xs, cs)) /\
                      obj_ok guard (fun _ => 0) B pl (open_obj t) xs cs) ->
  exists ρ, M ρ B (entry_state gobjs f sp)
    (fold_left (fun e px => put (snd (fst px)) (snd px) e) (combine (fn_params f) ws) []) X.
Proof using Type.
  intros Hok La LB LX HB HG Hargs Hg Hpre. unfold entry_state.
  destruct (spec_ok_inv sp Hok) as (Lpre & _).
  assert (Ep : pad (nglob + length (fn_params f)) (map (option_map open_obj) (sp_pre sp))
               = map (option_map open_obj) (sp_pre sp)).
  { unfold pad. rewrite length_map. replace (_ - _)%nat with 0%nat by lia. apply app_nil_r. }
  rewrite Ep. apply open_args_sound with (ρ := fun _ => 0).
  - apply M_base; auto.
  - exact Hargs.
  - symmetry. exact La.
Qed.

(** The machine enters a function that has no local objects and no
    variable arguments at its first block, with exactly the
    environment that [entry_sound] describes. *)
Lemma call_frame_entry f ws :
  local_objects f = [] -> variadic_func f = false -> length ws = length (fn_params f) ->
  fn_blocks f <> [] ->
  call_frame f ws = Some (mkFrame f (fold_left (fun e px => put (snd (fst px)) (snd px) e)
                                               (combine (fn_params f) ws) [])
                                  [] None (Enter (entry_label f) None)).
Proof using Type.
  intros Hl Hv Hlen Hb. unfold call_frame, entry_label.
  destruct (Nat.ltb_spec (length ws) (length (fn_params f))) as [H|_]; [lia|].
  destruct (fn_blocks f) as [|b bs]; [congruence|]. rewrite Hl, Hv, firstn_all2 by lia. reflexivity.
Qed.

(** * Return

    A function returns when the checker's state passes [ret_ok]. The
    returned word is then one that the specification's result
    describes, and every object of the postcondition has contents that
    the postcondition describes, at the place the caller gave it. *)
Lemma ret_ok_sound ρ B0 B1 st e X sp v :
  M ρ (B0 ++ B1) st e X -> spec_ok gobjs sp = true -> length B0 = length (sp_pre sp) ->
  ret_ok sp v st = true ->
  match v, sp_ret sp with
  | Some x, Some c => forall w, wf_val (length (st_bnd st)) x -> dval ge ρ (B0 ++ B1) x w -> dcval ge B0 c w
  | None, None => True
  | _, _ => False
  end /\
  (sp_guard' sp = true -> guard) /\
  forall i t, nth_error (sp_post sp) i = Some (Some t) ->
    exists pl xs cs, nth_error B0 i = Some pl /\ nth_error X i = Some (Some (xs, cs)) /\
                     obj_ok guard (fun _ => 0) B0 pl (open_obj t) xs cs.
Proof using Type.
  intros HM Hok LB Hr. destruct (spec_ok_inv sp Hok) as (Lpre & Lpost & _ & Gpost & Gret).
  unfold ret_ok in Hr. apply andb_prop in Hr as [Hr Hg]. apply andb_prop in Hr as [Hv Hobj].
  pose proof HM as (HB & HG & Hs & Hwf & Hden & (L1 & L2 & Ho)).
  assert (Hpre : forall i, (i < length B0)%nat -> nth_error B0 i = nth_error (B0 ++ B1) i)
    by (intros; symmetry; apply nth_error_app1; assumption).
  split; [|split].
  - destruct v as [x|], (sp_ret sp) as [c|] eqn:Er; try discriminate; [|exact I]. intros w Wx Dx.
    apply dcval_places with (B := B0 ++ B1); [exact (val_le_sound ρ _ st x c w Hs Wx Dx Hv)|].
    intros o lo hi ->. apply Hpre. specialize (Gret o lo hi eq_refl). lia.
  - intros Hg'. rewrite Hg' in Hg. exact (proj2 (proj2 (proj2 Hs)) Hg).
  - intros i t Hi. destruct (objs_le_nth st _ _ i t Hobj Hi) as (ob & Hob & Hle).
    destruct (Ho i ob Hob) as (pl & xs & cs & Hp & Hx & Hok').
    assert (Hi' : (i < length B0)%nat) by (rewrite LB, <- Lpost; apply nth_error_Some; congruence).
    exists pl, xs, cs. rewrite Hpre by exact Hi'. split; [exact Hp|]. split; [exact Hx|].
    apply (obj_le_sound ρ (fun _ => 0) (B0 ++ B1) B0 st pl ob t xs cs Hs); [|exact Hok' | exact Hle|].
    + apply (M_wf_obj guard ge gobjs ρ _ st e X i ob HM). unfold get_obj. rewrite Hob. reflexivity.
    + intros o Hin. apply Hpre. specialize (Gpost i t o Hi Hin). lia.
Qed.

(** * Calls

    A call is matched against one specification of the callee. The
    callee has its own list of places. Its globals are the caller's,
    and the object of each pointer argument is the caller's object
    that the argument points into. The definition [callee_places]
    builds that list, and [places_for] states the two facts about it
    that the proofs use. *)

Definition no_place : place := mkPlace 0 (mkRegion 0 0 Heap Live) false.

Definition callee_places (B : list place) (xs : list aval) : list place :=
  firstn nglob B ++ map (fun x => match x with VP o _ => nth o B no_place | _ => no_place end) xs.

Definition places_for (B : list place) (xs : list aval) (B' : list place) : Prop :=
  (forall i, (i < nglob)%nat -> nth_error B' i = nth_error B i) /\
  (forall j o a pl, nth_error xs j = Some (VP o a) -> nth_error B o = Some pl ->
     nth_error B' (nglob + j) = Some pl).

Lemma globals_length B : globals_ok ge gobjs B -> (nglob <= length B)%nat.
Proof using Type.
  intros HG. destruct (Nat.le_gt_cases nglob (length B)) as [H|H]; [exact H|]. unfold AbsRun.nglob in *.
  destruct (nth_error gobjs (length B)) as [g|] eqn:E; [|apply nth_error_None in E; lia].
  destruct (HG _ g E) as (pl & Hp & _). assert (nth_error B (length B) = None) by (apply nth_error_None; lia).
  congruence.
Qed.

Lemma callee_places_ok B xs :
  Forall place_ok B -> globals_ok ge gobjs B ->
  places_for B xs (callee_places B xs) /\ length (callee_places B xs) = (nglob + length xs)%nat /\
  Forall place_ok (callee_places B xs) /\ globals_ok ge gobjs (callee_places B xs).
Proof using Type.
  intros HB HG. pose proof (globals_length B HG) as Hn.
  assert (Lf : length (firstn nglob B) = nglob) by (apply firstn_length_le; exact Hn).
  assert (HP : places_for B xs (callee_places B xs)).
  { split.
    - intros i Hi. unfold callee_places. rewrite nth_error_app1 by lia. apply nth_error_firstn_lt. exact Hi.
    - intros j o a pl Hj Hp. unfold callee_places. rewrite nth_error_app2 by lia.
      replace (nglob + j - length (firstn nglob B))%nat with j by lia.
      rewrite nth_error_map, Hj. cbn [option_map]. f_equal. apply nth_error_nth. exact Hp. }
  split; [exact HP|]. split; [unfold callee_places; rewrite length_app, length_map; lia|]. split.
  - unfold callee_places. apply Forall_app. split; [apply Forall_firstn'; exact HB|].
    assert (Hno : place_ok no_place) by (unfold place_ok; cbn; lia).
    apply Forall_forall. intros pl Hin. apply in_map_iff in Hin as (x & <- & _).
    destruct x as [| | |o a| | |]; try exact Hno.
    destruct (nth_in_or_default o B no_place) as [Hin|E]; [|rewrite E; exact Hno].
    rewrite Forall_forall in HB. exact (HB _ Hin).
  - intros i g Hi. destruct (HG i g Hi) as (pl & H1 & H2). exists pl. split; [|exact H2].
    rewrite (proj1 HP); [exact H1|]. unfold AbsRun.nglob. apply nth_error_Some. congruence.
Qed.

(** An argument that passes [arg_le] is a word that the
    specification's argument describes under the callee's places. *)
Lemma arg_le_sound ρ B B' st xs j v c w :
  sat guard ρ st -> places_for B xs B' -> nth_error xs j = Some v ->
  wf_val (length (st_bnd st)) v -> dval ge ρ B v w -> arg_le gobjs st j v c = true -> dcval ge B' c w.
Proof using Type.
  intros Hs [H1 H2] Hj Wv Dv Hle.
  destruct c as [lo hi| |o lo hi|lo hi| |g]; cbn [arg_le] in Hle;
    try (apply dcval_places with (B := B); [exact (val_le_sound ρ B st v _ w Hs Wv Dv Hle) | intros ? ? ? [=]]).
  destruct v as [| | |o' a| | |]; try discriminate. destruct (rng st a) as [alo ahi] eqn:Er.
  apply andb_prop in Hle as [Hle Ho]. apply andb_prop in Hle as [Hlo Hhi].
  pose proof (rng_sound guard ρ st a alo ahi Hs Wv Er) as Rg. destruct Dv as (x & Hx & ->).
  exists x, (dint ρ a). split; [|split; [lia | reflexivity]].
  destruct (Nat.ltb_spec o nglob) as [Hlt|Hge]; apply Nat.eqb_eq in Ho; subst o.
  - rewrite H1; assumption.
  - exact (H2 j o' a x Hj Hx).
Qed.

Lemma args_le_sound ρ B B' st xs : sat guard ρ st -> places_for B xs B' ->
  forall vs cs ws j, (forall k v, nth_error vs k = Some v -> nth_error xs (j + k) = Some v) ->
  Forall (wf_val (length (st_bnd st))) vs -> Forall2 (dval ge ρ B) vs ws ->
  args_le gobjs st j vs cs = true -> Forall2 (dcval ge B') cs ws.
Proof using Type.
  intros Hs HP. induction vs as [|v vs IH]; intros cs ws j Hx Wv Dv Hle.
  - destruct cs; [|discriminate]. inversion Dv. constructor.
  - destruct cs as [|c cs]; [discriminate|]. cbn [args_le] in Hle. apply andb_prop in Hle as [Hc Hcs].
    inversion Dv as [|? w ? ws' Dvw Dv']; subst. inversion Wv; subst. constructor.
    + apply (arg_le_sound ρ B B' st xs j v c w Hs HP); auto.
      specialize (Hx 0%nat v eq_refl). rewrite Nat.add_0_r in Hx. exact Hx.
    + apply (IH cs ws' (Datatypes.S j)); auto. intros k v' Hk.
      replace (Datatypes.S j + k)%nat with (j + Datatypes.S k)%nat by lia. apply Hx. exact Hk.
Qed.

(** Object [i] of a specification is at the caller's place for the
    object that [arg_obj] names. *)
Lemma arg_obj_place B B' st xs i o pl :
  places_for B xs B' -> arg_obj gobjs st xs i = Some o -> nth_error B o = Some pl -> nth_error B' i = Some pl.
Proof using Type.
  intros [H1 H2] Ha Hp. unfold arg_obj in Ha. destruct (Nat.ltb_spec i nglob) as [Hi|Hi].
  - injection Ha as <-. rewrite H1; assumption.
  - destruct (nth_error xs (i - nglob)) as [[| | |o' a| | |]|] eqn:Ex; try discriminate. injection Ha as ->.
    pose proof (H2 _ _ _ _ Ex Hp) as H. replace (nglob + (i - nglob))%nat with i in H by lia. exact H.
Qed.

(** A state stays true when it forgets an object. *)
Lemma M_drop_obj ρ B st e X o : M ρ B st e X -> M ρ B (put_obj st o None) e (list_set o None X).
Proof using Type.
  intros (HB & HG & Hs & (We & Wf & Wl & Wo) & He & (L1 & L2 & Ho)).
  split; [exact HB|]. split; [exact HG|]. split; [exact Hs|]. split; [|split; [exact He|]].
  - split; [exact We|]. split; [exact Wf|]. split; [exact Wl|].
    cbn [put_obj set_objs st_objs st_bnd]. apply Forall_nth_error. intros i x. rewrite nth_error_list_set.
    destruct (Nat.eqb_spec i o) as [->|_].
    + destruct (nth_error (st_objs st) o); [intros [= <-]; exact I | discriminate].
    + intros E. rewrite Forall_nth_error in Wo. exact (Wo i x E).
  - cbn [put_obj set_objs st_objs]. split; [rewrite length_list_set; exact L1|].
    split; [rewrite length_list_set; exact L2|]. intros i ob0 E. rewrite nth_error_list_set in E.
    destruct (Nat.eqb_spec i o) as [->|Hne]; [destruct (nth_error (st_objs st) o); discriminate|].
    destruct (Ho i ob0 E) as (pl & xs & cs & H1 & H2 & H3). exists pl, xs, cs.
    rewrite nth_error_list_set, (proj2 (Nat.eqb_neq i o) Hne). auto.
Qed.

(** At a call the caller gives up each object that the callee's
    precondition asks for, and the checker compares the caller's
    object with the precondition's object. When the comparison
    succeeds, the real contents are ones that the precondition
    describes under the callee's places. The caller's state stays
    true after it forgets the object. *)
Lemma take_one_sound ρ B B' st e X xs i t o ob :
  places_for B xs B' -> M ρ B st e X -> arg_obj gobjs st xs i = Some o -> get_obj st o = Some ob ->
  obj_le st ob t = true -> forallb (aux_global gobjs) (o_aux t) = true ->
  exists pl ys cs, nth_error B o = Some pl /\ nth_error X o = Some (Some (ys, cs)) /\
    nth_error B' i = Some pl /\ obj_ok guard (fun _ => 0) B' pl (open_obj t) ys cs /\
    M ρ B (put_obj st o None) e (list_set o None X).
Proof using Type.
  intros HP HM Ha Hg Hle Hglob.
  destruct (M_obj guard ge gobjs ρ B st e X o ob HM Hg) as (pl & ys & cs & Hp & Hx & Hok & _).
  exists pl, ys, cs. split; [exact Hp|]. split; [exact Hx|].
  split; [exact (arg_obj_place B B' st xs i o pl HP Ha Hp)|]. split; [|apply M_drop_obj; exact HM].
  apply (obj_le_sound ρ (fun _ => 0) B B' st pl ob t ys cs (M_sat guard ge gobjs ρ B st e X HM));
    [exact (M_wf_obj guard ge gobjs ρ B st e X o ob HM Hg) | exact Hok | exact Hle|].
  intros o1 Hin. rewrite forallb_forall in Hglob. specialize (Hglob _ Hin). apply Nat.ltb_lt in Hglob.
  apply (proj1 HP). exact Hglob.
Qed.

(** The callee gives an object back with contents that its
    postcondition describes, and the caller's state takes the opened
    object of the postcondition in its place. *)
Lemma give_one_sound ρ B B' st e X xs i t o pl ys cs :
  places_for B xs B' -> M ρ B st e X -> arg_obj gobjs st xs i = Some o ->
  (o < length (st_objs st))%nat -> forallb (aux_global gobjs) (o_aux t) = true ->
  nth_error B' i = Some pl -> obj_ok guard (fun _ => 0) B' pl (open_obj t) ys cs ->
  nth_error B o = Some pl /\ M ρ B (put_obj st o (Some (open_obj t))) e (list_set o (Some (ys, cs)) X).
Proof using Type.
  intros HP HM Ha Ho Hglob Hp' Hok. pose proof HM as (_ & _ & _ & _ & _ & (L1 & L2 & _)).
  destruct (nth_error B o) as [pl0|] eqn:Hp; [|apply nth_error_None in Hp; lia].
  pose proof (arg_obj_place B B' st xs i o pl0 HP Ha Hp) as E. rewrite Hp' in E. injection E as <-.
  split; [reflexivity|].
  apply (M_put_obj guard ge gobjs ρ B st e X _ o pl (open_obj t) ys cs HM Hp).
  - apply (open_obj_ok (fun _ => 0) ρ B' B pl t ys cs Hok). intros o1 Hin. rewrite forallb_forall in Hglob.
    specialize (Hglob _ Hin). apply Nat.ltb_lt in Hglob. symmetry. apply (proj1 HP). exact Hglob.
  - apply open_obj_wf.
  - apply length_list_set.
  - rewrite nth_error_list_set, Nat.eqb_refl.
    destruct (nth_error X o) eqn:Ex; [reflexivity | apply nth_error_None in Ex; lia].
  - intros k Hk. rewrite nth_error_list_set, (proj2 (Nat.eqb_neq k o) Hk). reflexivity.
Qed.

(** The result of a call is bound the way the machine binds it. *)
Lemma bind_result_sound ρ B B' st e X xs r ret out st' :
  places_for B xs B' -> M ρ B st e X -> dret ge B' ret out -> bind_result gobjs r ret st = Some st' ->
  exists e' ρ', returned_env r out e = Some e' /\ M ρ' B st' e' X.
Proof using Type.
  intros HP HM Hd Hb. destruct r as [|d k|rs]; cbn [bind_result] in Hb.
  - injection Hb as <-. exists e, ρ. split; [|exact HM].
    destruct ret as [c|]; cbn [dret] in Hd; [destruct Hd as (w & -> & _) | subst out]; reflexivity.
  - destruct ret as [c|]; [|discriminate]. destruct Hd as (w & -> & Hc).
    destruct (match c with CP o _ _ => negb (Nat.ltb o nglob) | _ => false end) eqn:Eg; [discriminate|].
    assert (Hc' : dcval ge B c w).
    { apply dcval_places with (B := B'); [exact Hc|]. intros o lo hi ->.
      apply negb_false_iff, Nat.ltb_lt in Eg. symmetry. apply (proj1 HP). exact Eg. }
    destruct (open_val c st) as [v st1] eqn:Eo.
    destruct (open_val_sound ρ B st e X c w v st1 HM Hc' Eo) as (ρ1 & HM1 & _ & Wv & Dv).
    destruct (tmp_at k v st1) as [[v' st2]|] eqn:Et; [|discriminate]. injection Hb as <-.
    destruct (tmp_at_sound guard ge gobjs ρ1 B st1 e X k v w v' st2 HM1 Wv Dv Et) as (w' & Ew & HR).
    destruct (R_bind guard ge gobjs ρ1 B e X st1 st2 v' w' d HR) as (ρ2 & HM2 & _).
    exists (put d w' e), ρ2. split; [|exact HM2]. cbn [returned_env]. rewrite Ew. reflexivity.
  - discriminate.
Qed.

Lemma first_spec_In r xs st : forall sps st',
  first_spec gobjs r xs st sps = Some st' -> exists sp, In sp sps /\ call_spec gobjs r xs st sp = Some st'.
Proof using Type.
  induction sps as [|sp sps IH]; intros st' H; [discriminate|]. cbn [first_spec] in H.
  destruct (call_spec gobjs r xs st sp) as [s|] eqn:E.
  - injection H as <-. exists sp. split; [left; reflexivity | exact E].
  - destruct (IH st' H) as (sp' & Hin & E'). exists sp'. split; [right; exact Hin | exact E'].
Qed.

(** * Arguments of a call on the machine

    The machine reads the arguments of a call one by one at their
    classes. An indirect call also converts each argument to the class
    of its parameter. When the classes are equal and are plain words,
    the conversion changes nothing. *)

Lemma args_x_split e args :
  map_option (arg_x ge e) args = map2_option (value_x ge e) (arg_classes args) (arg_values args).
Proof using Type.
  induction args as [|[k v] args IH]; [reflexivity|]. unfold arg_classes, arg_values in *.
  cbn [map map_option map2_option arg_x]. rewrite IH. reflexivity.
Qed.

Lemma map_option_length {X Y : Type} (f : X -> option Y) : forall xs ys,
  map_option f xs = Some ys -> length ys = length xs.
Proof using Type.
  induction xs as [|x xs IH]; intros ys H; cbn [map_option] in H; [injection H as <-; reflexivity|].
  destruct (f x) as [y|]; [|discriminate]. destruct (map_option f xs) as [ys'|] eqn:E; [|discriminate].
  injection H as <-. cbn [length]. rewrite (IH ys' eq_refl). reflexivity.
Qed.

Lemma generic_same : forall ks ws, forallb class_plain ks = true -> length ws = length ks ->
  map2_option (fun ft x => generic_word (fst ft) (snd ft) x) (combine ks ks) ws = Some ws.
Proof using Type.
  induction ks as [|k ks IH]; intros [|w ws] Hp Hl; try discriminate; [reflexivity|].
  cbn [forallb] in Hp. apply andb_prop in Hp as [Hk Hp]. injection Hl as Hl.
  cbn [combine map2_option fst snd]. rewrite (IH ws Hp Hl). destruct k; try discriminate; reflexivity.
Qed.

Lemma same_words_length ks ks' : same_words ks ks' = true -> length ks = length ks'.
Proof using Type.
  unfold same_words. destruct (map_option word_class ks) as [cs|] eqn:E1; [|discriminate].
  destruct (map_option word_class ks') as [cs'|] eqn:E2; [|discriminate]. intros H.
  apply andb_prop in H as [H _]. apply Nat.eqb_eq in H.
  rewrite <- (map_option_length _ _ _ E1), <- (map_option_length _ _ _ E2). exact H.
Qed.

Lemma all2_class_eq : forall ks ks', all2 class_eqb ks ks' = true -> ks = ks'.
Proof using Type.
  induction ks as [|k ks IH]; intros [|k' ks'] H; cbn [all2] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. rewrite (IH ks' H2). destruct k, k'; try discriminate; reflexivity.
Qed.

Lemma conv_same gf r args ws e :
  all2 class_eqb (arg_classes args) (map fst (fn_params gf)) = true ->
  forallb class_plain (map fst (fn_params gf)) = true ->
  same_words (result_words r) (return_words (fn_ret gf)) = true ->
  map_option (arg_x ge e) args = Some ws ->
  indirect_call_conv gf r args ws = Some (Converted ws None).
Proof using Type.
  intros Hc Hp Hw Hx. apply all2_class_eq in Hc. pose proof (map_option_length _ _ _ Hx) as Lw.
  assert (La : length args = length (map fst (fn_params gf))).
  { rewrite <- Hc. unfold arg_classes. rewrite length_map. reflexivity. }
  unfold indirect_call_conv. rewrite (proj2 (Nat.ltb_ge _ _)) by lia.
  rewrite (proj2 (Nat.ltb_ge _ _)) by (rewrite (same_words_length _ _ Hw); lia).
  rewrite !firstn_all2 by lia. fold (arg_classes args). rewrite Hc, generic_same, Hw; [reflexivity | exact Hp | lia].
Qed.

Lemma fn_check g p : lookup g (ge_globals ge) = Some p -> ptr_cap p = Fn g -> function_check_res ge p = Some ok.
Proof using Type. intros Hl Hc. unfold function_check_res. rewrite Hc, Hl, Z.eqb_refl. reflexivity. Qed.

End call.
