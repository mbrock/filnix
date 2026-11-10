(** The program logic's frame for [[external call|external calls]]
    (Logic.v, docs/logic.md): what a call through a contract leaves of
    the ghost heap of Heap.v.

    A call changes memory along an [effects] path of
    [[campaign|Campaign]] 4 (ExternalCalls.v): [local_effect] segments,
    which write bytes and [[aux]] slots only where the call has
    [write_authority] and change an object only by freeing a live heap
    object it may release or allocated itself, and allocations at a
    [fresh] base, which join the call's born objects. The program logic
    owns pieces of memory ([agrees] with a ghost heap h), and asks what
    of them survives the call.

    The premise is separation by address, not by identity: no address
    of a contract's writable roots lies in a live object that owns a
    piece of h ([roots_apart]), and the contract releases none of h's
    identities ([ids_apart]). Then the call's born objects are not the
    program's, it writes nothing the program owns, and after the whole
    path h still agrees with memory and live objects are still apart
    (Logic.v's [effects_agrees], [prefix_agrees] and [invoke_agrees],
    over the language's own call relations). A world's new
    roots that a call delegates from its old roots and born objects
    stay apart as well ([delegates_apart]).

    A call may also write blocks the program hands it, such as
    mbrtowc's output, state and errno cells. Then its roots touch the
    program's objects only at the addresses of those blocks
    ([roots_out]), and every piece but the handed-over ones keeps
    agreeing ([agrees_except], [local_agrees_out]; Logic.v's
    [effects_agrees_out] and [prefix_agrees_out]).

    Byte and aux pieces of an object that is not live need only stay
    registered, and an aux piece of a live one is known up to
    [aux_holds]; regions of old identities change only by being freed,
    so a freed capability stays freed and one that traps as freed keeps
    trapping ([freed_in_step], [traps_as_freed_step]). Released or not,
    no piece but a life token needs its object kept live; a life token
    does, which is what [ids_apart] of the releases gives. *)

From iris.proofmode Require Import proofmode.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Identity ExternalCalls Pieces Heap.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Separation of a call from the program's pieces *)

(** The address a lies in a live object of m that owns a piece of
    memory in the ghost heap h. *)
Definition owned_live (h : gmap piece pval) (m : mem) (a : Z) : Prop :=
  exists l v reg, h !! l = Some v /\ mem_piece l /\ live_at m (piece_id l) reg /\
    piece_id l <= a < r_end reg.

(** No address of the spans roots lies in a live object owning a piece
    of h. *)
Definition roots_apart (roots : list span) (h : gmap piece pval) (m : mem) : Prop :=
  forall s a, In s roots -> span_contains s a -> ~ owned_live h m a.

(** None of the identities bs is that of a piece of memory in h. *)
Definition ids_apart (bs : list Z) (h : gmap piece pval) : Prop :=
  forall b l v, In b bs -> h !! l = Some v -> mem_piece l -> piece_id l <> b.

(** A call whose roots are apart from h and whose born objects are none
    of h's has no [write_authority] over an address of a live object
    owning a piece of h: a born live heap object overlapping it would be
    another live object over the same address. *)
Lemma owned_not_authority : forall roots born h m a,
  live_disjoint m -> roots_apart roots h m -> ids_apart born h ->
  owned_live h m a -> ~ write_authority roots born m a.
Proof.
  intros roots born h m a Hd Hr Hb Ho [(s & Hin & _ & Hs) | (base & reg & Hin & E & _ & L & Ha)].
  - exact (Hr s a Hin Hs Ho).
  - destruct Ho as (l & v & reg0 & Hl & Hm & Hlive & Ha0).
    specialize (Hb base l v Hin Hl Hm).
    destruct (Hd (piece_id l) reg0 base reg Hlive (conj E L) Hb); lia.
Qed.

(** ## Steps that keep old identities *)

(** A freed object's capability stays freed across a step that keeps
    every identity ([ids]) and changes an object only by ending a live
    one ([region_step]). *)
Lemma freed_in_step : forall m m' c,
  ids m m' -> region_step m m' -> freed_in (m_regions m) c -> freed_in (m_regions m') c.
Proof.
  intros m m' c Hi Hs (b & reg & Hc & E & L). destruct (Hi b reg E) as [reg' E'].
  destruct (Hs b reg' E') as (reg0 & E0 & [-> | (L0 & _)]); rewrite E in E0; injection E0 as <-.
  - exists b, reg. auto.
  - congruence.
Qed.

(** A capability that traps as a freed one keeps doing so across such
    a step: its object's region is kept, or emptied. *)
Lemma traps_as_freed_step : forall m m' c,
  ids m m' -> region_step m m' -> traps_as_freed (m_regions m) c -> traps_as_freed (m_regions m') c.
Proof.
  intros m m' c Hi Hs H a size r align Hsz. specialize (H a size r align Hsz).
  assert (Hempty : forall b, (b <=? a) && (a + size <=? b) = false).
  { intros b. destruct (Z.leb_spec b a); cbn [andb]; [apply Z.leb_gt; lia | reflexivity]. }
  assert (Hreg : forall b reg, object_region b (m_regions m) = Some reg ->
            object_region b (m_regions m') = Some reg \/
            object_region b (m_regions m') = Some (mkRegion b b (r_kind reg) Freed)).
  { intros b reg E. destruct (Hi b reg E) as [reg' E'].
    destruct (Hs b reg' E') as (reg0 & E0 & [-> | (_ & ->)]); rewrite E in E0; injection E0 as <-; auto. }
  destruct c as [|b|b|f|n]; cbn [cap_access_res] in H |- *; try exact H;
    (destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|discriminate H]);
    (destruct (Hreg b reg E) as [E'|E']; rewrite E'; [exact H|]);
    cbn [r_end]; rewrite Hempty; reflexivity.
Qed.

(** ## A call into owned blocks *)

(** Every piece of h but the keys ks agrees with m: a ghost heap whose
    pieces ks a call may overwrite. *)
Definition agrees_except (ks : list piece) (m : mem) (h : gmap piece pval) : Prop :=
  forall l v, h !! l = Some v -> l ∉ ks -> agree_piece m l v.

(** Every address of the spans roots that lies in a live object owning
    a piece of h is one of the addresses out, which the program hands
    to the call. *)
Definition roots_out (roots : list span) (h : gmap piece pval) (m : mem) (out : Z -> Prop) : Prop :=
  forall s a, In s roots -> span_contains s a -> owned_live h m a -> out a.

(** No byte or aux piece of h but the keys ks, of a live object of m
    and in its bounds, lies at an address out. *)
Definition pieces_off (ks : list piece) (h : gmap piece pval) (m : mem) (out : Z -> Prop) : Prop :=
  forall l v, h !! l = Some v -> l ∉ ks ->
    match l with
    | PByte b o | PAux b o => forall reg, live_at m b reg -> 0 <= o -> b + o < r_end reg -> ~ out (b + o)
    | _ => True
    end.

(** With nothing out, roots that avoid h's live objects. *)
Lemma roots_out_apart roots h m : roots_apart roots h m -> roots_out roots h m (fun _ => False).
Proof. intros Hra s a Hin Hs Ho. exact (Hra s a Hin Hs Ho). Qed.

(** ## A local effect *)

(** One [local_effect] of a call, from m to m', against the ghost heap h. *)
Section Local.

(** The call's sources, roots, releases and born objects, the memories
    before and after, and the ghost heap. *)
Variables (sources roots : list span) (releases born : list Z) (m m' : mem) (h : gmap piece pval).

(** The step is a [local_effect]. *)
Hypothesis Hl : local_effect sources roots releases born m m'.

(** A live object of m' was live in m with the same region: a local
    effect only ends objects. *)
Lemma local_live_back : forall b reg, live_at m' b reg -> live_at m b reg.
Proof.
  intros b reg [E L]. destruct Hl as (_ & Hr & _).
  destruct (Hr b reg E) as (reg0 & E0 & [-> | (_ & _ & _ & ->)]); [split; assumption | discriminate L].
Qed.

(** A local effect keeps live objects apart. *)
Lemma local_live_disjoint : live_disjoint m -> live_disjoint m'.
Proof.
  intros Hd b1 r1 b2 r2 H1 H2. exact (Hd b1 r1 b2 r2 (local_live_back _ _ H1) (local_live_back _ _ H2)).
Qed.

(** An address of a live owned object of m' was one of m. *)
Lemma local_owned_back : forall a, owned_live h m' a -> owned_live h m a.
Proof.
  intros a (l & v & reg & Hh & Hm & Hlive & Ha). exists l, v, reg. split; [exact Hh|].
  split; [exact Hm|]. split; [exact (local_live_back _ _ Hlive) | exact Ha].
Qed.

(** A local effect keeps every piece of h but the keys ks agreeing,
    where every root address in an object the program owns is out, no
    piece of h but ks lies at an address out, and the effect releases
    none of h's identities and was born with none of them. The program
    hands the call the pieces ks, at the addresses out. *)
Lemma local_agrees_out (ks : list piece) (out : Z -> Prop) : live_disjoint m -> agrees_except ks m h ->
  roots_out roots h m out -> pieces_off ks h m out ->
  ids_apart releases h -> ids_apart born h -> agrees_except ks m' h.
Proof.
  intros Hd Ha Hra Hoff Hrel Hb l v Hh Hk. pose proof (Ha l v Hh Hk) as Hp.
  pose proof (Hoff l v Hh Hk) as Hno.
  pose proof (local_effect_kept _ _ _ _ _ _ Hl) as [Hs _].
  pose proof Hl as (Hi & Hr & Hw & _).
  (* An address of a live object of m owning a piece of h, not out,
     keeps its byte and aux slot. *)
  assert (Hkeep : forall reg o, mem_piece l -> live_at m (piece_id l) reg -> 0 <= o -> piece_id l + o < r_end reg ->
            ~ out (piece_id l + o) ->
            m_bytes m' (piece_id l + o) = m_bytes m (piece_id l + o) /\
            m_aux m' (piece_id l + o) = m_aux m (piece_id l + o)).
  { intros reg o Hm Hlive Ho He Hout. apply Hw.
    assert (Hown : owned_live h m (piece_id l + o)).
    { exists l, v, reg. split; [exact Hh|]. split; [exact Hm|]. split; [exact Hlive|lia]. }
    intros [(s & Hin & _ & Hsp) | Hborn].
    - exact (Hout (Hra s _ Hin Hsp Hown)).
    - exact (owned_not_authority [] born h m _ Hd (fun s a Hin => match Hin with end) Hb Hown
               (or_intror Hborn)). }
  destruct l as [b|b o|b o|k], v as [reg|x|c| |q t|cd|sq sp|ga gi|op]; cbn [agree_piece piece_id] in Hp, Hkeep, Hno |- *;
    try contradiction; try exact I.
  - destruct Hp as [E L]. destruct (Hi b reg E) as [reg' E'].
    destruct (Hr b reg' E') as (reg0 & E0 & [-> | (Hin & _)]); rewrite E in E0; injection E0 as <-.
    + split; assumption.
    + exfalso. apply in_app_or in Hin as [Hin|Hin];
        [exact (Hrel b (PLive b) (VLive reg) Hin Hh I eq_refl) | exact (Hb b (PLive b) (VLive reg) Hin Hh I eq_refl)].
  - unfold registered in *. destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|contradiction].
    destruct (Hi b reg E) as [reg' ->]. discriminate.
  - destruct Hp as [Hreg Hin]. split.
    + unfold registered in *.
      destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|contradiction].
      destruct (Hi b reg E) as [reg' ->]. discriminate.
    + intros reg' E' L'. destruct (local_live_back b reg' (conj E' L')) as [E L].
      destruct (Hin reg' E L) as (Ho & He & Hx).
      split; [exact Ho|]. split; [exact He|]. rewrite (proj1 (Hkeep reg' o I (conj E L) Ho He (Hno reg' (conj E L) Ho He))). exact Hx.
  - destruct Hp as [Hreg Hin]. split.
    + unfold registered in *.
      destruct (object_region b (m_regions m)) as [reg|] eqn:E; [|contradiction].
      destruct (Hi b reg E) as [reg' ->]. discriminate.
    + intros reg' E' L'. destruct (local_live_back b reg' (conj E' L')) as [E L].
      destruct (Hin reg' E L) as (Ho & He & Hx).
      split; [exact Ho|]. split; [exact He|]. unfold aux_holds in *.
      rewrite (proj2 (Hkeep reg' o I (conj E L) Ho He (Hno reg' (conj E L) Ho He))).
      destruct Hx as [Hx | [Hf Ht]]; [left; exact Hx | right].
      split; [exact (freed_in_step m m' _ Hi Hs Hf) | exact (traps_as_freed_step m m' _ Hi Hs Ht)].
Qed.

(** A local effect whose roots are apart from h, that releases none of
    h's identities and was born with none of them, keeps h agreeing. *)
Lemma local_agrees : live_disjoint m -> agrees m h -> roots_apart roots h m ->
  ids_apart releases h -> ids_apart born h -> agrees m' h.
Proof.
  intros Hd Ha Hra Hrel Hb l v Hh.
  apply (local_agrees_out [] (fun _ => False) Hd); [| exact (roots_out_apart _ _ _ Hra) | | exact Hrel |
    exact Hb | exact Hh | apply not_elem_of_nil].
  - intros l' v' Hl' _. exact (Ha l' v' Hl').
  - intros l' v' _ _. destruct l'; auto.
Qed.

End Local.

(** ## An allocation *)

(** A live object of m after an allocation at a new base, other than
    the new object, was live in m with the same region. *)
Lemma allocated_live_back : forall m q base b reg,
  base <> b -> live_at (allocated m q base) b reg -> live_at m b reg.
Proof.
  intros m q base b reg Hne [E L]. rewrite object_region_allocated in E.
  destruct (Z.eqb_spec base b) as [<-|_]; [contradiction | split; assumption].
Qed.

(** An address of a live owned object after an allocation at a base
    that is no object of m was one of m: owned objects are registered. *)
Lemma allocated_owned_back : forall m q base h a,
  object_region base (m_regions m) = None -> agrees m h ->
  owned_live h (allocated m q base) a -> owned_live h m a.
Proof.
  intros m q base h a Hn Ha (l & v & reg & Hh & Hm & Hlive & Hr). exists l, v, reg. split; [exact Hh|].
  split; [exact Hm|]. split; [|exact Hr]. apply (allocated_live_back m q base); [|exact Hlive].
  intros E. apply (agree_piece_registered m l v Hm (Ha l v Hh)). rewrite <- E. exact Hn.
Qed.

(** A base that is no object of m is none of the identities of a ghost
    heap that agrees with m. *)
Lemma unregistered_apart : forall m h base bs,
  object_region base (m_regions m) = None -> agrees m h -> ids_apart bs h -> ids_apart (base :: bs) h.
Proof.
  intros m h base bs Hn Ha Hb b l v [<-|Hin] Hh Hm.
  - intros E. apply (agree_piece_registered m l v Hm (Ha l v Hh)). rewrite E. exact Hn.
  - exact (Hb b l v Hin Hh Hm).
Qed.

(** ## Delegated roots *)

(** A world's new roots, delegated in m from the old roots and the
    born objects ([stdio_delegates]), avoid h's live objects when the
    old roots do and the born objects are none of h's: every address of
    a new root is one the call has [write_authority] over. *)
Lemma delegates_apart : forall roots born m w h,
  stdio_delegates roots born m w -> roots_apart roots h m -> ids_apart born h -> live_disjoint m ->
  roots_apart (stdio_roots w) h m.
Proof.
  intros roots born m w h Hdel Hra Hb Hd s a Hin Hs Ho.
  destruct (Hdel s Hin) as [_ Hw].
  exact (owned_not_authority roots born h m a Hd Hra Hb Ho (Hw a Hs)).
Qed.
