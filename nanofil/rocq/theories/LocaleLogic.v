(** The locale world in the program logic of Logic.v (docs/logic.md,
    "Strings the world lends"): [locale_wi], the world interpretation
    of a program that calls setlocale, over [[campaign|Campaign]] 4's
    [locale_world] (Locale.v), and what it gives the triples of
    LentLogic.v and HelloLocale.v.

    [locale_wi] rep m w h asks of the memory m and the ghost heap h:
    - [locale_ready]: setlocale's trusted representation rep, its
      writable roots, every category's name a readable C string, its
      read spans, the heap objects it owns, the names' aligned bases;
    - [roots_apart] and [ids_apart]: the roots setlocale writes and
      the objects it may release are apart from the program's pieces,
      as the frame of an external call needs ([prefix_agrees]);
    - [cap_private]: the object of every read, root and name capability
      owns no piece of h, so libc's locale memory is not the program's;
    - [names_current]: every ghost name piece is a category's current
      name with its text, so a [lent] token is the world's name.

    From it, [locale_wi_lent] is LentLogic.v's hypothesis [lent_at] for
    every ghost name, and [locale_wi_pre] and [locale_wi_query] are
    HelloLocale.v's premises on setlocale's query. A safepoint keeps
    it where it keeps rep and readiness ([locale_wi_safepoint]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic Locale
  LentLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## The world interpretation *)

(** The capability c names an object, read-write or read-only, that
    owns no piece of memory of h; a null or function capability names
    none. *)
Definition cap_private (h : gmap piece pval) (c : cap) : Prop :=
  forall b, c = Obj b \/ c = Ro b -> ids_apart [b] h.

(** Every ghost name piece of h is the current name, with its text, of
    a category of the world w. *)
Definition names_current (w : locale_world) (h : gmap piece pval) : Prop :=
  forall k p t, h !! PName k = Some (VName p t) ->
    In k locale_categories /\ p = locale_name w k /\ t = locale_text w k.

(** The world interpretation of a program that calls setlocale, whose
    trusted representation is rep: in the memory m and against the
    ghost heap h, the world w is ready, libc's roots and releasable
    objects are apart from the program's pieces, its read, root and
    name capabilities are private, and the ghost names are current. *)
Definition locale_wi (rep : mem -> locale_world -> Prop) (m : mem) (w : locale_world)
    (h : gmap piece pval) : Prop :=
  locale_ready rep m w /\ roots_apart (locale_roots w) h m /\ ids_apart (locale_owned w) h /\
  Forall (fun s => cap_private h (ptr_cap (span_ptr s))) (locale_reads w ++ locale_roots w) /\
  (forall k, In k locale_categories -> cap_private h (ptr_cap (locale_name w k))) /\
  names_current w h.

(** ## Lent names *)

(** An access that succeeds through a read-write or read-only
    capability of b, from a for n bytes, lies in b's region. *)
Lemma access_region m a c b n r al :
  (c = Obj b \/ c = Ro b) -> access_res m a c n r al = Some ok ->
  exists reg, object_region b (m_regions m) = Some reg /\ b <= a /\ a + n <= r_end reg.
Proof.
  intros Hc Ha. unfold access_res, cap_access_res in Ha.
  destruct Hc as [-> | ->]; destruct (object_region b (m_regions m)) as [reg|] eqn:E;
    try discriminate Ha.
  all: destruct ((b <=? a) && (a + n <=? r_end reg)) eqn:Hb; [|discriminate Ha].
  all: apply andb_true_iff in Hb as [H1 H2]; apply Z.leb_le in H1; apply Z.leb_le in H2.
  all: exists reg; auto.
Qed.

(** Under [locale_wi], in a memory whose live objects are apart, whose
    objects fit and whose freed objects are empty, every ghost name is
    lent where [lent_at] says: the category's name is a C string in a
    live object at a multiple of 8, which, being private, is none of
    the program's, so no live object owning a piece overlaps it. *)
Lemma locale_wi_lent rep m w h k p t :
  locale_wi rep m w h -> live_disjoint m -> objects_fit (m_regions m) -> freed_empty (m_regions m) ->
  h !! PName k = Some (VName p t) -> lent_at m h p t.
Proof.
  intros (Hready & _ & _ & _ & Hpriv & Hcur) Hd Hfit Hfree Hk.
  destruct (Hcur _ _ _ Hk) as (Hcat & -> & ->).
  pose proof Hready as (_ & _ & Hstr & _ & _ & Hal).
  destruct (Hstr k Hcat) as [Hnz Hcs]. destruct (Hal k Hcat) as (b & Hc & Hb8).
  destruct (access_region _ _ _ _ _ _ _ Hc (proj1 Hcs)) as (reg & E & Hlo & Hhi).
  destruct (Hfit b reg E) as [Hb0 H48].
  assert (L : r_life reg = Live).
  { destruct (r_life reg) eqn:L; [reflexivity|]. pose proof (Hfree b reg E L). lia. }
  split; [exact Hcs|]. split; [lia|]. split; [lia|]. split; [exists b; auto|].
  intros a Ha (l & v & reg' & Hl & Hm & Hlv & Hin).
  assert (Hne : piece_id l <> b) by exact (Hpriv k Hcat b Hc b l v (or_introl eq_refl) Hl Hm).
  destruct (Hd _ _ _ _ Hlv (conj E L) Hne); lia.
Qed.

(** The locale logic over any [[runtime]] R. *)
Module LocaleLogic (R : Runtime).
Module LL := LentLogic R.
Module LG := LL.LG.
Module L := LG.L.
Import L LG.

(** setlocale's query of a category whose name is lent is admitted:
    the world is ready and the category is one of its own. *)
Lemma locale_wi_pre rep requests m w h k p t z :
  locale_wi rep m w h -> h !! PName k = Some (VName p t) -> ptr_addr z = 0 ->
  contract_pre (setlocale_contract rep requests) [WInt k; WPtr z] m w.
Proof.
  intros (Hready & _ & _ & _ & _ & Hcur) Hk Hz. destruct (Hcur _ _ _ Hk) as (Hcat & _ & _).
  split; [exact Hready|]. exists k, z. auto.
Qed.

(** setlocale's query of a category whose name is lent returns that
    name and changes nothing. *)
Lemma locale_wi_query rep requests r args s m w h k p t z trace ending s' m' w' :
  locale_wi rep m w h -> h !! PName k = Some (VName p t) -> ptr_addr z = 0 ->
  M.E.invoke (setlocale_contract rep requests) r args [WInt k; WPtr z] s m w trace ending s' m' w' ->
  s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr p].
Proof.
  intros (_ & _ & _ & _ & _ & Hcur) Hk Hz Hi. destruct (Hcur _ _ _ Hk) as (_ & -> & _).
  assert (Hq : locale_query [WInt k; WPtr z] = true) by (cbn; rewrite Hz; reflexivity).
  destruct Hi as [trace ending s' m' w' born _ _ [He [_ Hp]] Hpost _ _ _
                 |why trace s' m' w' born _ _ [He [_ Hp]] Hfail _].
  - unfold setlocale_contract in Hp, Hpost, He.
    cbn [contract_prefix contract_post contract_requests] in Hp, Hpost, He.
    unfold setlocale_prefix in Hp. rewrite Hq in Hp.
    destruct Hp as (_ & -> & ->).
    destruct Hpost as (c & q & Hxs & Hend). injection Hxs as <- _. rewrite Hq in Hend.
    split; [|auto]. clear -He Hq. induction He; [reflexivity | exact IHHe |].
    destruct H as [Hfalse _]. congruence.
  - exfalso. unfold setlocale_contract in Hfail. cbn [contract_requests] in Hfail. destruct Hfail as [al sz [Hfalse _] _ _ | al sz [Hfalse _] _]; congruence.
Qed.

(** A safepoint keeps [locale_wi] where it keeps rep and readiness: the
    roots stay apart since no region changes ([collector_live]), and the
    rest is of the world and the ghost heap. *)
Lemma locale_wi_safepoint (rep : mem -> locale_world -> Prop) :
  (forall s m s' m' w, R.safepoint s m s' m' -> locale_ready rep m w -> locale_ready rep m' w) ->
  SafepointStable (locale_wi rep).
Proof.
  intros Hst. split. intros s m s' m' w h Hsp (Hr & Ha & Hrest).
  split; [exact (Hst _ _ _ _ _ Hsp Hr)|]. split; [|exact Hrest].
  intros sp a Hin Hs (l & v & reg & Hl & Hm & [E Hlive] & Hb). apply (Ha sp a Hin Hs).
  rewrite (R.collector_live _ _ _ _ Hsp) in E. exists l, v, reg. split; [exact Hl|]. split; [exact Hm|].
  split; [|exact Hb]. split; [exact E | exact Hlive].
Qed.

End LocaleLogic.
