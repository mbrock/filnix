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
    HelloLocale.v's premises on setlocale's query, the latter from
    Campaign 4's [LocaleOn] instance over the logic's own machine. A safepoint keeps
    it where it keeps rep and readiness ([locale_wi_safepoint]).

    A setter keeps it too, with every category renamed to its new name
    ([locale_wi_setter]): the frame keeps libc's roots apart, and
    Campaign 4's private provenance ([locale_delegates_private]) makes
    every new read, root and name a born object or an old private one.
    [locale_set_return] is that for setlocale(c, p), in the form of
    [wp_lend]'s premise, and [wp_setlocale_set] is the setter's triple. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
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

(** ## Renaming the ghost names *)

(** Renaming keeps every piece of memory. *)
Lemma rename_mem h ks new l : mem_piece l -> rename h ks new !! l = h !! l.
Proof.
  intros Hm. induction ks as [|k ks IH]; [reflexivity|]. cbn [rename].
  rewrite lookup_insert_ne; [exact IH|]. intros <-. exact Hm.
Qed.

(** A key renaming does not touch keeps its name. *)
Lemma rename_out h ks new k : ~ In k ks -> rename h ks new !! PName k = h !! PName k.
Proof.
  intros Hk. induction ks as [|k' ks IH]; [reflexivity|]. cbn [rename].
  rewrite lookup_insert_ne; [|intros E; injection E as ->; apply Hk; left; reflexivity].
  apply IH. intros Hin. apply Hk. right. exact Hin.
Qed.

(** An address a renamed heap owns, the heap owned. *)
Lemma owned_live_rename h ks new m a : owned_live (rename h ks new) m a -> owned_live h m a.
Proof.
  intros (l & v & reg & Hl & Hm & Hlv & Hin). exists l, v, reg.
  rewrite (rename_mem _ _ _ _ Hm) in Hl. auto.
Qed.

(** Objects apart from h are apart from it renamed. *)
Lemma ids_apart_rename bs h ks new : ids_apart bs h -> ids_apart bs (rename h ks new).
Proof. intros Ha b l v Hb Hl Hm. rewrite (rename_mem _ _ _ _ Hm) in Hl. exact (Ha b l v Hb Hl Hm). Qed.

(** A capability private to h is private to it renamed. *)
Lemma cap_private_rename h ks new c : cap_private h c -> cap_private (rename h ks new) c.
Proof. intros Hc b Hb. apply ids_apart_rename. exact (Hc b Hb). Qed.

(** What the setter's [locale_retained_cap] keeps private: a born
    object, apart from h, or an old private source's own capability. *)
Lemma retained_private rep m w h born c :
  locale_wi rep m w h -> ids_apart born h -> locale_retained_cap w born c -> cap_private h c.
Proof.
  intros (_ & _ & _ & Hsrc & Hnames & _) Hb [(base & Hin & Hc) | (s & Hin & ->)].
  - intros b Hc'. assert (b = base) as ->.
    { destruct Hc as [-> | ->]; destruct Hc' as [E | E]; congruence. }
    intros b' l v Hb' Hl Hm. destruct Hb' as [<- | []]. exact (Hb base l v Hin Hl Hm).
  - unfold locale_private_sources in Hin. apply in_app_or in Hin as [Hin | Hin].
    + rewrite List.Forall_forall in Hsrc. exact (Hsrc s Hin).
    + apply in_map_iff in Hin as (k & <- & Hk). exact (Hnames k Hk).
Qed.

(** The new names, after a setter, of every category of the world w'. *)
Definition current_names (w' : locale_world) : Z -> ptr * list Z :=
  fun k => (locale_name w' k, locale_text w' k).

(** After a setter with private provenance, from the world w against
    the ghost heap h, to the world w' in m': if w' is ready, the frame
    kept h agreeing and libc's old roots apart, and the born objects
    are none of h's, then [locale_wi] holds of w' and h with every
    category renamed to its new name. *)
Lemma locale_wi_setter rep xs m w h born m' w' :
  locale_wi rep m w h -> locale_ready rep m' w' -> locale_delegates xs m w born m' w' ->
  live_disjoint m' -> roots_apart (locale_roots w) h m' -> ids_apart born h ->
  locale_wi rep m' w' (rename h locale_categories (current_names w')).
Proof.
  intros Hwi Hready Hdel Hd Hra Hb. pose proof Hwi as (_ & _ & Hown & _ & _ & Hcur).
  pose proof Hdel as (Hroots & _ & _ & Howned).
  split; [exact Hready|]. split; [|split; [|split; [|split]]].
  - intros sp a Hin Hs Ho. apply owned_live_rename in Ho.
    exact (owned_not_authority _ _ _ _ _ Hd Hra Hb Ho (proj2 (Hroots sp Hin) a Hs)).
  - apply ids_apart_rename. intros b l v Hin Hl Hm.
    destruct (Howned b Hin) as [Hin' _]. apply in_app_or in Hin' as [Hin' | Hin'];
      [exact (Hown b l v Hin' Hl Hm) | exact (Hb b l v Hin' Hl Hm)].
  - apply List.Forall_forall. intros sp Hin. apply cap_private_rename.
    apply (retained_private rep m w h born _ Hwi Hb).
    apply (locale_delegates_private _ _ _ _ _ _ _ Hdel). unfold locale_private_sources.
    apply in_or_app. left. exact Hin.
  - intros k Hk. apply cap_private_rename. apply (retained_private rep m w h born _ Hwi Hb).
    apply (locale_delegates_private _ _ _ _ _ _ (locale_name_span w' k) Hdel).
    unfold locale_private_sources. apply in_or_app. right. apply in_map. exact Hk.
  - intros k p t Hl. destruct (In_dec Z.eq_dec k locale_categories) as [Hk | Hk].
    + rewrite (rename_lookup _ _ _ _ Hk) in Hl. injection Hl as <- <-. auto.
    + rewrite (rename_out _ _ _ _ Hk) in Hl. exfalso. apply Hk. exact (proj1 (Hcur _ _ _ Hl)).
Qed.

(** The locale logic over any [[runtime]] R. *)
Module LocaleLogic (R : Runtime).
Module LL := LentLogic R.
Module LG := LL.LG.
Module L := LG.L.
Module LC := LocaleOn R L.M.
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
  destruct (LC.setlocale_query_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hz Hi)
    as (_ & -> & -> & -> & ->). auto.
Qed.

(** setlocale's setter of the category c, with a string argument p,
    keeps the frame of a program under [locale_wi]: every invocation
    that returns, from a state interpreted with the ghost heap h,
    returns null or c's new name, keeps h agreeing, the live objects
    apart and the runtime ready, and [locale_wi] holds of h with every
    category renamed to its new name ([locale_wi_setter]). This is
    [wp_lend]'s premise for setlocale(c, p), with the new names
    [current_names] of the world after the call. *)
Lemma locale_set_return rep requests r args s m w h c p trace values s' m' w' :
  locale_wi rep m w h -> agrees m h -> live_disjoint m -> R.ready s m -> ptr_addr p <> 0 ->
  M.E.invoke (setlocale_contract rep requests) r args [WInt c; WPtr p] s m w trace (CallReturn values)
    s' m' w' ->
  exists q new, values = [WPtr q] /\ (q = mkPtr 0 CNone \/ q = (new c).1) /\
    agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\
    locale_wi rep m' w' (rename h locale_categories new).
Proof.
  intros Hwi Ha Hd Hr Hp Hi.
  assert (Hq : locale_query [WInt c; WPtr p] = false) by (cbn; apply Z.eqb_neq; exact Hp).
  pose proof Hwi as (_ & Hra & Hown & _).
  remember (CallReturn values) as en eqn:Een.
  destruct Hi as [trace ending s' m' w' born _ _ Hpre Hpost _ _ _ | why trace s' m' w' born _ _ _ _ _];
    [|discriminate Een]. subst ending.
  destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
  assert (Hw : roots_apart (contract_writes (setlocale_contract rep requests) [WInt c; WPtr p] m w) h m).
  { unfold setlocale_contract. cbn [contract_writes]. unfold locale_writes. rewrite Hq. exact Hra. }
  assert (Hrel : ids_apart (contract_releases (setlocale_contract rep requests) [WInt c; WPtr p] m w) h).
  { unfold setlocale_contract. cbn [contract_releases]. unfold locale_releases. rewrite Hq. exact Hown. }
  destruct (prefix_agrees _ _ _ _ _ _ _ _ _ _ _ h Hpre Hr Hd Ha Hw Hrel) as (Ha' & Hd' & Hb & Hra').
  unfold setlocale_contract in Hra'. cbn [contract_writes] in Hra'. unfold locale_writes in Hra'.
  rewrite Hq in Hra'.
  destruct Hpre as [_ [_ Hpre]]. unfold setlocale_contract in Hpre. cbn [contract_prefix] in Hpre.
  rewrite Hq in Hpre. destruct Hpre as (Hready & Hdel & _).
  unfold setlocale_contract in Hpost. cbn [contract_post] in Hpost.
  destruct Hpost as (c' & p' & Hxs & Hend). injection Hxs as <- <-. rewrite Hq in Hend.
  exists (match values with [WPtr q] => q | _ => mkPtr 0 CNone end), (current_names w').
  destruct Hend as [[Hv _] | [Hv _]]; injection Hv as ->.
  all: split; [reflexivity|]; split; [auto|].
  all: split; [exact Ha'|]; split; [exact Hd'|]; split; [exact Hr'|].
  all: exact (locale_wi_setter _ _ _ _ _ _ _ _ Hwi Hready Hdel Hd' Hra' Hb).
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

(** ## The setter's triple *)

Section setter.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (registry : name -> option (contract locale_world)) (rep : mem -> locale_world -> Prop)
  (requests : list word -> mem -> locale_world -> Z -> Z -> Prop)
  `{!SafepointStable (locale_wi rep)} (ge : genv).

(** The Iris instance of the registry and [locale_wi]. *)
Local Instance setter_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (locale_wi rep) ge.

(** The expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** setlocale(c, p)'s triple over the locale world, from [wp_lend]
    and [locale_set_return]: owning every category's name and the
    string at p, which vc and vp read as, the call lends every
    category's new name for good and binds d to null or c's new
    name. *)
Lemma wp_setlocale_set f e ls lab d vc vp rest j c p b reg bytes old Φ :
  registry (TAtom "setlocale") = Some (setlocale_contract rep requests) ->
  find_fn ge (TAtom "setlocale") = None -> lookup (TAtom "setlocale") (ge_globals ge) = None ->
  arg_x ge e (Arg W vc) = Some (WInt c) -> arg_x ge e (Arg P vp) = Some (WPtr p) ->
  In c locale_categories ->
  ([∗ list] k ∈ locale_categories, LL.named k (old k).1 (old k).2) -∗ LL.SL.string p b reg bytes -∗
  ▷ (∀ q (new : Z -> ptr * list Z), ⌜q = mkPtr 0 CNone \/ q = (new c).1⌝ -∗
     LL.SL.string p b reg bytes -∗ ([∗ list] k ∈ locale_categories, LL.lent k (new k).1 (new k).2) -∗
     WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "setlocale")) [Arg W vc; Arg P vp] :: rest) j))
        : sexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hc Hp Hcat. iIntros "Hks Hs HK".
  iDestruct "Hs" as "[%Hok Hs]". pose proof Hok as (_ & Hb0 & Hlo & _).
  iAssert (LL.SL.string p b reg bytes) with "[Hs]" as "Hs"; [iSplit; [done | iExact "Hs"]|].
  iApply (LL.wp_lend registry (locale_wi rep) ge (locale_wi_lent rep) f e ls lab d (TAtom "setlocale")
            [Arg W vc; Arg P vp] rest j (setlocale_contract rep requests) [WInt c; WPtr p]
            locale_categories old (fun q new => q = mkPtr 0 CNone \/ q = (new c).1) with "Hks Hs HK");
    [exact Hreg | reflexivity | exact Hfn | exact Hdata | reflexivity |
     cbn [map_option]; rewrite Hc Hp; reflexivity | | | ].
  - split; [right; eexists; reflexivity | do 2 eexists; reflexivity].
  - iIntros (σ) "Hσ Hs". iDestruct (LL.SL.string_facts with "Hσ Hs") as %[_ Hcs].
    iDestruct "Hσ" as (h) "[_ %Hf]". destruct Hf as (_ & _ & _ & Hready & _). iPureIntro.
    split; [exact Hready|]. exists c, p. split; [reflexivity|]. split; [exact Hcat|]. right. eauto.
  - intros s m w h trace values s' m' w' Hw Ha Hd Hr Hi.
    assert (Hnz : ptr_addr p <> 0) by lia.
    exact (locale_set_return rep requests _ _ _ _ _ _ _ _ _ _ _ _ _ Hw Ha Hd Hr Hnz Hi).
Qed.

End setter.

End LocaleLogic.
