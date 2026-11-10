(** Strings the world lends, in the program logic of Logic.v
    (docs/logic.md). setlocale(k, NULL) returns libc's own name for the
    locale category k: memory the program does not own and may read
    only while the world keeps it. A weakest precondition cannot
    remember across steps which string a query returned, since the
    memory and the world are the state, not the assertion. A ghost
    piece does ([PName] of Pieces.v): [lent] k p t says the world lends
    the string t at p under the key k, and the world interpretation
    wi ties every such piece to the world.

    What a proof needs of wi is one fact, [lent_at]: a lent string is a
    C string ([c_string]), in an object at a multiple of 8, and apart
    from every object owning a piece of memory in the ghost heap. Its
    triples are generic in wi under that hypothesis:

    - [wp_lent_query]: a call that returns the lent pointer and changes
      nothing, such as setlocale's query;
    - [wp_strlen_lent]: strlen of a lent string;
    - [wp_memcpy_lent]: memcpy of a prefix of a lent string, with its
      NUL, into an owned block, whose aux slots afterwards are what the
      copy left there ([slots_after]).

    The token is persistent: a lent string is read, never given back,
    so no triple changes a lent string. Before it is lent, a name is
    owned whole ([named]), and a setter that changes it, such as
    setlocale(LC_ALL, ""), takes it:

    - [wp_lend]: a call that renames the keys whose names it is given,
      and lends the new names. The ghost heap renames them
      ([rename_update]); what the call must keep of the state is its
      premise, for the contract and wi to discharge. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Stdlib Require String.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Panics
  StepRules ExternalCalls ExternalMachine Pieces Heap ContractFrame Language Logic StringLogic
  MemLogic.
Open Scope Z_scope.
Open Scope list_scope.

(** ## Lent strings in the memory *)

(** The string t at p, lent by the world, in the memory m and against
    the ghost heap h: a C string through its NUL, not at null and
    ending before 2^64,
    in an object, or a read-only one, at a multiple of 8, and no byte
    of it in a live object owning a piece of memory of h. *)
Definition lent_at (m : mem) (h : gmap piece pval) (p : ptr) (t : list Z) : Prop :=
  c_string m p t /\ 0 < ptr_addr p /\ ptr_addr p + Z.of_nat (length t) < 2 ^ 64 /\
  (exists b, (ptr_cap p = Obj b \/ ptr_cap p = Ro b) /\ b mod 8 = 0) /\
  (forall a, ptr_addr p <= a <= ptr_addr p + Z.of_nat (length t) -> ~ owned_live h m a).

(** The i-th byte of a string in memory. *)
Lemma string_at_lookup m a t i y : string_at m a t -> t !! i = Some y -> m_bytes m (a + Z.of_nat i) = y.
Proof.
  revert a i. induction t as [|x t IH]; intros a i Hs Hy; [discriminate Hy|].
  destruct Hs as (_ & Hx & Hs). destruct i as [|i]; cbn in Hy.
  - injection Hy as <-. rewrite Z.add_0_r. exact Hx.
  - replace (a + Z.of_nat (S i)) with (a + 1 + Z.of_nat i) by lia. exact (IH _ _ Hs Hy).
Qed.

(** Overwriting pieces of memory keeps every name. *)
Lemma overwrite_name ps h k :
  Forall mem_piece ps.*1 -> overwrite ps h !! PName k = h !! PName k.
Proof.
  induction ps as [|[l v] ps IH]; intros Hm; [reflexivity|].
  inversion Hm as [|? ? Hl Hps]; subst. cbn [overwrite fst snd].
  rewrite lookup_insert_ne; [exact (IH Hps)|]. intros ->. exact Hl.
Qed.

(** The bytes of a string in memory are not NUL. *)
Lemma string_at_nonzero m a t : string_at m a t -> Forall (fun x => 0 < x < 256) t.
Proof.
  revert a. induction t as [|x t IH]; intros a Hs; [constructor|].
  destruct Hs as (Hx & _ & Hs). constructor; [exact Hx | exact (IH _ Hs)].
Qed.

(** The ghost heap h with the name of each key in ks renamed to new's:
    what a setter makes of the names it changes. *)
Fixpoint rename (h : gmap piece pval) (ks : list Z) (new : Z -> ptr * list Z) : gmap piece pval :=
  match ks with
  | [] => h
  | k :: ks' => <[PName k := VName (new k).1 (new k).2]> (rename h ks' new)
  end.

(** A renamed key has its new name. *)
Lemma rename_lookup h ks new k :
  In k ks -> rename h ks new !! PName k = Some (VName (new k).1 (new k).2).
Proof.
  induction ks as [|k' ks IH]; intros Hk; [destruct Hk|]. cbn [rename].
  destruct (decide (k' = k)) as [->|Hne]; [apply lookup_insert_eq|].
  rewrite lookup_insert_ne; [|congruence]. apply IH. destruct Hk as [Hk|Hk]; [congruence | exact Hk].
Qed.

(** Renaming changes no piece of memory, so a memory that agrees with
    h agrees with it renamed. *)
Lemma rename_agrees m h ks new : agrees m h -> agrees m (rename h ks new).
Proof.
  intros Ha. induction ks as [|k ks IH]; [exact Ha|]. cbn [rename]. intros l v Hl.
  destruct (decide (l = PName k)) as [->|Hne].
  - rewrite lookup_insert_eq in Hl. injection Hl as <-. exact I.
  - rewrite lookup_insert_ne in Hl; [|congruence]. exact (IH l v Hl).
Qed.

(** Pieces that agree with every memory: ghost names and codecs. *)
Definition ghost_ps (ps : list (piece * pval)) : Prop :=
  Forall (fun lv => forall m, agree_piece m lv.1 lv.2) ps.

(** A key that ps does not write keeps its piece. *)
Lemma overwrite_out ps h l : l ∉ ps.*1 -> overwrite ps h !! l = h !! l.
Proof.
  induction ps as [|[l' v'] ps IH]; intros Hl; [reflexivity|]. cbn [overwrite fst snd].
  apply not_elem_of_cons in Hl as [Hne Hl]. rewrite lookup_insert_ne; [exact (IH Hl)|].
  intros E. apply Hne. symmetry. exact E.
Qed.

(** Overwriting with ghost pieces keeps a memory agreeing. *)
Lemma ghost_agrees m h ps : agrees m h -> ghost_ps ps -> agrees m (overwrite ps h).
Proof.
  intros Ha Hg l v Hl. destruct (lookup_overwrite _ _ _ _ Hl) as [Hin | [_ Hh]]; [|exact (Ha l v Hh)].
  unfold ghost_ps in Hg. rewrite List.Forall_forall in Hg.
  exact (Hg (l, v) (proj1 (list_elem_of_In _ _) Hin) m).
Qed.

(** The aux slots of the n bytes from offset o of the object b in the
    memory m'. *)
Definition slots_after (m' : mem) (b o : Z) (n : nat) : list cap :=
  (fun i => m_aux m' (b + (o + i))) <$> seqZ 0 (Z.of_nat n).

(** There are n of them. *)
Lemma length_slots_after m' b o n : length (slots_after m' b o n) = n.
Proof. unfold slots_after. rewrite length_fmap length_seqZ. lia. Qed.

(** A copy of the n bytes ys at s, which need not be the program's,
    into the block of the bytes xs and the slots cs at offset o of the
    live object b, both at multiples of 8: afterwards the destination's
    bytes are ys and its slots what the copy left there, and every
    piece outside it keeps its agreement. *)
Lemma lent_copy_after m m' b reg o xs cs s ys :
  live_disjoint m -> live_at m b reg -> b mod 8 = 0 -> o mod 8 = 0 ->
  length ys = length xs -> length cs = length xs ->
  all_agree m (byte_ps b o xs ++ aux_ps b o cs) ->
  (forall i y, ys !! i = Some y -> m_bytes m (ptr_addr s + Z.of_nat i) = y) ->
  copy_result m (mkPtr (b + o) (Obj b)) s (Z.of_nat (length xs)) m' ->
  all_agree m' (byte_ps b o ys ++ aux_ps b o (slots_after m' b o (length xs))) /\
  frame_ok (byte_ps b o xs ++ aux_ps b o cs).*1 m m'.
Proof.
  intros Hd Hl Hb8 Ho8 Hly Hlc Hdst Hys Hres.
  pose proof Hres as (Hfr & Hcb & _). pose proof Hfr as (Hr & _ & _).
  split; [|exact (block_frame _ _ _ _ _ _ _ Hd Hl Hb8 Ho8 Hlc Hdst Hfr)].
  pose proof Hdst as Hdst'. apply all_agree_app in Hdst' as [Hx _].
  destruct Hl as [E0 L0].
  assert (Hreg : registered m' b) by (unfold registered; rewrite Hr E0; discriminate).
  assert (Hbyte : forall i, (i < length xs)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
  { intros i Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
    destruct (byte_ps_agree _ _ _ _ _ _ _ (conj E0 L0) Hx Hxi) as (_ & H1 & H2). lia. }
  apply all_agree_app. split; apply all_agree_intro; intros l v Hin.
  - apply byte_ps_elem in Hin as (i & y & Hyi & -> & ->).
    assert (Hi : (i < length xs)%nat) by (rewrite <- Hly; exact (lookup_lt_Some _ _ _ Hyi)).
    destruct (Hbyte i Hi) as [H1 H2]. cbn [agree_piece]. split; [exact Hreg|].
    intros reg0 E L. rewrite Hr E0 in E. injection E as <-. split; [exact H1|]. split; [exact H2|].
    rewrite Hcb; [|unfold span_contains; cbn; lia]. cbn [ptr_addr].
    replace (ptr_addr s + (b + (o + Z.of_nat i) - (b + o))) with (ptr_addr s + Z.of_nat i) by lia.
    exact (Hys i y Hyi).
  - apply aux_ps_elem in Hin as (i & c & Hci & -> & ->). unfold slots_after in Hci.
    apply list_lookup_fmap_Some in Hci as (z & -> & Hz). apply lookup_seqZ in Hz as [-> Hi].
    destruct (Hbyte i ltac:(lia)) as [H1 H2]. cbn [agree_piece]. split; [exact Hreg|].
    intros reg0 E L. rewrite Hr E0 in E. injection E as <-. split; [exact H1|]. split; [exact H2|].
    left. reflexivity.
Qed.

(** ## Triples *)

(** The triples over any [[runtime]] R. *)
Module LentLogicOn (R : Runtime) (LG0 : LogicSig R).
Module ML := MemLogicOn R LG0.
Module SL := ML.SL.
Module LG := ML.LG.
Module L := LG.L.
Module SLen := StringLengths R.
Import L LG SL ML.

Section lent.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** [lent] k p t: the world lends the string t at p under the key k;
    p is not null, t ends before 2^64 and its bytes are not NUL, facts
    of the lent value that hold from when the world lends it. *)
Definition lent (k : Z) (p : ptr) (t : list Z) : iProp Σ :=
  ⌜0 < ptr_addr p /\ ptr_addr p + Z.of_nat (length t) < 2 ^ 64 /\ Forall (fun x => 0 < x < 256) t⌝ ∗ pointsto (PName k) DfracDiscarded (VName p t).

(** Lending is persistent. *)
Global Instance lent_persistent k p t : Persistent (lent k p t).
Proof. apply _. Qed.

(** [named] k p t: the name t at p of the key k, owned whole and not
    yet lent. A setter that changes k's name takes it ([wp_lend]). *)
Definition named (k : Z) (p : ptr) (t : list Z) : iProp Σ :=
  pointsto (PName k) (DfracOwn 1) (VName p t).

(** Owning the names of the keys ks, the ghost heap may rename them,
    to any new names, which it then owns. *)
Lemma rename_update h ks old new :
  gen_heap_interp h -∗ ([∗ list] k ∈ ks, named k (old k).1 (old k).2) ==∗
  gen_heap_interp (rename h ks new) ∗ [∗ list] k ∈ ks, named k (new k).1 (new k).2.
Proof.
  induction ks as [|k ks IH]; iIntros "Hh Hks"; [iModIntro; iFrame|].
  rewrite !big_sepL_cons. iDestruct "Hks" as "[Hk Hks]".
  iMod (IH with "Hh Hks") as "[Hh Hks]". iMod (gen_heap_update with "Hh Hk") as "[Hh Hk]".
  iModIntro. cbn [rename]. iFrame.
Qed.

Section calls.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The world interpretation keeps every lent string where [lent_at]
    says, in a memory whose live objects are apart, whose objects fit
    the address space and whose freed objects are empty, as a ready
    runtime's are. *)
Hypothesis wi_lent : forall m w h k p t,
  wi m w h -> live_disjoint m -> objects_fit (m_regions m) -> freed_empty (m_regions m) ->
  h !! PName k = Some (VName p t) -> lent_at m h p t.

(** The Iris instance of the registry and wi. *)
Local Instance lent_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation lexpr := (language.expr (nanofil_lang registry ge)).

(** In an interpreted state, a lent string is where [lent_at] says,
    against the state's ghost heap h, which h itself agrees with. *)
Lemma lent_facts σ k p t :
  heap_interp wi σ -∗ lent k p t -∗
  ∃ h, ⌜agrees (ls_mem σ) h /\ live_disjoint (ls_mem σ) /\ R.ready (ls_rt σ) (ls_mem σ) /\
       lent_at (ls_mem σ) h p t⌝.
Proof.
  iIntros "(%h & Hh & %Hf) [_ Hk]". destruct Hf as (Ha & Hd & Hr & Hw).
  iDestruct (gen_heap_valid with "Hh Hk") as %Hl. iExists h. iPureIntro.
  split; [exact Ha|]. split; [exact Hd|]. split; [exact Hr|].
  exact (wi_lent _ _ _ _ _ _ Hw Hd (R.address_space _ _ Hr) (R.freed_bounds _ _ Hr) Hl).
Qed.

(** A call of the external g, with contract spec, returning a pointer,
    whose invocation from any state lending t at p under k admits the
    arguments xs and returns p, changing nothing: setlocale's query of
    the category k is one. d is bound to p. *)
Lemma wp_lent_query f e ls lab d g args rest j spec xs k p t Φ :
  registry g = Some spec -> contract_returns spec = RClass P ->
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> name_eqb g free_name = false ->
  map_option (arg_x ge e) args = Some xs -> contract_abi spec (CResult d P) args ->
  (forall m w h, wi m w h -> h !! PName k = Some (VName p t) -> contract_pre spec xs m w) ->
  (forall s m w h trace ending s' m' w', wi m w h -> h !! PName k = Some (VName p t) ->
     M.E.invoke spec (CResult d P) args xs s m w trace ending s' m' w' ->
     s' = s /\ m' = m /\ w' = w /\ ending = CallReturn [WPtr p]) ->
  lent k p t -∗
  ▷ WP (ERun (mkFrame f (put d (WPtr p) e) ls None (Exec lab rest j)) : lexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d P) (Global g) args :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hret Hfn Hdata Hfree Hx Habi Hpre Hinv. iIntros "#Hk HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ spec xs (lent k p t) with "Hk [HK]");
    [done | done | done | done | done | done | |].
  - iIntros (σ) "(%h & Hh & %Hf) [_ Hk']". destruct Hf as (_ & _ & _ & Hw).
    iDestruct (gen_heap_valid with "Hh Hk'") as %Hl. iPureIntro. exact (Hpre _ _ _ Hw Hl).
  - iNext. iIntros (σ trace values s' m' w' Hi) "(%h & Hh & %Hf) [_ Hk']".
    pose proof Hf as (_ & _ & _ & Hw). iDestruct (gen_heap_valid with "Hh Hk'") as %Hl.
    destruct (Hinv _ _ _ _ _ _ _ _ _ Hw Hl Hi) as (-> & -> & -> & He). injection He as ->.
    iModIntro. iExists _. iSplit.
    + iPureIntro. unfold external_env. rewrite Hret. reflexivity.
    + destruct σ as [m s fuel w]. iSplitL "Hh"; [iExists h; iFrame "Hh"; iPureIntro; exact Hf|].
      iExact "HK".
Qed.

(** A setter's triple: a call of the external g, with contract spec,
    returning a pointer, that renames the keys ks. Owning their names
    ([named]), the ghost pieces gs, whose keys are none of the names,
    and Q, from which spec admits the arguments xs in any state, the
    call lends the new names for good and gives the ghost pieces new
    values gs'. Every invocation that returns, from an interpreted
    state with the ghost heap h, returns some q with new names and
    ghost pieces, related by Rq, and keeps h's memory agreeing, the
    live objects apart and the runtime ready, while wi holds of the
    renamed h with gs' written over it ([rename]). d is bound to q.
    setlocale(LC_ALL, "") is one, renaming every category and giving
    the codec piece the new codec. *)
Lemma wp_lend f e ls lab d g args rest j spec xs ks old gs
    (Rq : ptr -> (Z -> ptr * list Z) -> list (piece * pval) -> Prop) (Q : iProp Σ) Φ :
  registry g = Some spec -> contract_returns spec = RClass P ->
  find_fn ge g = None -> lookup g (ge_globals ge) = None -> name_eqb g free_name = false ->
  map_option (arg_x ge e) args = Some xs -> contract_abi spec (CResult d P) args ->
  Forall (fun k => PName k ∉ gs.*1) ks ->
  (forall σ, heap_interp wi σ -∗ Q -∗ ⌜contract_pre spec xs (ls_mem σ) (ls_world σ)⌝) ->
  (forall s m w h trace values s' m' w', wi m w h -> agrees m h -> live_disjoint m -> R.ready s m ->
     M.E.invoke spec (CResult d P) args xs s m w trace (CallReturn values) s' m' w' ->
     exists q new gs', values = [WPtr q] /\ Rq q new gs' /\ gs'.*1 = gs.*1 /\ ghost_ps gs' /\
       agrees m' h /\ live_disjoint m' /\ R.ready s' m' /\ wi m' w' (overwrite gs' (rename h ks new))) ->
  ([∗ list] k ∈ ks, named k (old k).1 (old k).2) -∗ pts gs -∗ Q -∗
  ▷ (∀ q new gs', ⌜Rq q new gs'⌝ -∗ Q -∗ pts gs' -∗ ([∗ list] k ∈ ks, lent k (new k).1 (new k).2) -∗
     WP (ERun (mkFrame f (put d (WPtr q) e) ls None (Exec lab rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d P) (Global g) args :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hret Hfn Hdata Hfree Hx Habi Hgs Hpre Hpost. iIntros "Hks Hgs HQ HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ spec xs
            (Q ∗ ([∗ list] k ∈ ks, named k (old k).1 (old k).2) ∗ pts gs)%I with "[$HQ $Hks $Hgs] [HK]");
    [done | done | done | done | done | done | |].
  - iIntros (σ) "Hσ [HQ _]". iApply (Hpre with "Hσ HQ").
  - iNext. iIntros (σ trace values s' m' w' Hi) "(%h & Hh & %Hf) (HQ & Hks & Hgs)".
    destruct Hf as (Ha & Hd & Hr & Hw).
    destruct (Hpost _ _ _ _ _ _ _ _ _ Hw Ha Hd Hr Hi)
      as (q & new & gs' & -> & Hq & Hkeys & Hghost & Ha' & Hd' & Hr' & Hw').
    iMod (rename_update _ _ _ new with "Hh Hks") as "[Hh Hks]".
    iMod (pts_update _ _ gs' Hkeys with "Hh Hgs") as "[Hh Hgs]".
    iAssert (|==> [∗ list] k ∈ ks, lent k (new k).1 (new k).2)%I with "[Hks]" as ">Hl".
    { iApply big_sepL_bupd. iApply (big_sepL_impl with "Hks"). iIntros "!>" (i k Hik) "Hk".
      iMod (pointsto_persist with "Hk") as "Hk". iModIntro. iFrame "Hk". iPureIntro.
      assert (Hin : In k ks) by (apply list_elem_of_In; exact (list_elem_of_lookup_2 _ _ _ Hik)).
      assert (Hk : overwrite gs' (rename h ks new) !! PName k = Some (VName (new k).1 (new k).2)).
      { rewrite overwrite_out; [exact (rename_lookup h ks new k Hin)|]. rewrite Hkeys.
        rewrite List.Forall_forall in Hgs. exact (Hgs k Hin). }
      destruct (wi_lent _ _ _ _ _ _ Hw' Hd' (R.address_space _ _ Hr') (R.freed_bounds _ _ Hr') Hk)
        as ([_ Hs] & H0 & Hlen & _).
      split; [exact H0|]. split; [exact Hlen | exact (string_at_nonzero _ _ _ Hs)]. }
    iModIntro. iExists _. iSplit.
    + iPureIntro. unfold external_env. rewrite Hret. reflexivity.
    + iSplitL "Hh".
      * iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world].
        split; [exact (ghost_agrees _ _ _ (rename_agrees _ _ _ _ Ha') Hghost)|]. auto.
      * iApply ("HK" with "[%] HQ Hgs Hl"). exact Hq.
Qed.

(** strlen's triple, from [strlen_contract], for the string t lent at
    p: d is bound to t's length. *)
Lemma wp_strlen_lent f e ls lab d v rest j k p t Φ :
  registry (TAtom "strlen") = Some (strlen_contract world) ->
  find_fn ge (TAtom "strlen") = None -> lookup (TAtom "strlen") (ge_globals ge) = None ->
  arg_x ge e (Arg P v) = Some (WPtr p) ->
  lent k p t -∗
  ▷ WP (ERun (mkFrame f (put d (WInt (Z.of_nat (length t))) e) ls None (Exec lab rest j)) : lexpr)
      {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d L) (Global (TAtom "strlen")) [Arg P v] :: rest) j)) : lexpr)
    {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hv. iIntros "#Hk HK".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (strlen_contract world) [WPtr p] (lent k p t)
            with "Hk [HK]"); [done | done | done | done | cbn [map_option]; rewrite Hv; done | | |].
  - split; [right; eexists; reflexivity | eexists; reflexivity].
  - iIntros (σ) "Hσ Hk'". iDestruct (lent_facts with "Hσ Hk'") as %(h & _ & _ & Hr & Hs & _).
    iPureIntro. exists p, (Z.of_nat (length t)). split; [reflexivity|].
    exact (SLen.c_string_length _ _ _ _ Hr Hs).
  - iNext. iIntros (σ trace values s' m' w' Hinv) "Hσ Hk'".
    iDestruct (lent_facts with "Hσ Hk'") as %(h & _ & _ & Hr & Hs & _).
    pose proof (SLen.c_string_length _ _ _ _ Hr Hs) as Ht.
    destruct (M.E.strlen_invocation _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & -> & p' & n & Hx & Hn & He). injection Hx as <-. injection He as ->.
    rewrite (terminated_length_unique _ _ _ _ Hn Ht).
    iDestruct (pure_return with "Hσ") as "Hσ"; [exact Hinv|]. destruct σ as [m s fuel w]. iModIntro.
    iExists _. iSplit.
    + iPureIntro. cbn. rewrite Z.mod_small; [reflexivity|]. destruct Ht as [_ ?]. lia.
    + iFrame "Hσ". iExact "HK".
Qed.

(** memcpy's triple, from [memcpy_contract], of the first n bytes of
    the string t lent at p with its NUL, n at most t's length plus one,
    into the block of the n bytes xs and the slots cs at the 8-aligned
    offset o of the owned live object b, at a multiple of 8, where the
    copy keeps the world interpretation: the block's bytes are then
    that prefix, its slots what the copy left there, and d is bound to
    the block's pointer. *)
Lemma wp_memcpy_lent f e ls lab d vd vs vn rest j b reg o xs cs k p t Φ :
  registry (TAtom "memcpy") = Some (memcpy_contract world) ->
  find_fn ge (TAtom "memcpy") = None -> lookup (TAtom "memcpy") (ge_globals ge) = None ->
  arg_x ge e (Arg P vd) = Some (WPtr (mkPtr (b + o) (Obj b))) ->
  arg_x ge e (Arg P vs) = Some (WPtr p) ->
  arg_x ge e (Arg L vn) = Some (WInt (Z.of_nat (length xs))) ->
  (length xs <= S (length t))%nat -> length cs = length xs ->
  b mod 8 = 0 -> o mod 8 = 0 -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg ->
  (forall m m' wd h, copy_result m (mkPtr (b + o) (Obj b)) p (Z.of_nat (length xs)) m' ->
     (forall l v, (l, v) ∈ block_ps b reg o xs cs -> h !! l = Some v) -> wi m wd h ->
     wi m' wd (overwrite (block_ps b reg o (take (length xs) (t ++ [0]))
                            (slots_after m' b o (length xs))) h)) ->
  lent k p t -∗ live b reg -∗ bytes b o xs -∗ auxes b o cs -∗
  ▷ (∀ cs', ⌜length cs' = length xs⌝ -∗
     live b reg -∗ bytes b o (take (length xs) (t ++ [0])) -∗ auxes b o cs' -∗
     WP (ERun (mkFrame f (put d (WPtr (mkPtr (b + o) (Obj b))) e) ls None (Exec lab rest j)) : lexpr)
       {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
             (Exec lab (Call (CResult d P) (Global (TAtom "memcpy")) [Arg P vd; Arg P vs; Arg L vn] :: rest) j))
        : lexpr) {{ Φ }}.
Proof.
  intros Hreg Hfn Hdata Hpd Hps Hn Hlt Hlc Hb8 Ho8 Ho Hend Hwi.
  iIntros "#Hk Hl Hx Hcs HK".
  set (n := length xs). set (ys := take n (t ++ [0])).
  assert (Hly : length ys = n) by (unfold ys; rewrite length_take length_app; cbn; lia).
  (* The prefix ys is in memory wherever t is a C string there. *)
  assert (Hys : forall m, c_string m p t ->
            forall i y, ys !! i = Some y -> m_bytes m (ptr_addr p + Z.of_nat i) = y).
  { intros m [_ Hs] i y Hy. pose proof (string_at_length _ _ _ Hs) as [_ Hnul].
    unfold ys in Hy. apply lookup_take_Some in Hy as [Hy _].
    destruct (decide (i < length t)%nat) as [Hi|Hi].
    - rewrite lookup_app_l in Hy; [|exact Hi]. exact (string_at_lookup _ _ _ _ _ Hs Hy).
    - rewrite lookup_app_r in Hy; [|lia]. apply list_lookup_singleton_Some in Hy as [Hi' <-].
      replace (Z.of_nat i) with (Z.of_nat (length t)) by lia. exact Hnul. }
  iDestruct (block_pts b reg o xs cs with "[$Hl $Hx $Hcs]") as "Hdst".
  iApply (wp_external _ _ _ _ _ _ _ _ _ _ _ _ (memcpy_contract world)
            [WPtr (mkPtr (b + o) (Obj b)); WPtr p; WInt (Z.of_nat n)]
            (pts (block_ps b reg o xs cs) ∗ lent k p t) with "[$Hdst $Hk] [HK]");
    [done | done | done | done | cbn [map_option]; rewrite Hpd Hps Hn; done | | |].
  - split; [right; eexists; reflexivity | exists vd, vs, vn; reflexivity].
  - iIntros (σ) "Hσ [Hdst Hk']". iDestruct (pts_facts with "Hσ Hdst") as %(Ha & Hd & Hfit).
    iDestruct "Hσ" as (h) "[Hh %Hf]". iDestruct (pts_lookup with "Hh Hdst") as %Hlk.
    iDestruct "Hk'" as "[_ Hk']". iDestruct (gen_heap_valid with "Hh Hk'") as %Hlent. iPureIntro.
    destruct Hf as (_ & _ & Hr & Hw).
    destruct (wi_lent _ _ _ _ _ _ Hw Hd (R.address_space _ _ Hr) (R.freed_bounds _ _ Hr) Hlent)
      as (Hs & _ & _ & Hal & Hapart).
    destruct Ha as [[E L] _]. cbn [fst snd] in E, L.
    destruct (Hfit b reg E) as [Hb0 Hfit'].
    assert (Hown : forall a, b <= a < r_end reg -> owned_live h (ls_mem σ) a).
    { intros a Ha. exists (PLive b), (VLive reg), reg. split; [apply Hlk; left|]. split; [exact I|].
      split; [split; [exact E | exact L]|exact Ha]. }
    eexists _, _, _. split; [reflexivity|]. split; [|split; [|split]].
    + split; [lia|]. split; [lia|]. split.
      * unfold writable_span. cbn [span_ptr span_size ptr_addr ptr_cap].
        split; [lia|]. exists b, reg. split; [reflexivity|]. split; [exact E|]. split; [exact L|].
        apply (access_obj _ _ reg); [exact E | lia | lia | apply Z.mod_1_r].
      * right. exists b. auto.
    + apply (readable_bytes_prefix _ _ (Z.of_nat (length t) + 1)); [|lia].
      exact (terminated_length_readable _ _ _ (SLen.c_string_length _ _ _ _ Hr Hs)).
    + destruct Hal as (b' & Hc & Hb'). right. exists b'. auto.
    + right. right. cbn [ptr_addr].
      destruct (Z.le_gt_cases (b + o + Z.of_nat n) (ptr_addr p)) as [H|H]; [left; exact H|].
      destruct (Z.le_gt_cases (ptr_addr p + Z.of_nat n) (b + o)) as [H'|H']; [right; exact H'|].
      exfalso. apply (Hapart (Z.max (ptr_addr p) (b + o))); [lia|]. apply Hown. lia.
  - iNext. iIntros (σ trace values s' m' w' Hinv) "(%h & Hh & %Hf) [Hdst [_ Hk']]".
    destruct Hf as (Ha & Hd & Hr & Hw).
    iDestruct (gen_heap_valid with "Hh Hk'") as %Hlent.
    destruct (wi_lent _ _ _ _ _ _ Hw Hd (R.address_space _ _ Hr) (R.freed_bounds _ _ Hr) Hlent) as (Hs & _).
    destruct (M.E.copy_invocation _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv)
      as (_ & -> & d' & s0 & n' & Hx & _ & Hres & He).
    injection Hx as <- <- <-. injection He as ->.
    iDestruct (pts_lookup with "Hh Hdst") as %Hlk.
    assert (Hold : all_agree (ls_mem σ) (block_ps b reg o xs cs)).
    { apply all_agree_intro. intros l v Hin. exact (Ha l v (Hlk l v Hin)). }
    destruct Hold as [Hlv Hold]. cbn [agree_piece fst snd] in Hlv.
    destruct (lent_copy_after (ls_mem σ) m' b reg o xs cs p ys Hd Hlv Hb8 Ho8 Hly Hlc Hold (Hys _ Hs) Hres)
      as [Hnew Hfr].
    destruct (M.E.invoke_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ Hinv) as (born & Hpre).
    destruct (M.E.prefix_preserve _ _ _ _ _ _ _ _ _ _ _ Hpre Hr) as [Hr' _].
    pose proof Hres as ((Hregs & _) & _).
    assert (Hk : (block_ps b reg o ys (slots_after m' b o n)).*1 = (block_ps b reg o xs cs).*1).
    { apply block_ps_keys; [exact Hly | rewrite length_slots_after; lia]. }
    iMod (pts_update _ _ (block_ps b reg o ys (slots_after m' b o n)) with "Hh Hdst") as "[Hh Hdst]";
      [exact Hk|].
    iModIntro. iExists _. iSplit; [iPureIntro; reflexivity|].
    iSplitL "Hh".
    + iExists _. iFrame "Hh". iPureIntro. cbn [ls_mem ls_rt ls_world]. split; [|split; [|split]].
      * intros l v Hl'. destruct (lookup_overwrite _ _ _ _ Hl') as [Hin | [Hnk Hh]].
        -- apply elem_of_cons in Hin as [Hin|Hin].
           ++ injection Hin as -> ->. cbn [agree_piece]. exact (live_at_regions _ _ _ _ Hregs Hlv).
           ++ exact (all_agree_elem _ _ _ _ Hnew Hin).
        -- apply Hfr; [|exact (Ha l v Hh)]. intros Hk'. apply Hnk. rewrite Hk.
           cbn [fmap list_fmap fst block_ps]. right. exact Hk'.
      * exact (live_disjoint_regions _ _ Hregs Hd).
      * exact Hr'.
      * exact (Hwi _ _ _ _ Hres Hlk Hw).
    + rewrite !block_pts. iDestruct "Hdst" as "(Hl & Hx & Hcs)".
      iApply ("HK" $! (slots_after m' b o n) with "[%] Hl Hx Hcs"). apply length_slots_after.
Qed.

End calls.
End lent.
End LentLogicOn.

(** [LentLogicOn] over a Logic instance of its own. *)
Module LentLogic (R : Runtime).
Module LG0 := Logic R.
Include LentLogicOn R LG0.
End LentLogic.
