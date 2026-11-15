(** A proof about startup needs to know that the memory the loader builds
    for the linked program holds certain strings and tables. That memory
    is too large to compute, but the memory of the erased module is
    small enough, and HelloImageEraseMem.v shows that the two agree on
    every kept object. This file turns a computed check of pieces on the
    erased memory into agreement of the same pieces with the genuine
    memory. The check also confirms that each piece lies inside the
    region of a kept object, so the agreement theorem covers it.

    Nothing here says that a program starts from this memory or that any
    other part of it is owned. *)

From stdpp Require Import list.
From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Run Pieces Heap.
From Glibc Require Import HelloImageErase HelloImageEraseMem.
Import ListNotations.
Open Scope Z_scope.

(** ## Which pieces the agreement covers *)

(** These are the intervals of the kept data objects in ks: each runs
    from the object's final symbol to the end of its rounded region. The
    list ks holds items of the module, usually just its kept objects, and
    the check computes the intervals once rather than for every piece. *)
Definition kept_intervals (keep : name -> bool) (ks : module) (g : list (name * ptr)) : list (Z * Z) :=
  flat_map (fun it => match it with
    | IData n _ _ its => if keep n then match lookup n g with
        | Some q => [(ptr_addr q, ptr_addr q + rounded its)] | None => [] end else []
    | _ => [] end) ks.

(** A piece is covered when its object's registered region is one of the
    intervals. Ghost keys hold no memory and need nothing. *)
Definition piece_covered (iv : list (Z * Z)) (rs : list region) (l : piece) : bool :=
  match l with
  | PName _ => true
  | PLive b | PByte b _ | PAux b _ =>
      match object_region b rs with
      | Some r => existsb (fun be => (fst be =? b) && (snd be =? r_end r)) iv
      | None => false
      end
  end.

(** The computed check holds when every piece agrees with a memory and
    is covered. *)
Definition pieces_ok keep ks g (m : mem) (ps : list (piece * pval)) : bool :=
  let iv := kept_intervals keep ks g in
  forallb (fun lv => bool_decide (checked_piece m lv.1 lv.2) && piece_covered iv (m_regions m) lv.1) ps.

(** These are the kept data objects of a module, in order. *)
Definition kept_objects (keep : name -> bool) (md : module) : module :=
  filter (fun it => match it with IData n _ _ _ => keep n | _ => false end) md.

Lemma kept_objects_incl keep md : incl (kept_objects keep md) md.
Proof. apply incl_filter. Qed.

(** Every address in one of the intervals belongs to a kept object. *)
Lemma interval_kept keep ks md g b e : incl ks md ->
  existsb (fun be => (fst be =? b) && (snd be =? e)) (kept_intervals keep ks g) = true ->
  forall x, b <= x < e -> kept_at keep md g x.
Proof.
  intros Hks H x Hx. apply existsb_exists in H as ([b' e'] & Hin & H). cbn [fst snd] in H.
  apply andb_true_iff in H as [Hb He]. apply Z.eqb_eq in Hb, He. subst b' e'.
  unfold kept_intervals in Hin. apply in_flat_map in Hin as (it & Hit & Hin).
  destruct it as [f|o t|n lk al its|n lk t]; try destruct Hin.
  destruct (keep n) eqn:Hk; [|destruct Hin]. destruct (lookup n g) as [q|] eqn:Hq; [|destruct Hin].
  destruct Hin as [E|[]]. injection E as Eb Ee.
  exists (IData n lk al its). split; [exact (Hks _ Hit)|]. exists n, lk, al, its, q. split_and!; auto; lia.
Qed.

(** ## Moving a checked piece to the genuine memory *)

(** A proof that reads a constant needs it in the real memory, which
    cannot be computed. This lemma moves one checked piece across: the
    two memories have the same regions and match on every kept byte and
    capability slot. *)
Lemma checked_transfer keep ks md g m m' l v : incl ks md ->
  m_regions m' = m_regions m ->
  (forall x, kept_at keep md g x -> m_bytes m' x = m_bytes m x /\ m_aux m' x = m_aux m x) ->
  piece_covered (kept_intervals keep ks g) (m_regions m') l = true -> checked_piece m' l v -> checked_piece m l v.
Proof.
  intros Hks R K. destruct l as [b|b o|b o|k]; cbn [piece_covered]; intros C; destruct v; cbn [checked_piece]; try tauto.
  - unfold live_at. rewrite <- R. tauto.
  - rewrite <- R. destruct (object_region b (m_regions m')) as [r|]; [|tauto].
    intros H Hl. destruct (H Hl) as (Ho & He & Hv).
    assert (Hx : b <= b + o < r_end r) by lia. destruct (K _ (interval_kept _ _ _ _ _ _ Hks C _ Hx)) as [B _].
    split_and!; [exact Ho | exact He | congruence].
  - rewrite <- R. destruct (object_region b (m_regions m')) as [r|]; [|tauto].
    intros H Hl. destruct (H Hl) as (Ho & He & Hv).
    assert (Hx : b <= b + o < r_end r) by lia. destruct (K _ (interval_kept _ _ _ _ _ _ Hks C _ Hx)) as [_ A].
    split_and!; [exact Ho | exact He | congruence].
Qed.

(** The check on the erased memory gives agreement with the genuine one. *)
Theorem image_pieces keep ks md g m ps : incl ks md ->
  initial_memory md = Some (g, m) -> NoDup (map item_key md) -> zero_nonneg md = true ->
  exists m', initial_memory (erase keep md) = Some (g, m') /\ m_regions m' = m_regions m /\
    (pieces_ok keep ks g m' ps = true -> all_agree m ps).
Proof.
  intros Hks Hi Hd Hz. destruct (erase_memory keep md g m Hi Hd Hz) as (m' & E & R & B & A).
  exists m'. split; [exact E|]. split; [exact R|]. intros H. apply checked_pieces_all_agree.
  unfold pieces_ok in H. cbv zeta in H. rewrite forallb_forall in H |- *. intros lv Hlv.
  pose proof (H lv Hlv) as Hlv'. apply andb_true_iff in Hlv' as [Hc Hv]. apply bool_decide_eq_true_2.
  apply bool_decide_eq_true_1 in Hc. apply (checked_transfer keep ks md g m m' lv.1 lv.2 Hks R); auto.
Qed.

(** ## Controls

    A check that accepted everything would prove nothing, so it runs on
    a small program with two objects and must both pass and fail there.
    The program keeps one object whole and blanks the other. The check
    accepts the kept object, and the real memory then holds it. It
    refuses a byte of the blanked object. *)

Local Definition tx (s : string) : name := TAtom s.

Local Definition md : module :=
  [IData (tx "x") LExport 8 [Item Wl 5];
   IData (tx "k") (LRo (tx "local")) 1 [Sym (tx "x") 0; Str [67]]].

Local Definition keep_k (n : name) : bool := name_eqb n (tx "k").

Local Definition k_ps : list (piece * pval) :=
  [(PLive 65568, VLive (mkRegion 65568 65584 GlobalData Live)); (PAux 65568 0, VAux (Obj 65536));
   (PByte 65568 8, VByte 67); (PByte 65568 15, VByte 0)].

Local Definition check (ps : list (piece * pval)) : bool :=
  match initial_memory (erase keep_k md) with Some (g, m') => pieces_ok keep_k md g m' ps | None => false end.

Lemma k_pieces : exists g m, initial_memory md = Some (g, m) /\ all_agree m k_ps.
Proof.
  assert (Hs : option_map fst (initial_memory md) <> None) by (vm_compute; discriminate).
  destruct (initial_memory md) as [[g m]|] eqn:E; [|contradiction].
  assert (Hd : NoDup (map item_key md)) by (apply names_distinct_sound; vm_compute; reflexivity).
  destruct (image_pieces keep_k md md g m k_ps (incl_refl md) E Hd ltac:(vm_compute; reflexivity)) as (m' & E' & _ & P).
  exists g, m. split; [reflexivity|]. apply P.
  assert (C : check k_ps = true) by (vm_compute; reflexivity). unfold check in C. rewrite E' in C. exact C.
Qed.

(** The erased memory holds zero at x, which the genuine memory does not,
    and the check refuses that piece. *)
Lemma x_piece_refused : check [(PByte 65536 0, VByte 0)] = false.
Proof. vm_compute. reflexivity. Qed.
