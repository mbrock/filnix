(** The gettext diagnostic route reads fifteen constants: getopt's nine
    messages, dcigettext's "/" and ".mo", the locale category table with
    its index and the name "C", and libc's text domain "libc". Earlier
    files build the route's read-only strings from supplied pieces of
    these constants. This file shows that the memory the loader builds
    for the whole linked Hello image holds those pieces, at the addresses
    that its symbols give, with distinct keys.

    The real memory is too large to compute. A copy of the image that
    blanks every other object is small enough, and HelloImageEraseMem.v
    shows that the copy's memory matches the real one on the fifteen
    objects. Only this file names them; the generated image does not.

    This file does not show that Hello starts from this memory, that the
    route's proofs run this image, or who owns the rest of memory. *)

From stdpp Require Import list.
From Stdlib Require Import String ZArith Bool Lia.
From Nanofil Require Import Term Syntax Values Memory Run Pieces Heap.
From Glibc Require Import WordString HelloGetoptTable HelloGetoptDiagMsgs HelloGettextSuffix
  HelloGettextLocaleConst HelloGettextDomain.
From Glibc Require Import HelloImageErase HelloImageEraseMem HelloImagePieces HelloImageCode HelloImageLoad.
Import ListNotations.
Open Scope Z_scope.

(** ## The fifteen constants *)

(** The route reads these objects and nothing else from the image here. *)
Definition hello_keep_names : list string :=
  dgx_msg_names ++ dci_suffix_names ++
  ["_nl_category_names"; "_nl_category_name_idxs"; "_nl_C_name"; "__GI__libc_intl_domainname"]%string.

Definition hello_keep (n : name) : bool := existsb (name_eqb n) (map TAtom hello_keep_names).

(** These are the objects of the nine messages in the linked image. *)
Definition hello_msg_bases : list (Z * region) :=
  [(173888, gd 173888 173920); (173936, gd 173936 173984); (174000, gd 174000 174008);
   (174032, gd 174032 174040); (174064, gd 174064 174096); (174112, gd 174112 174160);
   (174176, gd 174176 174216); (174336, gd 174336 174368); (174384, gd 174384 174432)].

(** These are the objects of "/" and ".mo". *)
Definition hello_suffix_bases : list (Z * region) := [(85456, gd 85456 85464); (85488, gd 85488 85496)].

(** This is the object of the domain "libc". *)
Definition hello_domain_base : Z * region := (164688, gd 164688 164696).

(** These are the pieces of the fifteen constants: the locale table, its
    index and "C", then the eleven strings. *)
Definition hello_kept_ps : list (piece * pval) :=
  lc_ps 168736 (gd 168736 168880) 168672 (gd 168672 168688) 164624 (gd 164624 164632) ++
  dgx_msg_ps hello_msg_bases ++ dci_suffix_ps hello_suffix_bases ++
  libc_domain_ps hello_domain_base.1 hello_domain_base.2.

(** No constant holds a capability. These pieces say so for every word
    slot of every object, padding included. *)
Definition aux_none_ps (br : Z * region) : list (piece * pval) :=
  map (fun k => (PAux br.1 (8 * Z.of_nat k), VAux CNone)) (seq 0 (Z.to_nat ((r_end br.2 - br.1) / 8))).

Definition hello_aux_ps : list (piece * pval) :=
  List.concat (map aux_none_ps ([(168736, gd 168736 168880); (168672, gd 168672 168688);
    (164624, gd 164624 164632); hello_domain_base] ++ hello_msg_bases ++ hello_suffix_bases)).

(** ## Placement *)

(** A symbol names the read-only object at b. *)
Definition lookup_ro (g : list (name * ptr)) (n : string) (b : Z) : bool :=
  match Term.lookup (TAtom n) g with
  | Some p => (ptr_addr p =? b) && match ptr_cap p with Ro c => c =? b | _ => false end
  | None => false
  end.

Lemma lookup_ro_ok g n b : lookup_ro g n b = true -> Term.lookup (TAtom n) g = Some (mkPtr b (Ro b)).
Proof.
  unfold lookup_ro. destruct (Term.lookup (TAtom n) g) as [[a c]|]; [|discriminate]. cbn [ptr_addr ptr_cap].
  destruct c; try (rewrite andb_false_r; discriminate). intros H. apply andb_true_iff in H as [Ha Hc].
  apply Z.eqb_eq in Ha, Hc. subst. reflexivity.
Qed.

Lemma places_ok g (ns : list string) (bs : list (Z * region)) : List.length ns = List.length bs ->
  forallb (fun nb : string * (Z * region) => lookup_ro g nb.1 nb.2.1) (combine ns bs) = true ->
  Forall2 (fun n br => Term.lookup (TAtom n) g = Some (mkPtr br.1 (Ro br.1))) ns bs.
Proof.
  revert bs. induction ns as [|n ns IH]; intros [|br bs] Hl H; try discriminate Hl; [constructor|].
  cbn in H. apply andb_true_iff in H as [H1 H2]. constructor; [exact (lookup_ro_ok _ _ _ H1) | apply IH; auto].
Qed.

(** The symbols of the image place all fifteen constants. *)
Definition hello_places (g : list (name * ptr)) : bool :=
  forallb (fun nb : string * (Z * region) => lookup_ro g nb.1 nb.2.1) (combine dgx_msg_names hello_msg_bases) &&
  forallb (fun nb : string * (Z * region) => lookup_ro g nb.1 nb.2.1) (combine dci_suffix_names hello_suffix_bases) &&
  lookup_ro g "_nl_category_names" 168736 && lookup_ro g "_nl_category_name_idxs" 168672 &&
  lookup_ro g "_nl_C_name" 164624 && lookup_ro g "__GI__libc_intl_domainname" hello_domain_base.1.

(** ## The check on the erased image *)

(** The erased image keeps the fifteen objects whole. *)
Definition hello_skel : module := Eval vm_compute in erase hello_keep hello_image_module.

Lemma hello_skel_eq : erase hello_keep hello_image_module = hello_skel.
Proof. vm_compute. reflexivity. Qed.

(** These are the kept objects, so the check need not walk the image. *)
Definition hello_kept : module := Eval vm_compute in kept_objects hello_keep hello_image_module.

Lemma hello_kept_incl : incl hello_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_keep hello_image_module = hello_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

(** The loader runs once, here, on the erased image. Its memory holds
    every piece inside a kept object, and its symbols place the fifteen
    constants. *)
Lemma hello_skel_check :
  match initial_memory hello_skel with
  | Some (g, m') => pieces_ok hello_keep hello_kept g m' (hello_kept_ps ++ hello_aux_ps) && hello_places g
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** ## The constants in the genuine memory *)

(** Each string and table fits its object. *)
Lemma hello_kept_fit :
  Forall2 lit_fit hello_msg_bases dgx_msg_texts /\ Forall2 lit_fit hello_suffix_bases dci_suffix_texts /\
  lc_fit 168736 (gd 168736 168880) 168672 (gd 168672 168688) 164624 (gd 164624 164632) /\
  lit_fit hello_domain_base libc_domain_text.
Proof.
  split_and!.
  - repeat (apply List.Forall2_cons; [unfold lit_fit; vm_compute; split_and!; first [reflexivity | discriminate]|]).
    apply List.Forall2_nil.
  - repeat (apply List.Forall2_cons; [unfold lit_fit; vm_compute; split_and!; first [reflexivity | discriminate]|]).
    apply List.Forall2_nil.
  - unfold lc_fit, lit_fit. vm_compute. split_and!; first [reflexivity | discriminate].
  - unfold lit_fit. vm_compute. split_and!; first [reflexivity | discriminate].
Qed.

(** The keys of the fifteen constants are distinct. The table, its index
    and "C" have keys at their own three bases, and the eleven strings at
    eleven other bases. *)
Lemma hello_kept_keys : NoDup hello_kept_ps.*1.
Proof.
  set (bs := hello_msg_bases ++ hello_suffix_bases ++ [hello_domain_base]).
  assert (Hl : hello_kept_ps = lc_ps 168736 (gd 168736 168880) 168672 (gd 168672 168688) 164624 (gd 164624 164632) ++
    lits_ps bs (dgx_msg_texts ++ dci_suffix_texts ++ [libc_domain_text])).
  { unfold hello_kept_ps, dgx_msg_ps, dci_suffix_ps, libc_domain_ps, lits_ps, bs.
    rewrite !zip_with_app by reflexivity. rewrite !List.concat_app. cbn [zip_with List.concat]. rewrite app_nil_r. reflexivity. }
  rewrite Hl. apply lits_ps_sep.
  - apply lc_ps_nodup. apply (bool_decide_unpack _). vm_compute. exact I.
  - apply (bool_decide_unpack _). vm_compute. exact I.
  - intros k Hk. apply lc_ps_ids in Hk.
    assert (Hd : Forall (fun z => z ∉ bs.*1) [168736; 168672; 164624]) by (apply (bool_decide_unpack _); vm_compute; exact I).
    rewrite Forall_forall in Hd. exact (Hd _ Hk).
Qed.

(** The loader succeeds on the linked image. Its symbols place the
    fifteen constants at the objects above, its memory holds their pieces
    with distinct keys, and no word slot of those objects holds a
    capability. HelloImageKeptRefused.v shows that the check refuses
    changed, moved, short and uncovered pieces. *)
Theorem hello_image_kept : exists g m, initial_memory hello_image_module = Some (g, m) /\
  dgx_msg_at g hello_msg_bases /\ dci_suffix_at g hello_suffix_bases /\
  lc_at g 168736 168672 164624 /\ libc_domain_at g hello_domain_base.1 /\
  all_agree m hello_kept_ps /\ all_agree m hello_aux_ps /\ NoDup hello_kept_ps.*1.
Proof.
  destruct hello_image_memory as (g & m & E).
  destruct (image_pieces hello_keep hello_kept hello_image_module g m (hello_kept_ps ++ hello_aux_ps)
    hello_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_skel_check as C. rewrite <- hello_skel_eq, E' in C.
  apply andb_true_iff in C as [Cp Cg]. apply P, all_agree_app in Cp as [Ak Aa].
  unfold hello_places in Cg. apply andb_true_iff in Cg as [Cg Cd]. apply andb_true_iff in Cg as [Cg Cc].
  apply andb_true_iff in Cg as [Cg Ci]. apply andb_true_iff in Cg as [Cg Cn]. apply andb_true_iff in Cg as [Cm Cs].
  exists g, m. split_and!; auto.
  - apply places_ok; [reflexivity | exact Cm].
  - apply places_ok; [reflexivity | exact Cs].
  - split_and!; apply lookup_ro_ok; assumption.
  - apply lookup_ro_ok. exact Cd.
  - exact hello_kept_keys.
Qed.
