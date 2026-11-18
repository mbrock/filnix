(** Hello's wide stdout converts its wide characters to bytes through
    the C locale's ASCII step. A character above 127 goes to glibc's
    transliteration, which searches the C locale's built-in tables for
    a replacement and falls back to a question mark. The proof of that
    conversion reads those tables, so this module lists what Hello's
    image holds in them and checks the list against the loader.

    The tables hold about 50,000 bytes. Checking them byte by byte in a
    blanked copy of the image, as the smaller lists of constants are
    checked, would take minutes, because reading one byte of the copy
    walks every byte the copy wrote. This module instead proves once
    that the loader leaves a string object's bytes where it wrote them,
    and computes only the facts about the strings themselves. *)

From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Run Runtime Pieces Heap StringLogic.
From Glibc Require Import StartImageEarly HelloImageErase HelloImageEraseMem HelloImagePieces HelloImageModule HelloImageLoad.
Import ListNotations.
Open Scope Z_scope.

(** ## A string object keeps its bytes

    The loader writes a string initializer one byte at a time. Each
    later item writes only inside its own object, so the string object
    still holds its characters when the loader finishes. The lemmas
    below prove this for any module whose names are distinct. They
    compare the module with the copy that
    [HelloImageEraseMem](HelloImageEraseMem.v) blanks. *)

(** Writing a string at offset i of address a leaves character j at
    address a + i + j, reduced to a byte. *)
Lemma sfold_bytes a cs : forall m i (j : nat), (j < length cs)%nat ->
  m_bytes (fst (fold_left (sfold a) cs (m, i))) (a + i + Z.of_nat j) = nth j cs 0 mod 256.
Proof.
  induction cs as [|c cs IH]; intros m i j Hj; cbn [length] in Hj; [lia|]. cbn [fold_left].
  destruct j as [|j].
  - destruct (str_fold a cs (store_bytes m (a + i) 1 c) (i + 1)) as (_ & _ & B). rewrite B by lia.
    unfold store_bytes. cbn [m_bytes]. rewrite Z.add_0_r, Z.leb_refl, (proj2 (Z.ltb_lt _ _)) by lia. cbn.
    unfold byte_of. rewrite Z.sub_diag, Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  - cbn [nth]. replace (a + i + Z.of_nat (S j)) with (a + (i + 1) + Z.of_nat j) by lia. apply IH. lia.
Qed.

(** An erased item that the erasure does not keep writes nothing. *)
Lemma contents_erased_same keep g m m' it : keep (item_key it) = false ->
  contents g (Some m) (erase_item keep it) = Some m' -> m' = m.
Proof.
  destruct it as [f|o t|n lk al its|n lk t]; cbn [item_key erase_item contents]; intros Hk H;
    try (injection H as <-; reflexivity).
  rewrite Hk in H. destruct its as [|d ds]; cbn [erase_items] in H.
  - destruct lk; cbn in H; try (injection H as <-; reflexivity);
      destruct (lookup n g); cbn in H; try discriminate H; injection H as <-; reflexivity.
  - destruct lk; cbn in H; destruct (lookup n g); cbn in H; try discriminate H; injection H as <-; reflexivity.
Qed.

(** An initializer item that is a run of zeros writes nothing. *)
Definition is_zero (d : data_item) : bool := match d with Zero _ => true | _ => false end.

Lemma zeros_fold g zs : forall a m, forallb is_zero zs = true ->
  exists a', fold_left (item_contents g) zs (Some (a, m)) = Some (a', m).
Proof.
  induction zs as [|d zs IH]; intros a m H; [exists a; reflexivity|].
  cbn [forallb] in H. apply andb_true_iff in H as [Hd H]. destruct d; try discriminate Hd. apply IH. exact H.
Qed.

(** The kept string object is the only item of the erased copy that
    writes. Once the loader has passed it, its bytes stay. *)
Lemma erased_bytes keep g n lk al cs zs q : forallb is_zero zs = true -> keep n = true -> lookup n g = Some q ->
  forall md m m', (forall it, In it md -> keep (item_key it) = true -> it = IData n lk al (Str cs :: zs)) ->
  fold_left (contents g) (erase keep md) (Some m) = Some m' ->
  forall j, (j < length cs)%nat ->
  (In (IData n lk al (Str cs :: zs)) md \/ m_bytes m (ptr_addr q + Z.of_nat j) = nth j cs 0 mod 256) ->
  m_bytes m' (ptr_addr q + Z.of_nat j) = nth j cs 0 mod 256.
Proof.
  intros Hzs Hn Hq md. induction md as [|it md IH]; intros m m' Hk Hf j Hj Hin.
  - cbn in Hf. injection Hf as <-. destruct Hin as [[]|H]; exact H.
  - rewrite erase_cons in Hf. cbn [fold_left] in Hf.
    destruct (contents g (Some m) (erase_item keep it)) as [m1|] eqn:E; [|rewrite contents_fold_none in Hf; discriminate Hf].
    apply (IH m1 m'); [intros it' Hit'; apply Hk; right; exact Hit' | exact Hf | exact Hj |].
    destruct (keep (item_key it)) eqn:Ek.
    + pose proof (Hk it (or_introl eq_refl) Ek) as ->. right. rewrite erase_keep in E.
      2: { cbn [item_key] in Ek. exact Ek. }
      cbn [contents] in E. destruct lk; cbn in E; rewrite Hq in E; cbn in E;
        change (fold_left (fun (mi : mem * Z) (c : Z) => let (m', i) := mi in (store_bytes m' (ptr_addr q + i) 1 c, i + 1))
          cs (m, 0)) with (fold_left (sfold (ptr_addr q)) cs (m, 0)) in E;
        destruct (zeros_fold g zs (ptr_addr q + Z.of_nat (length cs)) (fst (fold_left (sfold (ptr_addr q)) cs (m, 0))) Hzs)
          as (a' & Ez); rewrite Ez in E; cbn in E; injection E as <-; pose proof (sfold_bytes (ptr_addr q) cs m 0 j Hj) as B; rewrite Z.add_0_r in B; exact B.
    + apply (contents_erased_same keep g m m1 it Ek) in E as ->.
      destruct Hin as [[E'|Hin]|H]; [subst it; cbn [item_key] in Ek; congruence|left; exact Hin|right; exact H].
Qed.

(** A module with distinct names and no negative runs of zeros holds,
    after loading, every character of each string object whose
    initializer is a string followed by zeros. *)
Lemma image_str_bytes md g m n lk al cs zs : forallb is_zero zs = true ->
  initial_memory md = Some (g, m) -> List.NoDup (map item_key md) -> zero_nonneg md = true ->
  In (IData n lk al (Str cs :: zs)) md ->
  exists q, lookup n g = Some q /\
    forall j, (j < length cs)%nat -> m_bytes m (ptr_addr q + Z.of_nat j) = nth j cs 0 mod 256.
Proof.
  intros Hzs Hi Hd Hz Hin. set (keep := fun x => name_eqb x n).
  destruct (kept_region md g m n lk al (Str cs :: zs) Hi Hd Hz Hin) as (q & Hq & _); [destruct lk; reflexivity|].
  destruct (erase_memory keep md g m Hi Hd Hz) as (m' & E & _ & B & _).
  assert (Hk : 0 <= items_size zs).
  { apply items_size_nonneg. unfold zero_nonneg in Hz. rewrite forallb_forall in Hz. specialize (Hz _ Hin).
    cbn [item_zero_ok forallb zero_ok] in Hz. exact Hz. }
  exists q. split; [exact Hq|]. intros j Hj. rewrite <- B.
  2: { exists (IData n lk al (Str cs :: zs)). split; [exact Hin|].
       exists n, lk, al, (Str cs :: zs), q. split_and!; [reflexivity | apply term_eqb_refl | exact Hq | lia |].
       pose proof (rounded_ge (Str cs :: zs)). rewrite items_size_cons in H. cbn [item_size] in H. lia. }
  unfold initial_memory in E. rewrite layout_fold_erase in E.
  destruct (fold_left layout md (Some (data_base, [], []))) as [[[a' g0] rs]|]; [|discriminate E].
  cbv beta iota zeta in E. rewrite alias_fold_erase in E.
  destruct (fold_left alias_global md (Some g0)) as [g1|]; [|discriminate E]. cbv beta iota zeta in E.
  destruct (fold_left (contents g1) (erase keep md) _) as [m1|] eqn:Ec; [|discriminate E].
  injection E as -> ->.
  refine (erased_bytes keep g n lk al cs zs q Hzs (term_eqb_refl n) Hq md _ m' _ Ec j Hj (or_introl Hin)).
  intros it Hit Hkit. apply term_eqb_eq in Hkit. apply (key_inj md _ _ Hd Hit Hin). exact Hkit.
Qed.

(** ## The C locale's transliteration tables

    Glibc stores each table as an array of 32-bit words, and the
    compiler emits it as one string of their little-endian bytes. The
    functions below read the words back out of the linked image. *)

(** This function lists the little-endian bytes of 32-bit words. *)
Definition le_words (ws : list Z) : list Z := flat_map (fun c => MemLogic.le_bytes c 4) ws.

(** This function reads a byte string as 32-bit words and drops a
    short tail. *)
Fixpoint words_of (cs : list Z) : list Z :=
  match cs with a :: b :: c :: d :: r => (a + 256 * (b + 256 * (c + 256 * d))) :: words_of r | _ => [] end.

(** This function returns the string that starts the initializer of
    the image's data object n, or nothing when it starts otherwise. *)
Definition img_str (n : string) : list Z :=
  match find (fun it => match it with IData k _ _ _ => name_eqb k (TAtom n) | _ => false end) hello_image_module with
  | Some (IData _ _ _ (Str cs :: _)) => cs
  | _ => []
  end.

Definition wc_from_idx : list Z := Eval vm_compute in words_of (img_str "glibc_C_ctype#translit_from_idx").
Definition wc_from_tbl : list Z := Eval vm_compute in words_of (img_str "glibc_C_ctype#translit_from_tbl").
Definition wc_to_idx : list Z := Eval vm_compute in words_of (img_str "glibc_C_ctype#translit_to_idx").
Definition wc_to_tbl : list Z := Eval vm_compute in words_of (img_str "glibc_C_ctype#translit_to_tbl").

(** Each table is a read-only local object whose initializer is the
    words' bytes, followed by a zero word in the two string tables.
    The record lists, for each table, its name, its words and the
    zeros after them. *)
Definition wc_tables : list (string * list Z * list data_item) :=
  [("glibc_C_ctype#translit_from_idx", wc_from_idx, []); ("glibc_C_ctype#translit_from_tbl", wc_from_tbl, [Zero 4]);
   ("glibc_C_ctype#translit_to_idx", wc_to_idx, []); ("glibc_C_ctype#translit_to_tbl", wc_to_tbl, [Zero 4])]%string.

Definition wc_item (t : string * list Z * list data_item) : item :=
  IData (TAtom t.1.1) (LRo (TAtom "local")) 4 (Str (le_words t.1.2) :: t.2).

Definition wfind (n : string) : option item :=
  find (fun it => match it with IData k _ _ _ => name_eqb k (TAtom n) | _ => false end) hello_image_module.

Lemma wc_tables_find : Forall (fun t => wfind t.1.1 = Some (wc_item t)) wc_tables.
Proof. repeat constructor; vm_compute; reflexivity. Qed.

Lemma wc_tables_in : Forall (fun t => In (wc_item t) hello_image_module) wc_tables.
Proof.
  eapply Forall_impl; [exact wc_tables_find|]. intros t H. exact (proj1 (find_some _ _ H)).
Qed.

(** ## The tables in the loaded image *)

(** A table's pieces are its object's life and the bytes of its
    words. *)
Definition wc_table_ps (t : string * list Z * list data_item) : list (piece * pval) :=
  (PLive (img_addr t.1.1), VLive (img_obj t.1.1).2) :: byte_ps (img_addr t.1.1) 0 (le_words t.1.2).

Definition hello_wc_tables_ps : list (piece * pval) := flat_map wc_table_ps wc_tables.

(** Each table's region is registered and live, it holds the table's
    bytes, and each of its bytes is below 256. *)
Definition wc_table_okb (t : string * list Z * list data_item) : bool :=
  let b := img_addr t.1.1 in let r := (img_obj t.1.1).2 in
  match object_region b img_regions with Some _ => true | None => false end &&
  match r_life r with Live => true | _ => false end && (0 <? b) &&
  (b + Z.of_nat (length (le_words t.1.2)) <=? r_end r) &&
  forallb (fun c => (0 <=? c) && (c <? 256)) (le_words t.1.2) && forallb is_zero t.2.

Lemma wc_tables_okb : forallb wc_table_okb wc_tables = true.
Proof. vm_compute. reflexivity. Qed.

(** Whatever memory the loader builds for Hello, its symbols and
    regions are the computed ones. *)
Lemma wc_loaded_tables g m : initial_memory hello_image_module = Some (g, m) ->
  g = img_globals /\ m_regions m = img_regions.
Proof.
  intros Hi.
  assert (C : option_map (fun gm => (fst gm, m_regions (snd gm))) (initial_memory hello_image_module) =
              Some (img_globals, img_regions)) by (rewrite hello_loaded_eq; vm_compute; reflexivity).
  rewrite Hi in C. cbn [option_map fst snd] in C. injection C as -> ->. split; reflexivity.
Qed.

(** Hello starts with the four tables as listed, in whatever memory
    the loader builds for it. *)
Lemma hello_wc_tables_agree g m : initial_memory hello_image_module = Some (g, m) -> all_agree m hello_wc_tables_ps.
Proof.
  intros Hi. destruct (wc_loaded_tables g m Hi) as [-> Hr].
  apply all_agree_intro. intros l v Hin. apply list_elem_of_In, in_flat_map in Hin as (t & Ht & Hin).
  pose proof wc_tables_okb as Ok. rewrite forallb_forall in Ok. specialize (Ok t Ht).
  unfold wc_table_okb in Ok. repeat rewrite andb_true_iff in Ok.
  destruct Ok as (((((Hreg & Hlive) & Hb) & Hend) & Hbytes) & Hzs).
  destruct (object_region (img_addr t.1.1) img_regions) as [r|] eqn:Er; [|discriminate Hreg].
  assert (Er' : (img_obj t.1.1).2 = r) by (unfold img_obj; cbn [snd]; rewrite Er; reflexivity).
  rewrite Er' in Hlive, Hend. destruct (r_life r) eqn:El; try discriminate Hlive.
  apply Z.leb_le in Hend. apply Z.ltb_lt in Hb. rewrite forallb_forall in Hbytes.
  pose proof wc_tables_in as Hins. rewrite Forall_forall in Hins. specialize (Hins t (proj2 (list_elem_of_In _ _) Ht)).
  destruct (image_str_bytes _ _ _ _ _ _ _ _ Hzs Hi hello_image_names hello_image_zero Hins) as (q & Hq & Hbs).
  assert (Hq' : img_addr t.1.1 = ptr_addr q) by (unfold img_addr; rewrite Hq; reflexivity).
  destruct Hin as [E|Hin].
  - apply pair_equal_spec in E as [<- <-]. cbn [agree_piece]. unfold live_at. rewrite Hr, Er', Er. split; [reflexivity | exact El].
  - unfold wc_table_ps in Hin. apply list_elem_of_In, list_elem_of_lookup in Hin as (i & Hi').
    assert (Hlen : (i < length (le_words t.1.2))%nat).
    { apply lookup_lt_Some in Hi'. unfold byte_ps in Hi'. rewrite length_zip_with, length_seqZ in Hi'. lia. }
    destruct (lookup_lt_is_Some_2 _ _ Hlen) as [x Hx].
    rewrite (byte_ps_lookup _ _ _ _ _ Hx) in Hi'. apply Some_inj, pair_equal_spec in Hi' as [<- <-]. cbn [agree_piece].
    unfold registered, in_live. rewrite Hr, Er. split; [discriminate|]. intros reg E' _. injection E' as <-.
    split_and!; [lia | lia |]. rewrite Z.add_0_l, Hq', Hbs by exact Hlen.
    rewrite (nth_lookup_Some _ _ 0 _ Hx). apply Z.mod_small.
    assert (Hxin : In x (le_words t.1.2)) by (apply list_elem_of_In; eapply list_elem_of_lookup_2; exact Hx).
    specialize (Hbytes x Hxin). apply andb_true_iff in Hbytes as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

(** ## The words that lead to the tables

    Transliteration finds the tables through the C locale's character
    type data. From offset 544 that data holds the number of entries,
    the four table pointers, the length and pointer of the default
    replacement, and the length of the list of ignored characters. The
    default replacement is a single question mark, and nothing is
    ignored. The ASCII step's function pointer sits at offset 40 of the
    output step. *)

(** This function gives the read-only pointer to the object n. *)
Definition wc_ro (n : string) : ptr := mkPtr (img_addr n) (Ro (img_addr n)).

Definition wc_life (n : string) : piece * pval := (PLive (img_obj n).1, VLive (img_obj n).2).

(** The ASCII step's converter is a function of the image. *)
Definition wc_ascii_fct : ptr :=
  mkPtr (img_addr "__gconv_transform_internal_ascii") (Fn (TAtom "__gconv_transform_internal_ascii")).

Definition hello_wc_words_ps : list (piece * pval) :=
  let cc := img_addr "_nl_C_LC_CTYPE" in
  byte_ps cc 544 (MemLogic.le_bytes 1659 4) ++
  ptr_ps cc 552 (wc_ro "glibc_C_ctype#translit_from_idx") ++ ptr_ps cc 560 (wc_ro "glibc_C_ctype#translit_from_tbl") ++
  ptr_ps cc 568 (wc_ro "glibc_C_ctype#translit_to_idx") ++ ptr_ps cc 576 (wc_ro "glibc_C_ctype#translit_to_tbl") ++
  byte_ps cc 584 (MemLogic.le_bytes 1 4) ++ ptr_ps cc 592 (wc_ro "glibc_C_ctype#str.280") ++
  byte_ps cc 600 (MemLogic.le_bytes 0 4) ++
  wc_life "glibc_C_ctype#str.280" :: byte_ps (img_addr "glibc_C_ctype#str.280") 0 (MemLogic.le_bytes 63 4) ++
  ptr_ps (img_addr "glibc_wcsmbsload#to_mb") 40 wc_ascii_fct.

(** The check keeps the three objects and the converter it names. *)
Definition hello_wc_words_names : list string :=
  ["_nl_C_LC_CTYPE"; "glibc_C_ctype#str.280"; "glibc_wcsmbsload#to_mb"; "__gconv_transform_internal_ascii"]%string.

Definition hello_wc_words_keep (n : name) : bool := existsb (name_eqb n) (map TAtom hello_wc_words_names).

Definition hello_wc_words_skel : module := Eval vm_compute in erase hello_wc_words_keep hello_image_module.
Lemma hello_wc_words_skel_eq : erase hello_wc_words_keep hello_image_module = hello_wc_words_skel.
Proof. vm_compute. reflexivity. Qed.

Definition hello_wc_words_kept : module := Eval vm_compute in kept_objects hello_wc_words_keep hello_image_module.
Lemma hello_wc_words_kept_incl : incl hello_wc_words_kept hello_image_module.
Proof.
  assert (E : kept_objects hello_wc_words_keep hello_image_module = hello_wc_words_kept) by (vm_compute; reflexivity).
  rewrite <- E. apply kept_objects_incl.
Qed.

Lemma hello_wc_words_check :
  match initial_memory hello_wc_words_skel with
  | Some (g, m') => pieces_ok hello_wc_words_keep hello_wc_words_kept g m' hello_wc_words_ps
  | None => false
  end = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma hello_wc_words_agree g m : initial_memory hello_image_module = Some (g, m) -> all_agree m hello_wc_words_ps.
Proof.
  intros E.
  destruct (image_pieces hello_wc_words_keep hello_wc_words_kept hello_image_module g m hello_wc_words_ps
    hello_wc_words_kept_incl E hello_image_names hello_image_zero) as (m' & E' & _ & P).
  pose proof hello_wc_words_check as C. rewrite <- hello_wc_words_skel_eq, E' in C. exact (P C).
Qed.
