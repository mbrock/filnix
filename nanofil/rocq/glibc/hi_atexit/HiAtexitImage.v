(** The loader image must leave the interpreter's allocation cursor
    above every static object and every initialized byte. This file
    checks those physical facts for the actual linked image. It also
    checks that static objects do not overlap, before host preparation
    allocates the thread object. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import ZArith List Lia.
From stdpp Require Import list.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Pieces.
From Glibc Require Import HiAtexitModule HiAtexitInitial.
Import ListNotations.
Open Scope Z_scope.

(** Looking up an object returns a region with that object's identity
    from the region table, not an unrelated region. *)
Lemma hi_object_member b rs reg : object_region b rs = Some reg ->
  b = r_base reg /\ In reg rs.
Proof.
  induction rs as [|r rs IH]; cbn; [discriminate|].
  destruct (Z.eqb (r_base r) b) eqn:E.
  - intros [= <-]. apply Z.eqb_eq in E. split; [congruence|left; reflexivity].
  - intros H. destruct (IH H) as [Hb Hin]. split; [exact Hb|right; exact Hin].
Qed.

(** The computed table is exactly the loader image's table. *)
Definition hi_image_regions : list region := Eval vm_compute in m_regions hi_m0.

(** Every recorded object lies below the initial cursor and is live. *)
Lemma hi_image_bounds reg : In reg hi_image_regions ->
  0 <= r_base reg < InterpRuntime.start /\ r_end reg <= InterpRuntime.start /\ r_life reg = Live.
Proof.
  assert (Hcheck : forallb (fun r =>
    (0 <=? r_base r) && (r_base r <? InterpRuntime.start) &&
    (r_end r <=? InterpRuntime.start) &&
    match r_life r with Live => true | Freed => false end) hi_image_regions = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in Hcheck. intros Hin. specialize (Hcheck reg Hin).
  repeat rewrite Bool.andb_true_iff in Hcheck.
  destruct Hcheck as (((Hb & Hs) & He) & Hl).
  apply Z.leb_le in Hb. apply Z.ltb_lt in Hs. apply Z.leb_le in He.
  destruct (r_life reg); [auto|discriminate].
Qed.

(** The finite pairwise check covers all objects, not only the ones
    whose fields the main proof happens to own. *)
Lemma hi_image_apart r1 r2 : In r1 hi_image_regions -> In r2 hi_image_regions ->
  r_base r1 <> r_base r2 -> r_end r1 <= r_base r2 \/ r_end r2 <= r_base r1.
Proof.
  assert (Hcheck : forallb (fun r => forallb (fun s =>
    (r_base r =? r_base s) || (r_end r <=? r_base s) || (r_end s <=? r_base r))
    hi_image_regions) hi_image_regions = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in Hcheck. intros H1 H2 Hne.
  specialize (Hcheck r1 H1). rewrite forallb_forall in Hcheck.
  specialize (Hcheck r2 H2). repeat rewrite Bool.orb_true_iff in Hcheck.
  destruct Hcheck as [[Heq|He]|He];
    [apply Z.eqb_eq in Heq; contradiction|left; apply Z.leb_le; exact He|right; apply Z.leb_le; exact He].
Qed.

(** No two live objects in the loader image overlap. *)
Lemma hi_image_live_disjoint : live_disjoint hi_m0.
Proof.
  intros b1 r1 b2 r2 [H1 _] [H2 _] Hne.
  apply hi_object_member in H1 as [Hb1 H1]. apply hi_object_member in H2 as [Hb2 H2].
  rewrite Hb1, Hb2. apply hi_image_apart; [exact H1|exact H2|congruence].
Qed.

(** No byte or capability at or above the cursor has been written. *)
Definition hi_image_high (m : mem) : Prop :=
  forall a, InterpRuntime.start <= a -> m_bytes m a = 0 /\ m_aux m a = CNone.

(** A byte store wholly below the cursor preserves that condition. *)
Lemma hi_image_high_bytes m a n x : a + n <= InterpRuntime.start ->
  hi_image_high m -> hi_image_high (store_bytes m a n x).
Proof.
  intros Hend H a' Ha'. unfold store_bytes. cbn.
  assert (Houtside : (a' <? a + n) = false) by (apply Z.ltb_ge; lia).
  rewrite Houtside, Bool.andb_false_r. exact (H a' Ha').
Qed.

(** A capability store below the cursor preserves the same condition. *)
Lemma hi_image_high_aux m a c : a < InterpRuntime.start ->
  hi_image_high m -> hi_image_high (store_aux m a c).
Proof.
  intros Hend H a' Ha'. unfold store_aux. cbn.
  assert (Houtside : (a' =? a) = false) by (apply Z.eqb_neq; lia).
  rewrite Houtside. exact (H a' Ha').
Qed.

(** Checking each initializer store one by one costs a proof step per
    string byte, which no longer fits the file's time budget once the
    image links glibc's startup code. Instead, a boolean pass follows
    only the write cursor of every static initializer, the same way
    [initial_memory] does, and checks that each store ends at or below
    the allocation cursor. The lemmas below show that a passing check
    keeps higher memory unwritten. *)
Definition hi_item_below (st : option Z) (it : data_item) : option Z :=
  match st with
  | None => None
  | Some a =>
      match it with
      | Sym _ _ => if (a mod 8 =? 0) && (a + 8 <=? InterpRuntime.start) then Some (a + 8) else None
      | Item w _ => if a + width_bytes w <=? InterpRuntime.start then Some (a + width_bytes w) else None
      | Str cs =>
          if a + Z.of_nat (length cs) <=? InterpRuntime.start
          then Some (a + Z.of_nat (length cs)) else None
      | Zero n => Some (a + n)
      | ItemOther _ => None
      end
  end.

(** Every data object's initializers pass the cursor check, starting
    from the object's address in the given globals. *)
Definition hi_contents_below (globals : list (name * ptr)) (it : item) : bool :=
  match it with
  | IData _ LExternWeak _ [] => true
  | IData n _ _ items =>
      match Term.lookup n globals with
      | Some p => match fold_left hi_item_below items (Some (ptr_addr p)) with
                  | Some _ => true | None => false end
      | None => true
      end
  | _ => true
  end.

(** A string's byte stores stay below the cursor when its last byte does. *)
Lemma hi_image_high_str cs : forall m a i, a + i + Z.of_nat (length cs) <= InterpRuntime.start ->
  hi_image_high m ->
  hi_image_high (fst (fold_left (fun (mi : mem * Z) (c : Z) =>
    let (m', j) := mi in (store_bytes m' (a + j) 1 c, j + 1)) cs (m, i))).
Proof.
  induction cs as [|c cs IH]; intros m a i Hend H; cbn [fold_left]; [exact H|].
  cbn [length] in Hend. apply IH; [lia|]. apply hi_image_high_bytes; [lia|exact H].
Qed.

(** While memory is being initialized, the real write address must
    match the address the check is following, and higher memory must
    stay unwritten. Once the check has failed, nothing is claimed. *)
Definition hi_cursor_rel (st : option (Z * mem)) (sto : option Z) : Prop :=
  match st, sto with
  | Some (a, m), Some b => a = b /\ hi_image_high m
  | _, _ => True
  end.

(** One initializer preserves the relation between memory and cursor. *)
Lemma hi_item_below_step globals st sto it : hi_cursor_rel st sto ->
  hi_cursor_rel (item_contents globals st it) (hi_item_below sto it).
Proof.
  destruct st as [[a m]|]; [|intros _; exact I].
  destruct sto as [b|];
    [|intros _; cbn [hi_item_below]; destruct (item_contents _ _ _) as [[]|]; exact I].
  intros [<- H]. destruct it as [w n|cs|sym off|n|t]; cbn.
  - destruct (_ <=? _) eqn:E; [|exact I]. apply Z.leb_le in E.
    split; [reflexivity|]. apply hi_image_high_bytes; [lia|exact H].
  - destruct (_ <=? _) eqn:E; [|exact I]. apply Z.leb_le in E.
    split; [reflexivity|]. apply (hi_image_high_str _ _ _ 0); [lia|exact H].
  - destruct (a mod 8 =? 0); cbn; [|exact I].
    destruct (_ <=? _) eqn:E; [|exact I]. apply Z.leb_le in E. split; [reflexivity|].
    apply hi_image_high_aux; [lia|]. apply hi_image_high_bytes; [lia|exact H].
  - split; [reflexivity|exact H].
  - exact I.
Qed.

(** Folding the step over an object's initializers keeps the relation. *)
Lemma hi_item_below_fold globals items : forall st sto, hi_cursor_rel st sto ->
  hi_cursor_rel (fold_left (item_contents globals) items st) (fold_left hi_item_below items sto).
Proof.
  induction items as [|it items IH]; intros st sto H; [exact H|].
  apply IH. apply hi_item_below_step. exact H.
Qed.

(** A data object at a known address whose initializers pass the
    check keeps memory above the cursor unwritten. *)
Lemma hi_data_below globals items a m m' :
  fold_left hi_item_below items (Some a) <> None ->
  option_map snd (fold_left (item_contents globals) items (Some (a, m))) = Some m' ->
  hi_image_high m -> hi_image_high m'.
Proof.
  intros Hok Hc H.
  pose proof (hi_item_below_fold globals items (Some (a, m)) (Some a) (conj eq_refl H)) as Hrel.
  destruct (fold_left (item_contents globals) items _) as [[a' m'']|]; [|discriminate].
  injection Hc as <-.
  destruct (fold_left hi_item_below items (Some a)); [exact (proj2 Hrel)|congruence].
Qed.

(** Every top-level item that passes the check keeps memory above the
    cursor unwritten: only data objects write memory at all. *)
Lemma hi_contents_below_step globals m m' it : hi_contents_below globals it = true ->
  contents globals (Some m) it = Some m' -> hi_image_high m -> hi_image_high m'.
Proof.
  intros Hok Hc H.
  destruct it as [f|n t|n lk al items|n lk t]; cbn in Hc; try (injection Hc as <-; exact H).
  assert (Hdata : match Term.lookup n globals with
      | Some p => match fold_left (item_contents globals) items (Some (ptr_addr p, m)) with
                  | Some r => Some (snd r) | None => None end
      | None => None end = Some m' -> hi_contents_below globals (IData n LExport al items) = true -> hi_image_high m').
  { cbn. destruct (Term.lookup n globals) as [p|]; cbn; [|discriminate].
    intros Hc' Hok'. apply (hi_data_below globals items (ptr_addr p) m); [|exact Hc'|exact H].
    destruct (fold_left hi_item_below items _); congruence. }
  destruct lk; try exact (Hdata Hc Hok).
  destruct items as [|i items]; [injection Hc as <-; exact H|exact (Hdata Hc Hok)].
Qed.

(** Folding [contents] over a passing module keeps memory above the
    cursor unwritten. *)
Lemma hi_contents_below_fold globals md : forall m m',
  forallb (hi_contents_below globals) md = true ->
  fold_left (contents globals) md (Some m) = Some m' -> hi_image_high m -> hi_image_high m'.
Proof.
  induction md as [|it md IH]; intros m m' Hok Hf H.
  - injection Hf as <-. exact H.
  - change (hi_contents_below globals it && forallb (hi_contents_below globals) md = true) in Hok.
    change (fold_left (contents globals) md (contents globals (Some m) it) = Some m') in Hf.
    apply Bool.andb_true_iff in Hok as [Hit Hok].
    destruct (contents globals (Some m) it) as [m1|] eqn:Hc.
    + exact (IH m1 m' Hok Hf (hi_contents_below_step _ _ _ _ Hit Hc H)).
    + exfalso. clear -Hf.
      induction md as [|it' md IH]; cbn [fold_left] in Hf; [discriminate|].
      exact (IH Hf).
Qed.

(** Any module whose initializers pass the check has an initial
    memory that leaves everything above the cursor unwritten. *)
Lemma hi_initial_below md g m : initial_memory md = Some (g, m) ->
  forallb (hi_contents_below g) md = true -> hi_image_high m.
Proof.
  unfold initial_memory. intros Hinit Hok.
  destruct (fold_left layout md _) as [[[a g0] rs]|]; [|discriminate]. cbn in Hinit.
  destruct (fold_left alias_global md _) as [g'|]; [|discriminate]. cbn in Hinit.
  destruct (fold_left (contents g') md _) as [m'|] eqn:Hc; [|discriminate].
  injection Hinit as -> ->.
  refine (hi_contents_below_fold g md _ m Hok Hc _). intros x Hx. split; reflexivity.
Qed.

(** The loader writes nothing where the first allocation will occur.
    Every initializer store of the linked module passes the cursor check. *)
Lemma hi_image_high_initial : hi_image_high hi_m0.
Proof.
  apply (hi_initial_below hi_module hi_globals); [exact hi_initial|].
  vm_compute. reflexivity.
Qed.

(** The runtime can allocate safely above the static image: every
    existing object ends below its cursor, and higher memory is unwritten. *)
Lemma hi_image_ready : InterpRuntime.ready InterpRuntime.start hi_m0.
Proof.
  split; [unfold InterpRuntime.start, InterpRuntime.address_end; lia|]. split.
  - intros b reg H. apply hi_object_member in H as [Hb Hin].
    destruct (hi_image_bounds reg Hin) as (Hbnd & Hend & Hlive).
    rewrite Hb. split; [exact Hbnd|]. split; [exact Hend|].
    intros Hfree. congruence.
  - exact hi_image_high_initial.
Qed.
