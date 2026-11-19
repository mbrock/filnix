(** The proof of `c: __libc_start_main` takes the facts it needs about
    the linked image as premises, and [StartLsmImage](../startup/StartLsmImage.v)
    collects the pure ones in [lsm_image_ok]. This module proves them
    for the whole linked Hello image. It also shows that Hello's
    `c: __libc_start_main` has the body that the proof was made for.

    The memory of the whole Hello image is too large to compute, but the
    symbols are not. Each lemma holds for whatever memory the loader
    builds, and each reads the addresses from the image rather than
    writing them here, so a relink changes no line of this module. *)

From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Run Pieces.
From Glibc Require Import OsStartCalls StartLogic StartLibcStartMain StartLsmImage
  HelloImageModule HelloImageLoad ImageEraseMem.
Import ListNotations.
Open Scope Z_scope.

(** Hello's `c: __libc_start_main` has the body that the startup proof
    runs. *)
Lemma hello_start_libc_start_main_defined :
  find_direct (TAtom "__libc_start_main") hello_image_module = Some (Defined start_libc_start_main_fn).
Proof. vm_compute. reflexivity. Qed.

(** This record holds Hello's addresses and regions, read from the
    symbols and regions that the loader computes for the image. *)
Definition hello_lsm_objs : lsm_objs := Eval vm_compute in lsm_objs_in img_globals img_regions.

(** These are the symbols of the startup body as the loader gives them. *)
Definition hello_lsm_lookups : list (option ptr) := Eval vm_compute in
  map (fun n => lookup n img_globals) (TAtom "__pthread_initialize_minimal" :: lsm_names).

(** Whatever memory the loader builds, its symbols are these. *)
Lemma hello_lsm_found g m : initial_memory hello_image_module = Some (g, m) ->
  map (fun n => lookup n g) (TAtom "__pthread_initialize_minimal" :: lsm_names) = hello_lsm_lookups /\
  lsm_objs_in g (m_regions m) = hello_lsm_objs.
Proof.
  intros Hi.
  assert (C : option_map (fun gm => (map (fun n => lookup n (fst gm)) (TAtom "__pthread_initialize_minimal" :: lsm_names),
                                     lsm_objs_in (fst gm) (m_regions (snd gm))))
                (initial_memory hello_image_module) = Some (hello_lsm_lookups, hello_lsm_objs))
    by (rewrite hello_loaded_eq; vm_compute; reflexivity).
  rewrite Hi in C. cbn [option_map fst snd] in C.
  apply (f_equal (fun o => match o with Some x => x | None => (hello_lsm_lookups, hello_lsm_objs) end)) in C.
  split; [exact (f_equal fst C) | exact (f_equal snd C)].
Qed.

(** These are the six globals of the record with their regions. *)
Definition hello_lsm_objs_regions : list (Z * region) :=
  [(lo_en hello_lsm_objs, lo_enreg hello_lsm_objs); (lo_dx hello_lsm_objs, lo_dxreg hello_lsm_objs);
   (lo_es hello_lsm_objs, lo_esreg hello_lsm_objs); (lo_dm hello_lsm_objs, lo_dmreg hello_lsm_objs);
   (lo_re hello_lsm_objs, lo_rereg hello_lsm_objs); (lo_se hello_lsm_objs, lo_sereg hello_lsm_objs)].

Local Lemma map_eq_Forall {A B : Type} (f h : A -> B) xs :
  map f xs = map h xs -> Forall (fun x => f x = h x) xs.
Proof.
  induction xs as [|x xs IH]; cbn; intros E; [constructor|].
  injection E as E1 E2. constructor; [exact E1 | exact (IH E2)].
Qed.

(** The regions of the record are the ones that the loader registers at
    those addresses, so a proof that owns the globals at the start owns
    them with these regions. *)
Lemma hello_lsm_regions g m : initial_memory hello_image_module = Some (g, m) ->
  Forall (fun q => object_region (fst q) (m_regions m) = Some (snd q)) hello_lsm_objs_regions.
Proof.
  intros Hi.
  assert (C : option_map (fun gm => map (fun q => object_region (fst q) (m_regions (snd gm))) hello_lsm_objs_regions)
      (initial_memory hello_image_module) = Some (map (fun q => Some (snd q)) hello_lsm_objs_regions))
    by (rewrite hello_loaded_eq; vm_compute; reflexivity).
  rewrite Hi in C. cbn [option_map fst snd] in C.
  apply (f_equal (fun o => match o with Some x => x | None => [] end)) in C.
  exact (map_eq_Forall (fun q => object_region (fst q) (m_regions m)) (fun q => Some (snd q)) _ C).
Qed.

(** A proof of the startup of Hello can call the body of
    `c: __libc_start_main` without checking the image again, because
    the image meets every pure premise of that proof, whatever memory
    the loader builds. *)
Lemma hello_lsm_image_ok g m fr : initial_memory hello_image_module = Some (g, m) ->
  lsm_image_ok (mkGenv hello_image_module g fr) hello_lsm_objs.
Proof.
  intros Hi. destruct (hello_lsm_found g m Hi) as [L _].
  cbv [map lsm_names errno_handler_name hello_lsm_lookups] in L.
  injection L as Lp Len Ldx Les Ldm Lre Lse Lcf Lhp Ldp.
  assert (X : forall s, absent_ok hello_image_module s = true ->
              os_ext (mkGenv hello_image_module g fr) s) by (intros s Hs; exact (absent_ok_sound _ _ _ fr _ Hi Hs)).
  unfold lsm_image_ok. cbn [ge_globals].
  cbv [hello_lsm_objs lo_en lo_enreg lo_dx lo_dxreg lo_es lo_esreg lo_dm lo_dmreg lo_re lo_rereg lo_se lo_sereg
       lo_cfp lo_hp lo_dp lo_dn errno_handler_name].
  repeat split;
    first [ apply X; vm_compute; reflexivity | eassumption | vm_compute; reflexivity | vm_compute; intro; discriminate ].
Qed.
