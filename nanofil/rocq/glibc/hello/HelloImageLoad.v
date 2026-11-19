(** A proof that the linked Hello image holds some constants must first
    know that the loader builds a memory for the image at all, and that
    the image avoids the shapes that let one object's bytes land inside
    another. The generated decoding already checks that no run of zeros
    is negative. This file checks that no two items share a name, and it
    runs the loader on the decoded image itself, not on an erased copy.

    A successful load means only that the loader finishes on these
    items. It does not mean that Hello starts from this memory, that a
    constructor has run, or that a proof of Hello's entry runs this
    module. *)

From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Run.
From Glibc Require Import ImageEraseMem HelloImageModule.
Import ListNotations.

(** No two items of the linked image share a name. *)
Lemma hello_image_names : NoDup (map item_key hello_image_module).
Proof. apply names_distinct_sound. vm_cast_no_check (eq_refl true). Qed.

(** The cached placement records symbols and regions without expanding byte functions. *)
Definition hello_placement := Eval vm_compute in
  fold_left layout hello_image_module (Some (data_base, [], [])).

(** This equality checks the cached placement once so later proofs can reuse it. *)
Lemma hello_placement_eq :
  fold_left layout hello_image_module (Some (data_base, [], [])) = hello_placement.
Proof. vm_cast_no_check (eq_refl hello_placement). Qed.

(** The loader reuses cached placement while leaving alias resolution and byte writes unevaluated. *)
Definition hello_loaded :=
  match hello_placement with
  | Some (_, globals0, rs) =>
    match fold_left alias_global hello_image_module (Some globals0) with
    | Some globals =>
      match fold_left (contents globals) hello_image_module
                      (Some (mkMem (m_bytes empty_mem) rs (m_aux empty_mem))) with
      | Some m => Some (globals, m)
      | None => None
      end
    | None => None
    end
  | None => None
  end.

(** This equality lets proofs use the cached loader without recomputing placement. *)
Lemma hello_loaded_eq : initial_memory hello_image_module = hello_loaded.
Proof. unfold initial_memory, hello_loaded. rewrite hello_placement_eq. reflexivity. Qed.

(** The loader succeeds on the linked image. Only the symbols are
    computed, because computing the whole memory would unfold its byte
    functions. *)
Lemma hello_image_loads : option_map fst (initial_memory hello_image_module) <> None.
Proof. rewrite hello_loaded_eq. vm_compute. discriminate. Qed.

(** The loader's result can therefore be named. *)
Lemma hello_image_memory : exists g m, initial_memory hello_image_module = Some (g, m).
Proof.
  pose proof hello_image_loads as H. destruct (initial_memory hello_image_module) as [[g m]|].
  - exists g, m. reflexivity.
  - contradiction.
Qed.

(** ## Addresses by name

    The proofs about this image name each object that they read by its
    symbol rather than by its address, so that a relink which moves the
    objects changes only the generated files. These tables are the
    loader's symbols and regions for the image, computed once here. No
    lemma assumes that they are right: every proof that takes an address
    from them checks it again against the loader's own result. *)

(** These are the image's symbols after alias resolution. *)
Definition img_globals : list (name * ptr) := Eval vm_compute in
  match hello_placement with
  | Some (_, g0, _) =>
      match fold_left alias_global hello_image_module (Some g0) with Some g => g | None => [] end
  | None => []
  end.

(** These are the regions that the loader registers for the image. *)
Definition img_regions : list region := Eval vm_compute in
  match hello_placement with Some (_, _, rs) => rs | None => [] end.

(** This function returns the address of a symbol, or 0 if it has none. *)
Definition img_addr (n : string) : Z :=
  match Term.lookup (TAtom n) img_globals with Some p => ptr_addr p | None => 0%Z end.

(** This function returns a symbol's address with the region that the
    loader registers there. *)
Definition img_obj (n : string) : Z * region :=
  let b := img_addr n in
  (b, match object_region b img_regions with Some r => r | None => mkRegion b b GlobalData Live end).

(** This function pairs each name of a list with its address. *)
Definition img_at (ns : list string) : list (string * Z) := map (fun n => (n, img_addr n)) ns.

(** A proof that needs the address of a symbol names the symbol, and
    Rocq looks the address up while it reads the proof. The checked term
    then holds the plain number, so the lookup costs nothing when the
    proof runs. [img_a] gives the address and [img_e] gives the end of
    the region there. *)
Abbreviation img_a n := (ltac:(let v := eval vm_compute in (img_addr n%string) in exact v)) (only parsing).
Abbreviation img_e n := (ltac:(let v := eval vm_compute in (r_end (snd (img_obj n%string))) in exact v)) (only parsing).

(** [img_gd "name"] is the global-data region from a symbol's address to
    the end of the region that the loader registers there. *)
Abbreviation img_gd n := (mkRegion (img_a n) (img_e n) GlobalData Live) (only parsing).

(** [img_sym "name"] pairs a name with its address, and [img_ob "name"]
    pairs an object's address with its region. *)
Abbreviation img_sym n := (n%string, img_a n) (only parsing).
Abbreviation img_ob n := (img_a n, img_gd n) (only parsing).
