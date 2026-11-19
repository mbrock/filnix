(** The linked program must start from real memory, not merely from
    stream and allocator resources that could be inconsistent. This
    file names its actual initial image and checks the finite pieces
    that glibc's allocator reads before allocating stdout's buffer. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List.
From stdpp Require Import list_numbers.
From Nanofil Require Import Term Syntax Values Memory Semantics Run Pieces Heap.
From Glibc Require Import HiAtexitModule ImageErase ImageEraseMem ImagePieces.
Import ListNotations.
Open Scope Z_scope.

(** The linker determines the program's starting memory. This definition
    returns empty memory only if layout fails; [hi_initial] rules that out. *)
Definition hi_m0 : mem :=
  match initial_memory hi_module with Some (_, m) => m | None => empty_mem end.

(** Laying out the actual linked module succeeds and produces this
    image together with the globals used by every linked call. *)
Lemma hi_initial : initial_memory hi_module = Some (hi_globals, hi_m0).
Proof.
  pose proof hi_layout as H. unfold hi_m0.
  destruct (initial_memory hi_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** ## Checking pieces on a smaller image

    The initial image is a chain of every initializer store, so reading
    one byte of it walks past thousands of stores, most of them the C
    locale's ctype tables. A piece check therefore runs on the erased
    image that ImageErase.v defines instead: it keeps the objects
    that the pieces name and writes zeros for every other object. The
    erasure theorems of ImageEraseMem.v and ImagePieces.v show
    that the erased image has the same regions and the same bytes and
    capabilities on every kept object, so a passing check gives
    agreement with [hi_m0] itself. *)

(** This function returns the object that a piece belongs to, if any. *)
Definition hi_piece_base (l : piece) : list Z :=
  match l with PLive b | PByte b _ | PAux b _ => [b] | PName _ => [] end.

(** A check keeps the data objects whose base address some piece names.
    The bases are collected once, before the loader asks about any name. *)
Definition hi_keep (ps : list (piece * pval)) : name -> bool :=
  let bs := nodup Z.eq_dec (flat_map (fun lv => hi_piece_base lv.1) ps) in
  fun n => match Term.lookup n hi_globals with
  | Some p => existsb (Z.eqb (ptr_addr p)) bs
  | None => false
  end.

(** This memory is the loader's image of the erased module. *)
Definition hi_erased (keep : name -> bool) : mem :=
  match initial_memory (erase keep hi_module) with Some (_, m) => m | None => empty_mem end.

(** The items of the linked module have distinct names, so the loader
    writes each object exactly where its symbol points. *)
Lemma hi_module_names : List.NoDup (map item_key hi_module).
Proof. apply names_distinct_sound. vm_compute. reflexivity. Qed.

(** No run of zeros in the linked module has a negative length. *)
Lemma hi_module_zeros : zero_nonneg hi_module = true.
Proof. vm_compute. reflexivity. Qed.

(** The erased image has the same regions as [hi_m0], and the same
    bytes and capabilities at every address of a kept object. *)
Lemma hi_erased_agree keep :
  m_regions (hi_erased keep) = m_regions hi_m0 /\
  forall x, kept_at keep hi_module hi_globals x ->
    m_bytes (hi_erased keep) x = m_bytes hi_m0 x /\ m_aux (hi_erased keep) x = m_aux hi_m0 x.
Proof.
  destruct (erase_memory keep _ _ _ hi_initial hi_module_names hi_module_zeros) as (m' & E & R & B & A).
  unfold hi_erased. rewrite E. split; [exact R|]. intros x Hx. split; [exact (B x Hx)|exact (A x Hx)].
Qed.

(** A piece list that passes the check on its erased image agrees with
    the initial image. *)
Lemma hi_m0_pieces ps :
  pieces_ok (hi_keep ps) hi_module hi_globals (hi_erased (hi_keep ps)) ps = true -> all_agree hi_m0 ps.
Proof.
  destruct (image_pieces (hi_keep ps) hi_module hi_module hi_globals hi_m0 ps (incl_refl _)
    hi_initial hi_module_names hi_module_zeros) as (m' & E & _ & H).
  unfold hi_erased. rewrite E. exact H.
Qed.

(** The allocator's configuration occupies this static region. *)
Definition hi_mp_reg : region := mkRegion 68800 68936 GlobalData Live.

(** The thread-cache pointer occupies this TLS region. *)
Definition hi_tc_reg : region := mkRegion 68992 69000 GlobalData Live.

(** The empty cache bins belong to the read-only dummy object. *)
Definition hi_dummy_reg : region := mkRegion 65888 66656 GlobalData Live.

(** The allocator reads these three objects in this exact image. *)
Lemma hi_allocator_regions :
  object_region 68800 (m_regions hi_m0) = Some hi_mp_reg /\
  object_region 68992 (m_regions hi_m0) = Some hi_tc_reg /\
  object_region 65888 (m_regions hi_m0) = Some hi_dummy_reg.
Proof. vm_compute. repeat split; reflexivity. Qed.

(** A pointer's image includes its capability slot and address bytes. *)
Definition hi_pointer_ps (b o : Z) (p : ptr) : list (piece * pval) :=
  (PAux b o, VAux (ptr_cap p)) :: cell b o (ptr_addr p).

(** Before allocating a buffer, glibc reads its configuration and empty
    cache bins. This list records those fields and their owning objects. *)
Definition hi_allocator_ps : list (piece * pval) :=
  concat [[(PLive 68800, VLive hi_mp_reg)]; cell 68800 120 1041;
    [(PLive 68992, VLive hi_tc_reg)]; (PAux 68992 0, VAux (Ro 65888)) :: cell 68992 0 65888;
    [(PLive 65888, VLive hi_dummy_reg)];
    concat (map (fun i => (PAux 65888 (152 + 8 * i), VAux CNone) ::
      cell 65888 (152 + 8 * i) 0) (seqZ 0 64))].

(** Every allocator piece agrees with the actual initial image,
    including the pointer capabilities and every empty cache bin. *)
Lemma hi_allocator_agree : all_agree hi_m0 hi_allocator_ps.
Proof. apply hi_m0_pieces. vm_cast_no_check (eq_refl true). Qed.

(** The finite key check compares object identities and offsets
    without constructing equality proofs for every pair of bytes.
    It conservatively treats all non-memory name keys as equal. *)
Definition hi_same_piece (x y : piece) : bool :=
  match x, y with
  | PLive b, PLive c => b =? c
  | PByte b o, PByte c p | PAux b o, PAux c p => (b =? c) && (o =? p)
  | PName _, PName _ => true
  | _, _ => false
  end.

(** The check rejects a key if an equal key occurs later in the list. *)
Fixpoint hi_unique (xs : list piece) : bool :=
  match xs with
  | [] => true
  | x :: xs => negb (existsb (hi_same_piece x) xs) && hi_unique xs
  end.

(** Passing the finite check proves that ownership keys are distinct. *)
Lemma hi_unique_sound xs : hi_unique xs = true -> NoDup xs.
Proof.
  induction xs as [|x xs IH]; [constructor|]. cbn.
  rewrite Bool.andb_true_iff. rewrite Bool.negb_true_iff. intros [Hnot Hxs].
  constructor; [|exact (IH Hxs)]. intros Hin.
  assert (Hsame : hi_same_piece x x = true) by (destruct x; cbn; rewrite ?Z.eqb_refl; reflexivity).
  assert (Hex : existsb (hi_same_piece x) xs = true).
  { apply existsb_exists. exists x. split; [apply list_elem_of_In; exact Hin|exact Hsame]. }
  congruence.
Qed.

(** The allocator can own all these fields at once: no object or field
    appears twice in the list. *)
Lemma hi_allocator_nodup : NoDup hi_allocator_ps.*1.
Proof. apply hi_unique_sound. vm_compute. reflexivity. Qed.
