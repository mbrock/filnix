(** The linked program must start from real memory, not merely from
    stream and allocator resources that could be inconsistent. This
    file names its actual initial image and checks the finite pieces
    that glibc's allocator reads before allocating stdout's buffer. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List.
From stdpp Require Import list_numbers.
From Nanofil Require Import Term Syntax Values Memory Semantics Run Pieces Heap.
From Glibc Require Import HiAtexitModule.
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
Proof. apply checked_pieces_all_agree. vm_cast_no_check (eq_refl true). Qed.

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
