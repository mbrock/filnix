(** The proofs of glibc's startup functions share two kinds of helper.
    Startup code runs under the startup world interpretation
    [os_wi_start] while it changes the cookie and registers the two
    handlers, so its stores and allocations must keep that
    interpretation. It also allocates zeroed objects, chiefly the thread
    object, and then writes many separate fields of them. This module
    proves that ordinary stores and allocations keep [os_wi_start], and
    it splits a zeroed object into the fields a proof names.

    ## Stores and allocations under the startup world

    Writing to memory must never disturb what the runtime knows about
    the process, such as where `c: errno` lives. Proofs after startup
    check this for each store and each allocation. During startup the
    proof also tracks the cookie and the two handler flags in one ghost
    key. A store or an allocation writes only memory, never that key, so
    these steps are as harmless during startup as they are later. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From stdpp Require Import list gmap.
From Nanofil Require Import Term Syntax Values Memory Runtime Semantics Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import Fix OsWorld OsStart FileInv LibioLogic LibioCloseSteps.
Import ListNotations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** A list of pieces is plain when it holds neither a life token nor a
    ghost name. The pieces of a stored cell are plain. *)
Definition plain (ps : list (piece * pval)) : Prop :=
  forall l v, (l, v) ∈ ps -> match l with PLive _ | PName _ => False | _ => True end.

(** The eight bytes of a cell are plain. *)
Lemma plain_cell b o x : plain (cell b o x).
Proof.
  intros l v Hin. unfold cell in Hin. cbn in Hin.
  repeat (apply elem_of_cons in Hin as [Hin|Hin]; [injection Hin as -> _; exact I|]).
  by apply not_elem_of_nil in Hin.
Qed.

(** A run of bytes is plain. *)
Lemma plain_byte_ps b o xs : plain (byte_ps b o xs).
Proof. intros l v Hin. apply byte_ps_elem in Hin as (i & x & _ & -> & _). exact I. Qed.

(** A stored pointer, its capability slot and its bytes, is plain. *)
Lemma plain_pcell b o c a : plain ((PAux b o, VAux c) :: cell b o a).
Proof.
  intros l v Hin. apply elem_of_cons in Hin as [[= -> _] | Hin]; [exact I|]. exact (plain_cell _ _ _ _ _ Hin).
Qed.

(** One byte is plain. *)
Lemma plain_byte b o x : plain [(PByte b o, VByte x)].
Proof. intros l v Hin. apply list_elem_of_singleton in Hin. injection Hin as -> _. exact I. Qed.

(** Plain pieces carry no life token. *)
Lemma plain_no_life ps : plain ps -> no_life ps.
Proof. intros H l v Hin. specialize (H l v Hin). destruct l; tauto. Qed.

(** Overwriting memory pieces leaves every ghost name as it was. *)
Lemma overwrite_name ps h k :
  (forall l v, (l, v) ∈ ps -> mem_piece l) -> overwrite ps h !! PName k = h !! PName k.
Proof.
  induction ps as [|[l v] ps IH]; intros Hps; [reflexivity|]. cbn [overwrite fst snd].
  rewrite lookup_insert_ne.
  - apply IH. intros l' v' Hin. apply (Hps l' v'). right. exact Hin.
  - intros ->. exact (Hps (PName k) v ltac:(left)).
Qed.

(** Suppose a step leaves the key alone. If the step is fine in every
    fixed startup world, then it is fine under the startup
    interpretation. *)
Lemma os_wi_start_lift w0 k m w h m' h' :
  h' !! PName k = h !! PName k ->
  (forall c e d, os_wi (start_world w0 c e d) m w h -> os_wi (start_world w0 c e d) m' w h') ->
  os_wi_start w0 k m w h -> os_wi_start w0 k m' w h'.
Proof.
  intros Ek H (c & e & d & Hk & Hw). exists c, e, d. split; [rewrite Ek; exact Hk | exact (H _ _ _ Hw)].
Qed.

(** A store into an object that the caller owns is fine during startup.
    The store's new pieces must be the object's life token followed by
    plain pieces. *)
Lemma os_wi_start_store_life w0 k b reg ps ps' m m' wd h :
  m_regions m' = m_regions m -> plain ps' ->
  (forall l v, (l, v) ∈ (PLive b, VLive reg) :: ps -> h !! l = Some v) -> os_wi_start w0 k m wd h ->
  os_wi_start w0 k m' wd (overwrite ((PLive b, VLive reg) :: ps') h).
Proof.
  intros Er Hn Hh. apply os_wi_start_lift.
  - apply overwrite_name. intros l v Hin. apply elem_of_cons in Hin as [[= -> _] | Hin]; [exact I|].
    specialize (Hn l v Hin). destruct l; cbn; tauto.
  - intros c e d Hw. exact (os_wi_store_life _ b reg ps ps' m m' wd h Er (plain_no_life _ Hn) Hh Hw).
Qed.

(** A fresh allocation keeps the startup interpretation, because it
    keeps the fixed one. *)
Lemma os_wi_start_alloc w0 k m wd h q base :
  fresh m q base -> os_wi_start w0 k m wd h ->
  os_wi_start w0 k (allocated m q base) wd (overwrite (obj_ps base q) h).
Proof.
  intros Hf. apply os_wi_start_lift.
  - apply overwrite_name. intros l v Hin. exact (obj_ps_mem _ _ _ _ Hin).
  - intros c e d Hw. exact (os_wi_alloc _ _ _ _ _ _ Hf Hw).
Qed.

(** Each store rule asks the caller to show that the store is fine for
    the OS world. This tactic proves that premise during startup. *)
Ltac wi_store_start :=
  let Hh := fresh "Hh" in let Hw := fresh "Hw" in
  intros ? ? ? Hh Hw; eapply os_wi_start_store_life; [reflexivity | | exact Hh | exact Hw];
  first [apply plain_cell | apply plain_byte_ps | apply plain_pcell | apply plain_byte].

(** A runtime function is external to a program when the program
    defines it neither as code nor as data, so that a call reaches its
    contract. *)
Definition os_ext (ge : genv) (n : string) : Prop :=
  find_fn ge (TAtom n) = None /\ lookup (TAtom n) (ge_globals ge) = None.

(** ## Fields of a zeroed object

    A fresh object has zero bytes and empty capability slots. A proof
    about code that fills in some of its fields wants each field as its
    own assertion. A layout lists the fields in order, with padding
    between them, and [zero_layout] turns the zeroed object into one
    assertion for each field. *)

(** A field is padding, a null pointer slot, a zero [c: int], a zero
    [c: long] or a zero byte. *)
Inductive field := FPad (n : nat) | FPtr | FInt | FLong | FByte.

(** This function gives the size of a field in bytes. *)
Definition field_len (f : field) : nat :=
  match f with FPad n => n | FPtr | FLong => 8 | FInt => 4 | FByte => 1 end.

(** The size of a layout is the sum of its fields' sizes. *)
Definition layout_len (fs : list field) : nat := fold_right (fun f n => field_len f + n)%nat 0%nat fs.

Section fields.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** The assertion a zero field gives at offset o of the object b.
    Padding gives nothing. *)
Definition field_own (b o : Z) (f : field) : iProp Σ :=
  match f with
  | FPad _ => True
  | FPtr => pcell b o null
  | FInt => bytes b o [0; 0; 0; 0]
  | FLong => icell b o 0
  | FByte => ibyte b o 0
  end.

(** This assertion owns all the fields of a layout, and the first field
    starts at offset o. *)
Fixpoint layout_own (b o : Z) (fs : list field) : iProp Σ :=
  match fs with
  | [] => True
  | f :: fs' => field_own b o f ∗ layout_own b (o + Z.of_nat (field_len f)) fs'
  end.

(** A zero range of a field's size gives that field. *)
Lemma zero_field b o f :
  bytes b o (replicate (field_len f) 0) ∗ auxes b o (replicate (field_len f) CNone) ⊢ field_own b o f.
Proof.
  destruct f; cbn [field_len field_own replicate].
  - iIntros "_". done.
  - iIntros "[Hb Ha]". iApply pcell_null_of. rewrite (auxes_app b o [CNone] (replicate 7 CNone)).
    iDestruct "Ha" as "[$ _]". iExact "Hb".
  - iIntros "[$ _]".
  - iIntros "[Hb _]". rewrite /bytes byte_ps_cell0. iExact "Hb".
  - iIntros "[Hb _]". rewrite /bytes /ibyte /byte_ps. cbn. iExact "Hb".
Qed.

(** A zero range of a layout's size gives all of its fields. *)
Lemma zero_layout b o fs :
  bytes b o (replicate (layout_len fs) 0) ∗ auxes b o (replicate (layout_len fs) CNone) ⊢ layout_own b o fs.
Proof.
  revert o. induction fs as [|f fs IH]; intros o; cbn [layout_len fold_right layout_own].
  - iIntros "_". done.
  - rewrite !replicate_add bytes_app auxes_app !length_replicate.
    iIntros "[[Hb Hbs] [Ha Has]]". iSplitL "Hb Ha"; [iApply zero_field; iFrame|].
    iApply IH. iFrame.
Qed.

End fields.
