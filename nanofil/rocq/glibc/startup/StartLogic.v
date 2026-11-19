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
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Pieces Heap ExternalCalls StepRules Language Logic StringLogic MemLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsStart FileInv LibioLogic LibioCloseSteps.
Import ListNotations Fix.ML0 Fix.LG0 Fix.LG0.L.
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
Proof using Type.
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
Proof using Type.
  revert o. induction fs as [|f fs IH]; intros o; cbn [layout_len fold_right layout_own].
  - iIntros "_". done.
  - rewrite !replicate_add bytes_app auxes_app !length_replicate.
    iIntros "[[Hb Hbs] [Ha Has]]". iSplitL "Hb Ha"; [iApply zero_field; iFrame|].
    iApply IH. iFrame.
Qed.

(** A fresh object whose size matches a layout gives its lifetime and
    the layout's zero fields. *)
Lemma obj_layout b q fs :
  0 <= req_extent q -> Z.to_nat (req_extent q) = layout_len fs ->
  obj b q ⊢ live b (mkRegion b (b + req_extent q) (req_kind q) Live) ∗ layout_own b 0 fs.
Proof using Type.
  intros H Hl. rewrite obj_zero_block; [|exact H]. rewrite Hl. iIntros "[$ H]". iApply zero_layout. iExact "H".
Qed.

(** A fresh object can be lent whole to a system call that fills it.
    Its zero bytes and empty capability slots then become a block of
    unknown contents. *)
Lemma obj_blk_any b q :
  0 <= req_extent q -> obj b q ⊢ live b (mkRegion b (b + req_extent q) (req_kind q) Live) ∗ blk_any b 0 (req_extent q).
Proof using Type.
  iIntros (H) "Ho". rewrite obj_zero_block; [|exact H]. iDestruct "Ho" as "($ & Hb & Ha)".
  iExists (replicate (Z.to_nat (req_extent q)) 0), (replicate (Z.to_nat (req_extent q)) CNone).
  rewrite /bytes /auxes pts_app. iFrame. iPureIntro. rewrite !length_replicate. done.
Qed.

End fields.

(** ## Reading bytes whose values are unknown

    A system call that fills a buffer leaves bytes that the proof knows
    nothing about, such as the time that `c: clock_gettime` reports.
    Startup still reads such bytes as an eight-byte integer and mixes
    them into a random key, and it stores the key back over them. The
    rules below read and write eight owned bytes whatever their values. *)

Section loads.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{Hstable : !SafepointStable wi} (ge : genv).
Local Instance load_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ := nanofil_irisGS registry wi ge.
Local Notation lexpr := (language.expr (nanofil_lang registry ge)).

(** An eight-byte load from owned bytes bs yields the little-endian
    integer that bs spell, through a writable or read-only capability. *)
Lemma wp_raw_load_long_bytes f e ls l d k off args rest j classes p b reg o bs Φ :
  op_arg_classes (RawLoad LdL off) k = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr p] ->
  length bs = 8%nat -> ptr_cap p = Obj b \/ ptr_cap p = Ro b -> raw_address (ptr_addr p) off = b + o ->
  live b reg -∗ bytes b o bs -∗
  ▷ (live b reg -∗ bytes b o bs -∗
     WP (ERun (mkFrame f (put d (WInt (of_bytes bs)) e) ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d k (RawLoad LdL off) args :: rest) j)) : lexpr) {{ Φ }}.
Proof using Hstable.
  intros Hc Hx Hlen Hp Ha. iIntros "Hl Hb HK".
  iApply (wp_read_with _ _ _ (live b reg ∗ bytes b o bs)
            (fun m => live_at m b reg /\ all_agree m (byte_ps b o bs)) _ _ [] with "[$Hl $Hb] [HK]").
  - iIntros (σ) "Hσ [Hl Hb]".
    iDestruct (pts_facts with "Hσ Hl") as %([Hlv _] & _).
    iDestruct (pts_facts with "Hσ Hb") as %(Hbs & _). iPureIntro. auto.
  - intros m fuel (Hlv & Hbs).
    destruct (lookup_lt_is_Some_2 bs 0 ltac:(lia)) as [x0 H0].
    destruct (lookup_lt_is_Some_2 bs (length bs - 1) ltac:(lia)) as [x1 H1].
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H0) as (_ & Hlo & _).
    destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hbs H1) as (_ & _ & Hhi).
    apply rule_let with (classes := classes) (xs := [WPtr p]); [reflexivity | exact Hc | exact Hx |].
    rewrite (op_raw_load m k p off).
    + rewrite Ha. replace 8 with (Z.of_nat (length bs)) by (rewrite Hlen; reflexivity).
      rewrite (bytes_load m b reg o bs Hlv Hbs). reflexivity.
    + rewrite Ha. apply (access_read _ b reg); [exact Hp | exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
  - iNext. iIntros "[Hl Hb]". iApply ("HK" with "Hl Hb").
Qed.

(** An eight-byte store over owned bytes bs, whatever their values,
    leaves the little-endian bytes of the stored integer. *)
Lemma wp_raw_store_long_bytes f e ls l off v a rest j p b reg o xs y Φ :
  value_x ge e L v = Some (WInt y) -> value_x ge e A a = Some (WPtr p) ->
  ptr_cap p = Obj b -> raw_address (ptr_addr p) off = b + o -> length xs = 8%nat ->
  (forall m wd h, (forall l v, (l, v) ∈ (PLive b, VLive reg) :: byte_ps b o xs -> h !! l = Some v) ->
     wi m wd h ->
     wi (store_bytes m (b + o) 8 y) wd (overwrite ((PLive b, VLive reg) :: byte_ps b o (le_bytes y 8)) h)) ->
  live b reg -∗ bytes b o xs -∗
  ▷ (live b reg -∗ bytes b o (le_bytes y 8) -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : lexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Wl off v a :: rest) j)) : lexpr) {{ Φ }}.
Proof using Hstable.
  intros Hv Ha Hp Hoff Hlen Hwi. iIntros "Hl Hx HK".
  iApply (wp_write _ _ _ ((PLive b, VLive reg) :: byte_ps b o xs) ((PLive b, VLive reg) :: byte_ps b o (le_bytes y 8))
            _ _ [] (fun m => store_bytes m (b + o) 8 y) with "[Hl Hx] [HK]");
    [cbn [fmap list_fmap fst]; rewrite !byte_ps_keys length_le_bytes Hlen; reflexivity | | exact Hwi |
     rewrite /live /bytes /pts !big_sepL_cons big_sepL_nil; iFrame; iDestruct "Hl" as "[$ _]" |].
  - intros m fuel (Hf & Hd & _). cbn [all_agree agree_piece fst snd] in Hf. destruct Hf as [Hlv Hx].
    destruct (store_after m b reg o xs y Hd Hlv Hx) as [Hag Hfr]. rewrite Hlen in Hag Hfr. cbn in Hag, Hfr.
    assert (Hb : forall i, (i < 8)%nat -> 0 <= o + Z.of_nat i /\ b + (o + Z.of_nat i) < r_end reg).
    { intros i Hi. rewrite <- Hlen in Hi. destruct (lookup_lt_is_Some_2 xs i Hi) as [x Hxi].
      destruct (byte_ps_agree _ _ _ _ _ _ _ Hlv Hx Hxi) as (_ & H1 & H2). lia. }
    destruct (Hb 0%nat ltac:(lia)) as [H0 _]. destruct (Hb 7%nat ltac:(lia)) as [_ H7]. cbn in H0, H7.
    split; [|split; [reflexivity|split; [|split]]].
    + apply rule_raw_store with (vk := L) (x := WInt y) (p := p); [reflexivity | exact Hv | exact Ha |].
      rewrite Hoff. apply store_res_long. rewrite Hp.
      apply (access_obj _ _ reg); [exact (proj1 Hlv) | lia | lia | apply Z.mod_1_r].
    + apply store_bytes_kept. intros a' Ha'. exists b, reg. split; [exact (proj1 Hlv)|lia].
    + cbn [all_agree agree_piece fst snd]. split; [exact Hlv | exact Hag].
    + intros l' v' Hn Ha'. apply Hfr; [|exact Ha'].
      intros Hin. apply Hn. cbn [fmap list_fmap fst]. apply elem_of_cons. right.
      rewrite byte_ps_keys length_le_bytes. rewrite byte_ps_keys Hlen in Hin. exact Hin.
  - iNext. iIntros "H".
    iDestruct (pts_app [(PLive b, VLive reg)] (byte_ps b o (le_bytes y 8)) with "H") as "[Hl Hx]".
    iApply ("HK" with "Hl Hx").
Qed.

End loads.
