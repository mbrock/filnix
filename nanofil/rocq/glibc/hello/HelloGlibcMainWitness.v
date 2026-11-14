(** This file checks that the concrete stream and allocator resources
    used by Hello can coexist. A finite heap contains three empty narrow
    streams with separate locks and an idle allocation prelude. Its keys
    are distinct, so Iris can allocate all these resources together.

    This witness checks the resource contracts, not the remaining M4 and
    M6 call proofs. It does not claim to construct HelloDebts. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld FileInv AllocLogic AtexitLogic HelloGlibcDebts HelloGlibcLibsT.
From stdpp Require Import list.
From Glibc Require AllocLogic FileInv.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

(** A fixture object occupies one page of global data. *)
Definition hello_witness_region (b : Z) : region := mkRegion b (b + 4096) GlobalData Live.

(** A pointer cell owns its capability slot and its eight address bytes. *)
Definition hello_witness_pointer (b o : Z) (p : ptr) : list (piece * pval) :=
  (PAux b o, VAux (ptr_cap p)) :: cell b o (ptr_addr p).

(** This comparison computes without constructing equality proofs for every byte. *)
Definition hello_witness_same (x y : piece) : bool :=
  match x, y with
  | PLive b, PLive c => b =? c
  | PByte b o, PByte c p | PAux b o, PAux c p => (b =? c) && (o =? p)
  | PName _, PName _ => true
  | _, _ => false
  end.

(** The finite check rejects a key whenever an equal key occurs later. *)
Fixpoint hello_witness_unique (xs : list piece) : bool :=
  match xs with
  | [] => true
  | x :: xs => negb (existsb (hello_witness_same x) xs) && hello_witness_unique xs
  end.

(** Passing the finite check establishes distinct ownership keys. *)
Lemma hello_witness_unique_sound xs : hello_witness_unique xs = true -> NoDup xs.
Proof.
  induction xs as [|x xs IH]; [constructor|]. cbn. rewrite Bool.andb_true_iff Bool.negb_true_iff.
  intros [Hnot Hxs]. constructor; [|exact (IH Hxs)]. intros Hin.
  assert (Hsame : hello_witness_same x x = true) by (destruct x; cbn; rewrite ?Z.eqb_refl; reflexivity).
  assert (Hex : existsb (hello_witness_same x) xs = true).
  { apply existsb_exists. exists x. split; [apply list_elem_of_In; exact Hin|exact Hsame]. }
  congruence.
Qed.


(** The stream witness uses the existing file invariant without weakening it. *)
(** The allocation witness uses the existing idle-prelude predicate. *)
Import LG0 LG0.L FileInv FileInv.ML.

(** The stream starts unoriented, with no buffer and a free lock. *)
Definition hello_witness_state (vb lb fd : Z) : fstate :=
  mkFstate (io_magic + io_is_filebuf) (replicate 12 null) fd 0 (2 ^ 64 - 1)
    (replicate 8 0) (mkPtr lb (Obj lb)) (2 ^ 64 - 1) null null null null 0 0
    (mkPtr (vb + vt_file) (Ro vb)).

(** The field image uses precisely the cells owned by file_fields. *)
Definition hello_witness_fields (fb : Z) (st : fstate) : list (piece * pval) :=
  concat [byte_ps fb off_flags (int_bytes (fs_flags st));
    concat (imap (fun i p => hello_witness_pointer fb (off_ptr i) p) (fs_ptrs st));
    byte_ps fb off_fileno (int_bytes (fs_fileno st));
    byte_ps fb off_flags2 (int_bytes (fs_flags2 st)); cell fb off_old_offset (fs_old_offset st);
    byte_ps fb off_column (fs_column st); hello_witness_pointer fb off_lock (fs_lock st);
    cell fb off_offset (fs_offset st); hello_witness_pointer fb off_codecvt (fs_codecvt st);
    hello_witness_pointer fb off_wide (fs_wide st);
    hello_witness_pointer fb off_freeres_list (fs_freeres_list st);
    hello_witness_pointer fb off_freeres_buf (fs_freeres_buf st);
    byte_ps fb off_mode (int_bytes (fs_mode st)); cell fb off_total_written (fs_total st);
    hello_witness_pointer fb off_vtable (fs_vtable st)].

(** Each stream owns a separate page and a separate unlocked lock. *)
Definition hello_witness_file (fb vb lb fd : Z) : list (piece * pval) :=
  concat [[(PLive fb, VLive (hello_witness_region fb))];
    hello_witness_fields fb (hello_witness_state vb lb fd);
    [(PLive lb, VLive (hello_witness_region lb))];
    byte_ps lb 0 (int_bytes 0); byte_ps lb 4 (int_bytes 0); hello_witness_pointer lb 8 null].

(** The allocation prelude reads three separate pages and sixty-four null bins. *)
Definition hello_witness_alloc : list (piece * pval) :=
  concat [[(PLive 32768, VLive (hello_witness_region 32768))]; cell 32768 120 1041;
    [(PLive 36864, VLive (hello_witness_region 36864))];
    hello_witness_pointer 36864 0 (mkPtr 40960 (Ro 40960));
    [(PLive 40960, VLive (hello_witness_region 40960))];
    concat ((fun i => hello_witness_pointer 40960 (152 + 8 * i) null) <$> seqZ 0 64)].

(** All three standard streams coexist with the idle allocator. *)
Definition hello_witness_pieces : list (piece * pval) :=
  concat [hello_witness_file 4096 16384 20480 1; hello_witness_file 8192 16384 24576 2;
    hello_witness_file 12288 16384 28672 0; hello_witness_alloc].

(** No field or life token occurs twice in the combined fixture. *)
Lemma hello_witness_distinct : NoDup hello_witness_pieces.*1.
Proof. apply hello_witness_unique_sound. vm_compute. reflexivity. Qed.

(** The exit-state pages are separate from the errno page. *)
Definition hello_witness_objects : hello_objs :=
  mkHelloObjs (mkPtr 4096 (Obj 4096)) (mkPtr 8192 (Obj 8192)) (mkPtr 12288 (Obj 12288))
    106496 (hello_witness_region 106496) 110592 (hello_witness_region 110592)
    114688 (hello_witness_region 114688) 118784 (hello_witness_region 118784)
    16384 (hello_witness_region 16384) 98304 (hello_witness_region 98304) 49152 (hello_witness_region 49152)
    (mkExitObjs 61440 (hello_witness_region 61440) 65536 (hello_witness_region 65536)
      69632 (hello_witness_region 69632) 73728 (hello_witness_region 73728)
      77824 (hello_witness_region 77824))
    81920 (hello_witness_region 81920) null null
    32768 (hello_witness_region 32768) 36864 (hello_witness_region 36864)
    40960 (hello_witness_region 40960) 122880 126976 131072
    (hello_witness_region 122880) (hello_witness_region 126976) (hello_witness_region 131072)
    (mkPtr 135168 (Ro 135168)) (mkPtr 139264 (Ro 139264)).

(** The world has a real errno pointer, a non-null thread cookie and standard descriptors. *)
Definition hello_witness_world : os_world :=
  mkOsWorld (Some (mkPtr 49152 (Obj 49152))) (mkPtr 53248 (Obj 53248)) None [0; 1; 2].

(** The additional OS layout premise has an explicit concrete instance. *)
Lemma hello_witness_os_layout : hello_os_layout hello_witness_world hello_witness_objects.
Proof.
  split; [vm_compute; intuition congruence|]. intros p Hp b Hb. injection Hp as <-.
  cbn in Hb |- *. repeat destruct Hb as [<- | Hb]; try contradiction; lia.
Qed.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** Ownership of a concatenation splits into ownership of its component images. *)
Lemma witness_concat pss : pts (concat pss) ⊣⊢ [∗ list] ps ∈ pss, pts ps.
Proof. induction pss as [|ps pss IH]; cbn [concat]; rewrite ?pts_app ?IH; done. Qed.

(** Read-only images split into the same disjoint component images. *)
Lemma witness_concatq dq pss : ptsq dq (concat pss) ⊣⊢ [∗ list] ps ∈ pss, ptsq dq ps.
Proof. induction pss as [|ps pss IH]; cbn [concat]; rewrite ?ptsq_app ?IH; done. Qed.

(** Indexed field images keep the same indices when their ownership is split. *)
Lemma witness_imap {A} (f : nat -> A -> list (piece * pval)) ps :
  pts (concat (imap f ps)) ⊣⊢ [∗ list] i ↦ p ∈ ps, pts (f i p).
Proof.
  revert f. induction ps as [|p ps IH]; intros f; cbn [imap concat];
    rewrite ?pts_app ?big_sepL_cons ?IH; done.
Qed.

(** Concatenating pointer images gives ownership of every pointer cell. *)
Lemma witness_pointers fb ps :
  pts (concat (imap (fun i p => hello_witness_pointer fb (off_ptr i) p) ps)) ⊣⊢
  [∗ list] i ↦ p ∈ ps, pcell fb (off_ptr i) p.
Proof.
  rewrite witness_imap /pcell /hello_witness_pointer. done.
Qed.

(** The finite field image establishes all fields of the initialized stream. *)
Lemma witness_fields fb vb lb fd : 0 <= fd < 2 ^ 32 ->
  pts (hello_witness_fields fb (hello_witness_state vb lb fd)) -∗
  file_fields fb (hello_witness_state vb lb fd).
Proof.
  intros Hfd. rewrite /hello_witness_fields witness_concat. cbn [big_opL]. rewrite witness_pointers.
  rewrite /file_fields /hello_witness_state.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset
    fs_codecvt fs_wide fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable].
  iIntros "(Hfl & Hps & Hfd & Hf2 & Hold & Hcol & Hlk & Hoff & Hcv & Hwd & Hfrl & Hfrb & Hmd & Htotal & Hvt & _)".
  iSplit; [done|].
  iSplitL "Hfl"; [iSplit; [iPureIntro; vm_compute; intuition congruence|iExact "Hfl"]|].
  iSplitL "Hps"; [iExact "Hps"|].
  iSplitL "Hfd"; [iSplit; [done|iExact "Hfd"]|].
  iSplitL "Hf2"; [iSplit; [iPureIntro; lia|iExact "Hf2"]|].
  iSplitL "Hold"; [iExact "Hold"|]. iSplit; [done|].
  iSplitL "Hcol"; [iExact "Hcol"|].
  iSplitL "Hlk"; [iExact "Hlk"|]. iSplitL "Hoff"; [iExact "Hoff"|].
  iSplitL "Hcv"; [iExact "Hcv"|]. iSplitL "Hwd"; [iExact "Hwd"|].
  iSplitL "Hfrl"; [iExact "Hfrl"|]. iSplitL "Hfrb"; [iExact "Hfrb"|].
  iSplitL "Hmd"; [iSplit; [iPureIntro; lia|iExact "Hmd"]|].
  iSplitL "Htotal"; [iExact "Htotal"|]. iExact "Hvt".
Qed.

(** The initialized empty stream satisfies the original whole-stream invariant. *)
Lemma witness_file fb vb lb fd self :
  0 < fb -> fb mod 8 = 0 -> fb + 4096 <= 2 ^ 63 ->
  lb mod 8 = 0 -> lb + 4096 <= 2 ^ 63 -> 0 <= fd < 2 ^ 32 ->
  pts (hello_witness_file fb vb lb fd) -∗ file_inv vb self (mkPtr fb (Obj fb)).
Proof.
  intros Hfb Hfa Hfe Hla Hle Hfd. rewrite /hello_witness_file witness_concat. cbn [big_opL].
  iIntros "(Hf & Hfields & Hl & Hlk & Hcnt & Howner & _)".
  iExists fb, (hello_witness_region fb), (hello_witness_state vb lb fd), NbNone, vt_file, None.
  iSplit.
  { iPureIntro. split; [reflexivity|]. split; [exact Hfa|]. split; [exact Hfb|].
    split; [change (fb + 224 <= fb + 4096); lia|]. split; [exact Hfe|].
    split; [vm_compute; intuition congruence|]. split; [left; split; [left|]; reflexivity|].
    split; reflexivity. }
  iFrame "Hf". iSplitL "Hfields"; [iApply (witness_fields with "Hfields"); exact Hfd|].
  iSplitL; [|done]. iExists lb, (hello_witness_region lb). iSplit; [done|].
  iSplit; [iPureIntro; cbn; lia|]. iFrame "Hl Howner".
  rewrite /int_cell /bytes. iSplitL "Hlk"; iSplit; try iPureIntro; try lia; iAssumption.
Qed.

(** The allocator image supplies the full-share idle-prelude predicate. *)
Lemma witness_alloc : pts hello_witness_alloc -∗
  AllocLogic.tcache_idle (DfracOwn 1) 32768 36864 40960
    (hello_witness_region 32768) (hello_witness_region 36864) (hello_witness_region 40960).
Proof.
  rewrite /hello_witness_alloc witness_concat /AllocLogic.tcache_idle. cbn [big_opL].
  iIntros "(Hmp & Hmax & Htc & Hptr & Hdm & Hbins & _)". iSplit; [iPureIntro; vm_compute; intuition congruence|].
  iFrame "Hmp Hmax Htc Hptr Hdm".
  rewrite witness_concat big_sepL_fmap /pcellq /hello_witness_pointer. done.
Qed.

(** Giving up the allocator image produces exactly the read-only prelude used by Hello. *)
Lemma witness_alloc_readonly : pts hello_witness_alloc ==∗
  AllocLogic.tcache_idle DfracDiscarded 32768 36864 40960
    (hello_witness_region 32768) (hello_witness_region 36864) (hello_witness_region 40960).
Proof.
  iIntros "Ha". iMod (ptsq_persist (DfracOwn 1) with "Ha") as "#Ha". iModIntro.
  rewrite /hello_witness_alloc witness_concatq /AllocLogic.tcache_idle. cbn [big_opL].
  iDestruct "Ha" as "(Hmp & Hmax & Htc & Hptr & Hdm & Hbins & _)".
  iSplit; [iPureIntro; vm_compute; intuition congruence|]. iFrame "Hmp Hmax Htc Hptr Hdm".
  rewrite witness_concatq big_sepL_fmap /pcellq /hello_witness_pointer. done.
Qed.

(** The combined finite image supplies all streams and the allocator together. *)
Lemma witness_resources : pts hello_witness_pieces -∗
  file_inv 16384 (ow_self hello_witness_world) (mkPtr 4096 (Obj 4096)) ∗
  file_inv 16384 (ow_self hello_witness_world) (mkPtr 8192 (Obj 8192)) ∗
  file_inv 16384 (ow_self hello_witness_world) (mkPtr 12288 (Obj 12288)) ∗
  AllocLogic.tcache_idle (DfracOwn 1) 32768 36864 40960
    (hello_witness_region 32768) (hello_witness_region 36864) (hello_witness_region 40960).
Proof.
  rewrite /hello_witness_pieces witness_concat. cbn [big_opL]. iIntros "(Ho & He & Hi & Ha & _)".
  iSplitL "Ho"; [iApply (witness_file with "Ho"); vm_compute; intuition congruence|].
  iSplitL "He"; [iApply (witness_file with "He"); vm_compute; intuition congruence|].
  iSplitL "Hi"; [iApply (witness_file with "Hi"); vm_compute; intuition congruence|].
  iApply (witness_alloc with "Ha").
Qed.
End resources.

(** Iris can create the combined resources from the explicit finite heap.
    This establishes satisfiability rather than assuming resource ownership. *)
Lemma witness_allocatable Σ `{!gen_heapGpreS piece pval Σ} :
  ⊢ |==> ∃ Hh : gen_heapGS piece pval Σ,
    @FileInv.file_inv Σ Hh 16384 (ow_self hello_witness_world) (mkPtr 4096 (Obj 4096)) ∗
    @FileInv.file_inv Σ Hh 16384 (ow_self hello_witness_world) (mkPtr 8192 (Obj 8192)) ∗
    @FileInv.file_inv Σ Hh 16384 (ow_self hello_witness_world) (mkPtr 12288 (Obj 12288)) ∗
    @AllocLogic.tcache_idle Σ Hh (DfracOwn 1) 32768 36864 40960
      (hello_witness_region 32768) (hello_witness_region 36864) (hello_witness_region 40960).
Proof.
  iMod (gen_heap_init (list_to_map hello_witness_pieces : gmap piece pval)) as (Hh) "(_ & Hpts & _)".
  iModIntro. iExists Hh. iApply witness_resources.
  rewrite /pts -(big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v));
    [iExact "Hpts"|exact hello_witness_distinct].
Qed.
