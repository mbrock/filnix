(** The parser's private state must come from real storage rather than an
    assumed library invariant. This file checks the zeroed object in the
    linked getopt image and constructs ownership of all its accessed fields.
    Argument storage, diagnostics and the parser transition remain separate
    obligations; this is not a complete program-entry theorem. *)

From Glibc Require Import GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import GetoptModule GetoptState.
From stdpp Require Import list.
From Glibc Require FileInv GetoptState.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Transparent getopt_module.

(** The loader computes both symbols and memory from the generated module. *)
Definition getopt_globals : list (name * ptr) := Eval vm_compute in
  match initial_memory getopt_module with Some (g, _) => g | None => [] end.
(** This image retains the loader's bytes and capability slots unchanged. *)
Definition getopt_memory : mem :=
  match initial_memory getopt_module with Some (_, m) => m | None => empty_mem end.

(** Checking the symbols forces successful layout without expanding memory functions. *)
Lemma getopt_initial_layout : option_map fst (initial_memory getopt_module) = Some getopt_globals.
Proof. vm_compute. reflexivity. Qed.

(** The loader succeeds for this fixture rather than selecting the fallback. *)
Lemma getopt_initial_memory : initial_memory getopt_module = Some (getopt_globals, getopt_memory).
Proof.
  pose proof getopt_initial_layout as H. unfold getopt_memory.
  destruct (initial_memory getopt_module) as [[g m]|]; inversion H; reflexivity.
Qed.

(** The private parser object occupies 56 bytes in the actual linked image. *)
Definition getopt_private_region : region := mkRegion 65584 65640 GlobalData Live.

(** The symbol and region identify the same private storage. *)
Lemma getopt_private_layout :
  Term.lookup (TAtom "glibc_getopt#getopt_data") getopt_globals = Some (mkPtr 65584 (Obj 65584)) /\
  object_region 65584 (m_regions getopt_memory) = Some getopt_private_region.
Proof. vm_compute. split; reflexivity. Qed.

(** The private image records integer bytes, both pointer capabilities, and
    the lifetime of the object. Unused padding is not claimed by the parser. *)
Definition getopt_private_pieces : list (piece * pval) :=
  concat [[(PLive 65584, VLive getopt_private_region)];
    byte_ps 65584 0 (le_bytes 0 4); byte_ps 65584 4 (le_bytes 0 4);
    byte_ps 65584 8 (le_bytes 0 4);
    (PAux 65584 16, VAux CNone) :: cell 65584 16 0;
    byte_ps 65584 24 (le_bytes 0 4);
    (PAux 65584 32, VAux CNone) :: cell 65584 32 0;
    byte_ps 65584 40 (le_bytes 0 4); byte_ps 65584 44 (le_bytes 0 4);
    byte_ps 65584 48 (le_bytes 0 4)].

(** Every claimed field agrees with the unmodified loader image. *)
Lemma getopt_private_agrees : all_agree getopt_memory getopt_private_pieces.
Proof. apply checked_pieces_all_agree. vm_compute. reflexivity. Qed.

(** Distinct field keys allow Iris to allocate their ownership together. *)
Lemma getopt_private_distinct : NoDup getopt_private_pieces.*1.
Proof.
  apply (NoDup_fmap_1 (fun p => match p with
    | PByte _ o => 2 * o + 1 | PAux _ o => 2 * o + 2 | _ => 0 end)).
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.


(** The session module supplies the private-field representation. *)
Import GetoptState FileInv FileInv.ML FileInv.LG FileInv.L.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** The parser can own its fields together because they occupy separate
    parts of the initial image. *)
Lemma getopt_private_own : pts getopt_private_pieces ⊢
  getopt_state_own 65584 getopt_private_region getopt_zero.
Proof.
  rewrite /getopt_private_pieces /concat !pts_app.
  iIntros "(Hl & Hi & He & Ho & Ha & Hz & Hn & Hr & Hf & Ht & _)".
  rewrite /getopt_state_own /getopt_zero /=.
  iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  iFrame "Hl Ha Hn". rewrite /int_cell /int_bytes /bytes.
  iFrame. repeat iSplit; iPureIntro; lia.
Qed.

End resources.

(** The parser's initial ownership can be constructed rather than assumed.
    The allocated fields agree with the loader's memory, but this theorem
    does not construct ownership of the rest of the program. *)
Lemma getopt_private_allocatable Σ `{!gen_heapGpreS piece pval Σ} :
  ⊢ |==> ∃ Hh : gen_heapGS piece pval Σ,
    @getopt_state_own Σ Hh 65584 getopt_private_region getopt_zero.
Proof.
  iMod (gen_heap_init (list_to_map getopt_private_pieces : gmap piece pval)) as (Hh) "(_ & Hpts & _)".
  iModIntro. iExists Hh. iApply getopt_private_own.
  rewrite /pts -(big_sepM_list_to_map (fun l v => pointsto l (DfracOwn 1) v));
    [iExact "Hpts"|exact getopt_private_distinct].
Qed.

