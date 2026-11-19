(** The parser's private state must come from real storage rather than an
    assumed library invariant. This file checks the zeroed object in the
    image that the loader builds for the getopt module alone, and it
    constructs ownership of all the fields the parser reads. The same
    fields at any other base describe the object wherever a linker puts
    it. Argument storage, diagnostics and the parser transition remain
    separate obligations; this is not a complete program-entry theorem. *)

From Glibc Require Import OsMemLogic WordString LiteralWords ImageData GlibcTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Run Pieces Heap Logic StringLogic MemLogic.
From Glibc Require Import GetoptModule GetoptState.
From stdpp Require Import list.
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

(** The private parser object occupies 56 bytes in the getopt module's own image. *)
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


(** ## The zeroed object at any base

    A linked program may put the parser's object at another address. The
    fields keep their offsets there, so one list describes the zeroed
    object at every base, and the loader's object is its instance. *)

(** The zeroed object at base b with region r has these fields. *)
Definition getopt_zero_ps (b : Z) (r : region) : list (piece * pval) :=
  concat [[(PLive b, VLive r)];
    byte_ps b 0 (le_bytes 0 4); byte_ps b 4 (le_bytes 0 4);
    byte_ps b 8 (le_bytes 0 4);
    (PAux b 16, VAux CNone) :: cell b 16 0;
    byte_ps b 24 (le_bytes 0 4);
    (PAux b 32, VAux CNone) :: cell b 32 0;
    byte_ps b 40 (le_bytes 0 4); byte_ps b 44 (le_bytes 0 4);
    byte_ps b 48 (le_bytes 0 4)].

(** The loader's object is the zeroed object at its own base. *)
Lemma getopt_private_zero_ps : getopt_private_pieces = getopt_zero_ps 65584 getopt_private_region.
Proof. reflexivity. Qed.

(** The field keys differ at every base, because only their offsets vary. *)
Lemma getopt_zero_ps_distinct b r : NoDup (getopt_zero_ps b r).*1.
Proof.
  apply (NoDup_fmap_1 (fun p => match p with
    | PByte _ o => 2 * o + 1 | PAux _ o => 2 * o + 2 | _ => 0 end)).
  apply (bool_decide_unpack _). vm_compute. exact I.
Qed.

(** ## The public flags

    The parser also writes the public integers opterr and optopt. glibc
    initializes opterr to 1 and optopt to the question mark, 63. One list
    describes such an integer object at any base. *)

(** The integer object at base b with region r holds v in its first four bytes. *)
Definition int_global_ps (b : Z) (r : region) (v : Z) : list (piece * pval) :=
  (PLive b, VLive r) :: byte_ps b 0 (le_bytes v 4).

(** The getopt module's own image puts opterr and optopt at these objects. *)
Lemma getopt_flag_layout :
  Term.lookup (TAtom "opterr") getopt_globals = Some (mkPtr 65696 (Obj 65696)) /\
  Term.lookup (TAtom "optopt") getopt_globals = Some (mkPtr 65760 (Obj 65760)) /\
  object_region 65696 (m_regions getopt_memory) = Some (mkRegion 65696 65704 GlobalData Live) /\
  object_region 65760 (m_regions getopt_memory) = Some (mkRegion 65760 65768 GlobalData Live).
Proof. vm_compute. split_and!; reflexivity. Qed.

(** Those objects hold glibc's initial values 1 and 63. *)
Lemma getopt_flag_agrees : all_agree getopt_memory
  (int_global_ps 65696 (mkRegion 65696 65704 GlobalData Live) 1 ++
   int_global_ps 65760 (mkRegion 65760 65768 GlobalData Live) 63).
Proof. apply checked_pieces_all_agree. vm_compute. reflexivity. Qed.

(** The session module supplies the private-field representation. *)
Import GetoptState Fix.ML0 Fix.LG0 Fix.LG0.L.

Section resources.
Context `{!gen_heapGS piece pval Σ}.

(** The parser can own its fields together because they occupy separate
    parts of the initial image. *)
Lemma getopt_private_own : pts getopt_private_pieces ⊢
  getopt_state_own 65584 getopt_private_region getopt_zero.
Proof using Type.
  rewrite /getopt_private_pieces /concat !pts_app.
  iIntros "(Hl & Hi & He & Ho & Ha & Hz & Hn & Hr & Hf & Ht & _)".
  rewrite /getopt_state_own /getopt_zero /=.
  iSplitR; [iPureIntro; vm_compute; intuition congruence|].
  iFrame "Hl Ha Hn". rewrite /int_cell /int_bytes /bytes.
  iFrame. repeat iSplit; iPureIntro; lia.
Qed.

(** The zeroed fields at an aligned base give the parser its fresh state. *)
Lemma getopt_zero_ps_own b r : 0 < b -> b mod 8 = 0 -> b + 56 <= r_end r -> r_end r <= 2 ^ 48 ->
  pts (getopt_zero_ps b r) ⊢ getopt_state_own b r getopt_zero.
Proof using Type.
  intros Hb H8 He Hr. rewrite /getopt_zero_ps /concat !pts_app.
  iIntros "(Hl & Hi & He & Ho & Ha & Hz & Hn & Hr & Hf & Ht & _)".
  rewrite /getopt_state_own /getopt_zero /=.
  iSplitR; [iPureIntro; lia|].
  iFrame "Hl Ha Hn". rewrite /int_cell /int_bytes /bytes.
  iFrame. repeat iSplit; iPureIntro; lia.
Qed.

(** The pieces of an integer object give the cell that the parser writes. *)
Lemma int_global_own b r v : 0 <= v < 2 ^ 32 -> pts (int_global_ps b r v) ⊢ live b r ∗ int_cell b 0 v.
Proof using Type.
  intros Hv. rewrite /int_global_ps (pts_app [_]). iIntros "[Hl Hb]".
  iFrame "Hl". rewrite /int_cell /int_bytes /bytes. iFrame "Hb". iPureIntro. exact Hv.
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


(** ## glibc's objects at startup

    Before Hello's first call, glibc's parser has written nothing. Its
    private object holds zeroes, opterr holds 1 and optopt holds the
    question mark. The strings are constant. *)

(** These are the fields of glibc's objects that the parser uses, at the
    bases that the linked program chose. *)
Definition getopt_start_ps (gb : Z) (greg : region) (oe : Z) (roe : region) (oo : Z) (roo : region)
    (bdd : Z) (rdd : region) (b7 : Z) (r7 : region) (b0 : Z) (r0 : region) : list (piece * pval) :=
  getopt_zero_ps gb greg ++ int_global_ps oe roe 1 ++ int_global_ps oo roo 63 ++
  lit_ps bdd rdd (lit_words [45; 45]) ++ lit_ps b7 r7 (lit_words [45]) ++ lit_ps b0 r0 (lit_words [45; 87; 32]).

(** This checks glibc's own pieces and nothing else. When the getopt
    module is loaded on its own, its memory holds exactly these values,
    each at its own key. It does not show that Hello's, the backends' and
    startup's other assumptions can hold in the same memory, and the
    linked program may put these objects elsewhere. *)
Lemma getopt_start_fixture :
  let ps := getopt_start_ps 65584 getopt_private_region 65696 (gd 65696 65704) 65760 (gd 65760 65768)
    66176 (gd 66176 66184) 66208 (gd 66208 66216) 66352 (gd 66352 66360) in
  all_agree getopt_memory ps /\ NoDup ps.*1.
Proof.
  cbn zeta. split.
  - apply checked_pieces_all_agree. unfold getopt_memory. vm_compute. reflexivity.
  - apply (NoDup_fmap_1 (fun p => match p with
      | PLive b => 4 * 512 * b | PByte b o => 4 * (512 * b + o) + 1
      | PAux b o => 4 * (512 * b + o) + 2 | _ => 3 end)).
    apply (bool_decide_unpack _). vm_compute. exact I.
Qed.
