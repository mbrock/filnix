(** * Reading getopt's libc cells

    A program reads `optarg` and `optind` straight from libc's cells,
    which getopt rewrites at every call. The program owns neither cell:
    it owns a ghost token, [getopt_ps], naming the values getopt last
    left there, and the world interpretation ties the token to the
    world's getopt state and the cells' memory ([getopt_current],
    Campaign 4's [getopt_state_at]). A read of either cell is then an
    instruction whose result the world interpretation fixes
    ([wp_world_let_with]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import ZArith Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run StepRules
  ExternalCalls ExternalMachine Pieces Heap Language Logic Startup Getopt.
Open Scope Z_scope.
Open Scope list_scope.

(** The key of the getopt token: no locale category's, not the codec's
    (-1), and no stream's (below -1). *)
Definition getopt_key : Z := 64.

(** The getopt token: optarg a and optind i. *)
Definition getopt_ps (a : ptr) (i : Z) : list (piece * pval) := [(PName getopt_key, VGetopt a i)].

(** The getopt token of h, if any, holds the getopt state g's optarg and
    optind. *)
Definition getopt_current (g : getopt_world) (h : gmap piece pval) : Prop :=
  forall a i, h !! PName getopt_key = Some (VGetopt a i) -> getopt_optarg g = a /\ getopt_optind g = i.

(** A read access that passes at some alignment passes at alignment 1. *)
Lemma access_read_align1 m a c size al :
  access_res m a c size Read al = Some ok -> access_res m a c size Read 1 = Some ok.
Proof.
  unfold access_res, cap_access_res, readonly_access_res, aligned_res.
  destruct c as [|b|b|g|g]; try discriminate; destruct (object_region b (m_regions m)); try discriminate;
    destruct (_ && _); try discriminate; rewrite Z.mod_1_r; reflexivity.
Qed.

(** Sign extension, cut back to its width, is the value cut to it. *)
Lemma sign_extension_mod md hf x : 0 < md -> sign_extension md hf x mod md = x mod md.
Proof.
  intros Hm. unfold sign_extension. destruct (hf <=? x mod md).
  - replace (x mod md - md) with (x mod md + (-1) * md) by lia. rewrite Z.mod_add; [|lia].
    apply Z.mod_mod. lia.
  - apply Z.mod_mod. lia.
Qed.

(** A raw signed 32-bit load at offset off from the proven pointer p,
    whose read access passes: the four bytes there, as a W word. *)
Lemma op_raw_load_sw m p off :
  access_res m (raw_address (ptr_addr p) off) (ptr_cap p) 4 Read 1 = Some ok ->
  op_res (RawLoad (LdNarrow Sw) off) W [WPtr p] m =
  Some (OpRes (RVal (WInt (load_bytes m (raw_address (ptr_addr p) off) 4 mod 2 ^ 32))) m).
Proof.
  intros H.
  assert (E : op_res (RawLoad (LdNarrow Sw) off) W [WPtr p] m =
              op_res_int (RawLoad (LdNarrow Sw) off) W [WPtr p] m) by reflexivity.
  rewrite E. cbn - [access_res raw_address load_bytes extended]. unfold int_load_res.
  cbn - [access_res raw_address load_bytes extension]. rewrite H.
  cbn - [raw_address load_bytes extension]. rewrite sign_extension_mod; [|lia].
  reflexivity.
Qed.

(** A pointer cell whose pieces agree with the memory, in a live object,
    holding a word-sized address whose capability's object is not
    freed, is a [pointer_slot] there: Campaign 4's reading of a stored
    pointer. *)
Lemma pcell_slot m b reg o x :
  live_at m b reg -> agree_piece m (PAux b o) (VAux (ptr_cap x)) -> all_agree m (cell b o (ptr_addr x)) ->
  0 <= ptr_addr x < 2 ^ 64 -> ~ freed_in (m_regions m) (ptr_cap x) -> pointer_slot m (b + o) x.
Proof.
  intros Hlv Hax Hcl Hr Hf. split; [exact Hr|]. split.
  - rewrite (cell_load m b reg o (ptr_addr x) (b + o) Hlv Hcl eq_refl). apply Z.mod_small. exact Hr.
  - destruct (cell_bounds _ _ _ _ _ Hlv Hcl) as [Ho He].
    apply aux_holds_kept; [exact (aux_piece_holds _ _ _ _ _ Hlv Hax) | exact Hf].
Qed.

(** Reading getopt's cells over any [[runtime]] R and Logic instance. *)
Module GetoptLogicOn (R : Runtime) (LG0 : LogicSig R).
Module LG := LG0.
Module L := LG.L.
Import L LG.

Section getopt.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).

(** The Iris instance of the registry and wi. *)
Local Instance getopt_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.

(** The expressions of the language. *)
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The world's getopt state, through the projection view, is in the
    memory at the cells optarg_cell and optind_cell, whose addresses are
    words, and the getopt token is current. *)
Context (view : world -> getopt_world) (optarg_cell optind_cell : ptr)
  (Hcells : 0 <= ptr_addr optarg_cell < 2 ^ 64 /\ 0 <= ptr_addr optind_cell < 2 ^ 64)
  (Hgetopt_wi : forall m w h, wi m w h ->
     getopt_state_at m (view w) /\ getopt_optarg_cell (view w) = optarg_cell /\
     getopt_optind_cell (view w) = optind_cell /\ getopt_current (view w) h).

(** The check of optarg's cell for an 8-byte read passes. *)
Lemma wp_optarg_check f e ls l d args rest j classes Φ :
  op_arg_classes (Check 0 8 Read 8) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr optarg_cell] ->
  ▷ WP (ERun (mkFrame f (put d (WPtr optarg_cell) e) ls None (Exec l rest j)) : gexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check 0 8 Read 8) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hx. iIntros "HK".
  iAssert (pts []) as "Hn"; [rewrite /pts; done|].
  iApply (wp_world_let_with registry wi ge [] with "Hn [HK]"); [reflexivity | exact Hc | exact Hx | |].
  - intros m w h Hw _. destruct (Hgetopt_wi _ _ _ Hw) as ((Hpc & _) & Hoc & _ & _).
    apply op_check. unfold raw_address. rewrite Z.add_0_r Z.mod_small; [|lia]. cbn.
    destruct Hpc as (_ & Hacc & _). rewrite Hoc in Hacc. exact Hacc.
  - iNext. iIntros "_". iExact "HK".
Qed.

(** The plain pointer load of optarg's cell: optarg a, as the token
    names it. *)
Lemma wp_optarg_load f e ls l d args rest j classes a i Φ :
  op_arg_classes (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) P = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr optarg_cell] ->
  pts (getopt_ps a i) -∗
  ▷ (pts (getopt_ps a i) -∗ WP (ERun (mkFrame f (put d (WPtr a) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None
       (Exec l (Let d P (RawLoadPointer 0 [AuxRead; LowerResolve; AddressRead]) args :: rest) j)) : gexpr)
    {{ Φ }}.
Proof.
  intros Hc Hx. iIntros "Ht HK".
  iApply (wp_world_let_with with "Ht HK"); [reflexivity | exact Hc | exact Hx |].
  intros m w h Hw Hl. destruct (Hgetopt_wi _ _ _ Hw) as ((Hpc & _) & Hoc & _ & Hcur).
  destruct (Hcur a i (Hl _ _ ltac:(left))) as [Ha _].
  rewrite Hoc Ha in Hpc.
  assert (Er : raw_address (ptr_addr optarg_cell) 0 = ptr_addr optarg_cell).
  { unfold raw_address. rewrite Z.add_0_r. apply Z.mod_small. lia. }
  apply op_raw_load_pointer; rewrite Er.
  - destruct Hpc as (_ & Hacc & _). exact Hacc.
  - exact (exposed_pointer_load _ _ _ Hpc).
Qed.

(** The check of optind's cell for a 4-byte read at alignment 1
    passes. *)
Lemma wp_optind_check f e ls l d args rest j classes Φ :
  op_arg_classes (Check 0 4 Read 1) A = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr optind_cell] ->
  ▷ WP (ERun (mkFrame f (put d (WPtr optind_cell) e) ls None (Exec l rest j)) : gexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check 0 4 Read 1) args :: rest) j)) : gexpr) {{ Φ }}.
Proof.
  intros Hc Hx. iIntros "HK".
  iAssert (pts []) as "Hn"; [rewrite /pts; done|].
  iApply (wp_world_let_with registry wi ge [] with "Hn [HK]"); [reflexivity | exact Hc | exact Hx | |].
  - intros m w h Hw _. destruct (Hgetopt_wi _ _ _ Hw) as ((_ & Hic & _) & _ & Hoc & _).
    apply op_check. unfold raw_address. rewrite Z.add_0_r Z.mod_small; [|lia]. cbn.
    destruct Hic as (_ & _ & Hacc & _). rewrite Hoc in Hacc. exact (access_read_align1 _ _ _ _ _ Hacc).
  - iNext. iIntros "_". iExact "HK".
Qed.

(** The signed 32-bit load of optind's cell: optind i, as the token
    names it, as a W word. *)
Lemma wp_optind_load f e ls l d args rest j classes a i Φ :
  op_arg_classes (RawLoad (LdNarrow Sw) 0) W = Some classes ->
  map2_option (value_x ge e) classes args = Some [WPtr optind_cell] ->
  pts (getopt_ps a i) -∗
  ▷ (pts (getopt_ps a i) -∗
     WP (ERun (mkFrame f (put d (WInt (i mod 2 ^ 32)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d W (RawLoad (LdNarrow Sw) 0) args :: rest) j)) : gexpr)
    {{ Φ }}.
Proof.
  intros Hc Hx. iIntros "Ht HK".
  iApply (wp_world_let_with with "Ht HK"); [reflexivity | exact Hc | exact Hx |].
  intros m w h Hw Hl. destruct (Hgetopt_wi _ _ _ Hw) as ((_ & Hic & _) & _ & Hoc & Hcur).
  destruct (Hcur a i (Hl _ _ ltac:(left))) as [_ Hi].
  rewrite Hoc Hi in Hic. destruct Hic as (_ & _ & Hacc & _ & Hload).
  assert (Er : raw_address (ptr_addr optind_cell) 0 = ptr_addr optind_cell).
  { unfold raw_address. rewrite Z.add_0_r. apply Z.mod_small. lia. }
  rewrite op_raw_load_sw; rewrite Er; [|exact (access_read_align1 _ _ _ _ _ Hacc)].
  rewrite Hload Z.mod_mod; [reflexivity | lia].
Qed.

End getopt.
End GetoptLogicOn.
