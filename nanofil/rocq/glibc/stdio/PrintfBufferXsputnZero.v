(** Printf can dispatch a zero-byte write without borrowing stream memory.
    This proof checks the loaded function pointer and invokes the actual
    xsputn body, whose early return preserves every caller resource.
    The call rule stops before the count comparison. The composed rule
    follows the matching-count branch, leaving buffer selection to the caller. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics
  ExternalCalls Pieces Heap Language Logic Symbolic.
From Glibc Require Import LibioLogic LibioXsputnCode LibioXsputnZero
  PrintfBufferFileCode PrintfBufferXsputnReturn.
Import ListNotations.
Open Scope Z_scope.

(** The caller and zero-length callee share the supplied instruction rules. *)
Module PrintfBufferXsputnZeroOn (R : Runtime) (LG : LogicSig R).
Module ZS := LibioXsputnZeroOn R LG.
Import LG LG.L.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context {world : Type} (registry : name -> option (contract world))
  (wi : mem -> world -> gmap piece pval -> Prop) `{!SafepointStable wi} (ge : genv).
Context (Hfn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).

(** The proof retains the caller's world interpretation across the indirect call. *)
Local Instance zero_call_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry wi ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A zero-byte write returns zero without changing the caller's memory.
    Printf keeps its buffer pointer and requested count for the comparison
    that follows the call. *)
Lemma wp_printf_xsputn_zero_call e fp src bb (P : iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb+24) (Obj bb))) ->
  lookup (TAtom "v48") e = Some (WPtr (FileInv.sym_ptr ge "_IO_new_file_xsputn")) ->
  lookup (TAtom "v51") e = Some (WPtr fp) ->
  lookup (TAtom "v53") e = Some (WPtr src) ->
  lookup (TAtom "v37") e = Some (WInt 0) ->
  P -∗ (∀ e', ⌜lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb))) /\
    lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (bb+24) (Obj bb))) /\
    lookup (TAtom "v37") e' = Some (WInt 0) /\
    lookup (TAtom "v55") e' = Some (WInt 0)⌝ -∗ P -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
      (Exec (TAtom "iw_1.join") (skipn 9 (b_insts printf_xsputn_block))
        (b_jump printf_xsputn_block))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Exec (TAtom "iw_1.join") (skipn 7 (b_insts printf_xsputn_block))
      (b_jump printf_xsputn_block))) : sexpr) {{ Φ }}.
Proof.
  intros Hv0 Hchk Hptr Hfp Hsrc Hcount. iIntros "HP HK".
  cbn [printf_xsputn_block b_insts b_jump skipn].
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfn) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfn) |
    apply (ge_fn_check _ _ _ Hfn) | vx | apply (ge_fn_find _ _ _ Hfn) |
    reflexivity | reflexivity |].
  iNext. iApply (ZS.wp_xsputn_zero registry wi ge _ fp src P with "HP [HK]"); [reflexivity |].
  iNext. iIntros "HP".
  iExists _. iSplit; [iPureIntro; reflexivity |]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  iApply ("HK" $! _ with "[%] HP"). split_and!; lookups; assumption || reflexivity.
Qed.

(** The zero result matches the zero request, so printf proceeds to choose
    its next buffer without marking failure. The continuation keeps every
    resource and the original buffer registers. *)
Lemma wp_printf_xsputn_zero_complete e fp src bb (P : iProp Σ) Φ :
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb+24) (Obj bb))) ->
  lookup (TAtom "v48") e = Some (WPtr (FileInv.sym_ptr ge "_IO_new_file_xsputn")) ->
  lookup (TAtom "v51") e = Some (WPtr fp) ->
  lookup (TAtom "v53") e = Some (WPtr src) ->
  lookup (TAtom "v37") e = Some (WInt 0) ->
  P -∗ (∀ e', ⌜lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb))) /\
    lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (bb+24) (Obj bb)))⌝ -∗ P -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
      (Enter (TAtom "L40") (Some (TAtom "iw_1.join")))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Exec (TAtom "iw_1.join") (skipn 7 (b_insts printf_xsputn_block))
      (b_jump printf_xsputn_block))) : sexpr) {{ Φ }}.
Proof.
  intros Hv0 Hchk Hptr Hfp Hsrc Hcount. iIntros "HP HK".
  iApply (wp_printf_xsputn_zero_call e fp src bb P with "HP [HK]"); try assumption.
  iIntros (e' (Hv0' & Hchk' & Hcount' & Hret')) "HP".
  cbn [printf_xsputn_block b_insts b_jump skipn].
  iApply wp_let; [reflexivity | reflexivity | vx | intros; reflexivity |]. iNext.
  iApply wp_branch; [vx |]. iNext.
  cbn [edge_label].
  iApply ("HK" with "[%] HP"). split; lookups; assumption || reflexivity.
Qed.
End rules.
End PrintfBufferXsputnZeroOn.
