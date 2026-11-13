(** Printf passes its staged character to the stream as an unsigned byte.
    This proof follows the byte load and overflow call in the captured
    flush body, beginning after the FILE pointer has been loaded.

    The stream call remains an explicit conditional obligation. Its resource
    predicate must carry any descriptor and buffer-ordering facts needed by
    the backend; ownership of the FILE layout alone does not establish them. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioOverflowBase PrintfBufferFileCode PrintfBufferOverflowReturn.
Import ListNotations.
Open Scope Z_scope.

(** The caller and its conditional callee share the same OS interpretation. *)
Module PrintfBufferOverflowCallOn (R : Runtime) (LG0 : LogicSig R).
Module CS := LibioCloseStepsOn R LG0.
Import CS CS.SW CS.SW.FI.ML CS.SW.FI.LG CS.SW.FI.L CS.SW.OW CS.SW.FI CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The surrounding process retains its existing OS resources across the call. *)
Local Instance call_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

Context (F : ptr -> iProp Σ) (E : iProp Σ).

(** The backend must return its stream resources even when it returns EOF.
    The abstract resources may own errno, but need not preserve its value. *)
Definition printf_overflow_call_spec : Prop := forall fr fp ch Φ,
  0 <= ch < 256 ->
  call_frame glibc___overflow [WPtr fp; WInt ch] = Some fr ->
  F fp -∗ E -∗
  ▷ (∀ r, ⌜0 <= r < 2 ^ 32⌝ -∗ F fp -∗ E -∗ Φ (Ret (WInt r))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.

Context (Hoverflow : find_fn ge (TAtom "__GI___overflow") = Some (Defined glibc___overflow)).
Context (Hcall : printf_overflow_call_spec).

(** The staged byte is passed unchanged, including bytes above 127. The
    returned value remains unrestricted except for its canonical integer range. *)
Lemma wp_printf_overflow_call e bb breg fp ch Φ :
  0 < bb -> bb + 49 <= r_end breg -> r_end breg <= 2 ^ 63 ->
  0 <= ch < 256 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) ->
  lookup (TAtom "v91") e = Some (WPtr fp) ->
  live bb breg -∗ bytes bb 48 [ch] -∗ F fp -∗ E -∗
  (∀ r e', ⌜0 <= r < 2 ^ 32 /\
       lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb))) /\
       lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (bb + 24) (Obj bb))) /\
       lookup (TAtom "v96") e' = Some (WInt r)⌝ -∗
     live bb breg -∗ bytes bb 48 [ch] -∗ F fp -∗ E -∗
     WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
       (Exec (TAtom "L74") (skipn 8 (b_insts printf_overflow_block))
         (b_jump printf_overflow_block))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Exec (TAtom "L74") (skipn 3 (b_insts printf_overflow_block))
      (b_jump printf_overflow_block))) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hbe Hbr Hch Hv0 Hchk Hfp. iIntros "Hb Hch HF HE HK".
  cbn [printf_overflow_block b_insts b_jump skipn].
  fs. fchk "Hb".
  iApply (wp_raw_load_sub_bytes_dq with "Hb Hch");
    [reflexivity | vx | reflexivity | reflexivity | left; reflexivity | a2 |].
  iNext. iIntros "Hb Hch". fs.
  iApply wp_call_bind; [vx | exact Hoverflow | reflexivity |]. iNext.
  norm. rewrite Z.mul_0_r Z.add_0_r (sb_byte ch Hch).
  rewrite !(Z.mod_small ch (2 ^ 32) ltac:(lia)).
  iApply (Hcall with "HF HE"); [exact Hch | reflexivity |].
  iNext. iIntros (r Hr) "HF HE". resume.
  iApply ("HK" $! r _ with "[%] Hb Hch HF HE").
  split; [exact Hr |]. split_and!; lookups; try assumption.
  all: try rewrite (Z.mod_small r (2 ^ 32) Hr); reflexivity.
Qed.

End rules.
End PrintfBufferOverflowCallOn.
