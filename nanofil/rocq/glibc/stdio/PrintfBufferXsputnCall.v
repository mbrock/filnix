(** Printf sends its staging array through the stream's checked xsputn
    function pointer. The array contains raw bytes and need not end in NUL.
    The caller compares the returned count with the requested count.

    This rule starts after the pointer loads. It checks the function pointer
    and calls the captured file-xsputn body under an explicit callee contract.
    That contract returns the borrowed bytes even when the count differs. *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioXsputnCode PrintfBufferFileCode PrintfBufferXsputnReturn.
Import ListNotations.
Open Scope Z_scope.

(** The indirect call uses the same runtime and OS interpretation as its caller. *)
Module PrintfBufferXsputnCallOn (R : Runtime) (LG0 : LogicSig R).
Module CS := LibioCloseStepsOn R LG0.
Import CS CS.SW CS.SW.FI.ML CS.SW.FI.LG CS.SW.FI.L CS.SW.OW CS.SW.FI CS.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The stream contract owns any errno resources that the call may change. *)
Local Instance call_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Context (F : ptr -> iProp Σ) (E : iProp Σ).

(** The backend must preserve the source bytes and stream resources on every
    return. The result may differ from the requested count. *)
Definition printf_xsputn_call_spec : Prop := forall fr fp bb breg dq xs Φ,
  0 < bb -> bb mod 8 = 0 -> Z.of_nat (length xs) <= 128 ->
  bb + 48 + Z.of_nat (length xs) <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) xs ->
  call_frame glibc__IO_new_file_xsputn
    [WPtr fp; WPtr (mkPtr (bb + 48) (Obj bb)); WInt (Z.of_nat (length xs))] = Some fr ->
  F fp -∗ E -∗ liveq dq bb breg -∗ bytesq dq bb 48 xs -∗
  ▷ (∀ r, ⌜0 <= r < 2 ^ 64⌝ -∗ F fp -∗ E -∗ liveq dq bb breg -∗
    bytesq dq bb 48 xs -∗ Φ (Ret (WInt r))) -∗ WP (ERun fr : sexpr) {{ Φ }}.

Context (Hfn : ge_fn ge "_IO_new_file_xsputn" glibc__IO_new_file_xsputn).
Context (Hcall : printf_xsputn_call_spec).

(** The checked pointer names the captured file-xsputn function. Its result
    reaches the count comparison without assuming complete acceptance. *)
Lemma wp_printf_xsputn_call e fp bb breg dq xs Φ :
  0 < bb -> bb mod 8 = 0 -> Z.of_nat (length xs) <= 128 ->
  bb + 48 + Z.of_nat (length xs) <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) xs ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr bb (Obj bb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (bb + 24) (Obj bb))) ->
  lookup (TAtom "v48") e = Some (WPtr (sym_ptr ge "_IO_new_file_xsputn")) ->
  lookup (TAtom "v51") e = Some (WPtr fp) ->
  lookup (TAtom "v53") e = Some (WPtr (mkPtr (bb + 48) (Obj bb))) ->
  lookup (TAtom "v37") e = Some (WInt (Z.of_nat (length xs))) ->
  F fp -∗ E -∗ liveq dq bb breg -∗ bytesq dq bb 48 xs -∗
  (∀ r e', ⌜0 <= r < 2 ^ 64 /\
      lookup (TAtom "v0") e' = Some (WPtr (mkPtr bb (Obj bb))) /\
      lookup (TAtom "chk0") e' = Some (WPtr (mkPtr (bb + 24) (Obj bb))) /\
      lookup (TAtom "v37") e' = Some (WInt (Z.of_nat (length xs))) /\
      lookup (TAtom "v55") e' = Some (WInt r)⌝ -∗
    F fp -∗ E -∗ liveq dq bb breg -∗ bytesq dq bb 48 xs -∗
    WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e' [] None
      (Exec (TAtom "iw_1.join") (skipn 9 (b_insts printf_xsputn_block))
        (b_jump printf_xsputn_block))) : sexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame glibc___printf_buffer_flush_to_file e [] None
    (Exec (TAtom "iw_1.join") (skipn 7 (b_insts printf_xsputn_block))
      (b_jump printf_xsputn_block))) : sexpr) {{ Φ }}.
Proof.
  intros Hbb Hba Hlen Hbe Hbr Hxs Hv0 Hchk Hptr Hfp Hsrc Hcount.
  iIntros "HF HE Hb Hxs HK". cbn [printf_xsputn_block b_insts b_jump skipn].
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfn) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfn) |
    apply (ge_fn_check _ _ _ Hfn) | vx | apply (ge_fn_find _ _ _ Hfn) |
    reflexivity | reflexivity |].
  iNext. rewrite (Z.mod_small (Z.of_nat (length xs)) (2 ^ 64)); [|lia].
  iApply (Hcall with "HF HE Hb Hxs"); try assumption; [reflexivity |].
  iNext. iIntros (r Hr) "HF HE Hb Hxs". resume.
  iApply ("HK" $! r _ with "[%] HF HE Hb Hxs").
  split; [exact Hr |]. split_and!; lookups; try assumption.
  all: try rewrite (Z.mod_small r (2 ^ 64) Hr); reflexivity.
Qed.

End rules.
End PrintfBufferXsputnCallOn.
