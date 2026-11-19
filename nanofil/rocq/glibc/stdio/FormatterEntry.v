(** The formatter allocates temporary memory, reads errno and copies
    the argument cursor before scanning its format. This proof follows
    those entry instructions and hands their resources to the scan.
    The caller must already own errno and the argument cursor.

    The captured function uses heap allocations rather than named stack
    allocations. Its real call frame therefore has no stack objects to
    invalidate on return. This fact does not permit dropping an arbitrary
    list of stack objects supplied at an internal block. *)
From Glibc Require FixVariadic.
From Glibc Require Import Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap Language Logic MemLogic VariadicLogic.
From Glibc Require Import OsWorld FileInv LibioLogic
  FormatterInitialScan Fix.
Import FixVariadic.VL0 ListNotations ProgramAbbreviations Fix.ML0 Fix.LG0 Fix.LG0.L LibioLogic.
Open Scope Z_scope.
(** Calling the captured function initializes its actual stack-object
    list to empty; the heap allocation instructions preserve that list. *)
Lemma formatter_call_stack_empty bb p ab flags fr :
  call_frame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer [WPtr bb; WPtr p; WPtr ab; WInt flags] = Some fr ->
  fr_locals fr = [].
Proof. intros H. injection H as <-. reflexivity. Qed.
(** The scan needs the original call arguments and the allocated saved
    pointer and work area. The entry code also retains its cursor copy
    and the sentinel used by the parser. *)
Definition formatter_entry_inputs e bb p ab flags fb wb vb :=
  lookup (TAtom "v0") e = Some (WPtr bb) /\
  lookup (TAtom "v2") e = Some (WPtr p) /\
  lookup (TAtom "v4") e = Some (WPtr ab) /\
  lookup (TAtom "v6") e = Some (WInt flags) /\
  lookup (TAtom "v10") e = Some (WPtr (mkPtr fb (Obj fb))) /\
  lookup (TAtom "v13") e = Some (WPtr (mkPtr wb (Obj wb))) /\
  lookup (TAtom "v15") e = Some (WPtr (mkPtr vb (Obj vb))) /\
  lookup (TAtom "v23") e = Some (WPtr (mkPtr (2^64-1) CNone)).
Section entry.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
(** Entry preserves the caller's cursor, snapshot lifetime and errno.
    It supplies a fresh saved-format cell, work area and cursor copy.
    Other caller resources remain in the frame around the continuation. *)
Lemma wp_formatter_entry fr bb p ab ar flags sb sr cur eb er err Φ :
  call_frame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer
    [WPtr bb; WPtr p; WPtr (mkPtr ab (Obj ab)); WInt flags] = Some fr ->
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  0 < ab -> ab mod 8 = 0 -> ab + 8 <= r_end ar -> r_end ar <= 2^63 ->
  0 <= cur < 2^64 -> 0 < eb -> eb + 4 <= r_end er -> r_end er <= 2^63 ->
  live ab ar -∗ pcell ab 0 (mkPtr cur (Ro sb)) -∗ live sb sr -∗ live eb er -∗ int_cell eb 0 err -∗
  ▷ (∀ e fb wb vb,
    ⌜formatter_entry_inputs e bb p (mkPtr ab (Obj ab)) flags fb wb vb /\
      0 < fb /\ fb mod 8 = 0 /\ fb + 16 <= 2^48 /\
      0 <= wb /\ wb + 1000 < 2^64 /\
      0 < vb /\ vb mod 8 = 0 /\ vb + 32 <= 2^48⌝ -∗
    live ab ar -∗ pcell ab 0 (mkPtr cur (Ro sb)) -∗ live sb sr -∗ live eb er -∗ int_cell eb 0 err -∗
    live fb (mkRegion fb (fb+16) Heap Live) -∗ pcell fb 0 null -∗
    obj wb (heap_req 4 1000) -∗
    live vb (mkRegion vb (vb+32) Heap Live) -∗ pcell vb 0 (mkPtr cur (Ro sb)) -∗
    WP (ERun (mkFrame Unit_stdioZ2dcommon_vfprintfZ2dinternal_os.fn___printf_buffer e [] None
      (Exec (TAtom "start") (skipn 19 (b_insts initial_scan_block)) (b_jump initial_scan_block))) : gexpr) {{ Φ }}) -∗
  WP (ERun fr : gexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Herr Hab Haa Hae Har Hcur Heb Hee Her.
  injection Hfr as <-. iIntros "Hal Hap Hsl Hel Herr HK". step.
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (fb [Hfb [Hfa Hfe]]) "Ho".
  iDestruct (obj_zero_block with "Ho") as "(Hfl & Hfx & Hfc)"; [compute; discriminate|].
  iAssert (live fb (mkRegion fb (fb+16) Heap Live)) with "Hfl" as "Hfl".
  iDestruct (zero_cell_prefix fb 0 8 with "Hfx Hfc") as "(Hfp & _ & _)".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (wb [Hwb [Hwa Hwe]]) "Hwork".
  iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |].
  iNext. iIntros (vb [Hvb [Hva Hve]]) "Ho".
  iDestruct (obj_zero_block with "Ho") as "(Hvl & Hvx & Hvc)"; [compute; discriminate|].
  iAssert (live vb (mkRegion vb (vb+32) Heap Live)) with "Hvl" as "Hvl".
  iDestruct (zero_cell_prefix vb 0 24 with "Hvx Hvc") as "(Hvp & _ & _)".
  do 8 (iApply wp_alloc; [vm_compute; reflexivity | vm_compute; congruence | vm_compute; congruence |
    intros ? ? ? ? Hf Hw; exact (os_wi_alloc w0 _ _ _ _ _ Hf Hw) |]; iNext; iIntros (? _) "_").
  step. check "Hel". iDestruct "Herr" as "[%Herrr Herr]". load_s32 "Hel" "Herr".
  step. check "Hal".
  iApply (wp_raw_load_pointer_dq with "Hal Hap Hsl");
    [reflexivity | vx | left; reflexivity | a2 | a2 | exact Hcur |].
  iNext. iIntros "Hal Hap Hsl".
  change (fb mod 16 = 0) in Hfa. change (fb + 16 <= 2^48) in Hfe.
  change (vb mod 16 = 0) in Hva. change (vb + 32 <= 2^48) in Hve.
  change (wb + 1008 <= 2^48) in Hwe.
  assert (Hvb8 : vb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  assert (Hfb8 : fb mod 8 = 0) by (Z.div_mod_to_equations; lia).
  set (vr := mkRegion vb (vb+32) Heap Live) in *.
  assert (Hvr : r_end vr = vb+32) by reflexivity.
  check "Hvl". store "Hvl" "Hvp".
  iApply ("HK" with "[%] Hal Hap Hsl Hel [Herr] Hfl Hfp Hwork Hvl Hvp").
  - split.
    + unfold formatter_entry_inputs. repeat split; reflexivity.
    + repeat split; lia.
  - iSplit; [done|iExact "Herr"].
Qed.
End entry.
