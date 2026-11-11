(** stdout gets its first buffer by asking the kernel about its file
    descriptor, choosing a buffer size, and calling glibc's allocator.
    This file joins the proofs of those steps. The resulting buffer
    belongs to the stream, and the allocator's thread cache stays idle. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsFstat OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers
  AllocLogic LibioSetb LibioDoAllocBase LibioDoAllocTail LibioDoAllocMode LibioDoAlloc
  HiAtexitBase HiAtexitSetb HiAtexitAlloc HiAtexitCloseIt.
Import ListNotations.
Open Scope Z_scope.

(** The allocation tail runs in the common interpreter logic. *)
Module HAT := LibioDoAllocTailOn InterpRuntime HLG.
(** The file-kind test runs in the common interpreter logic. *)
Module HAM := LibioDoAllocModeOn InterpRuntime HLG.
(** The complete allocation function runs in the common interpreter logic. *)
Module HAD := LibioDoAllocOn InterpRuntime HLG.
Import HSB.SW HSB.SW.FI.ML HSB.SW.FI.LG HSB.SW.FI.L HSB.SW.OW HSB.SW.FI HSB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" glibc__IO_file_stat)
  (Hfstat : find_fn ge (TAtom "__GI___fstat64") = Some (Defined glibc___fstat64))
  (Hmaj : find_fn ge (TAtom "__gnu_dev_major") = Some (Defined glibc___gnu_dev_major))
  (Hisatty : find_fn ge (TAtom "__isatty_nostatus") = Some (Defined glibc___isatty_nostatus))
  (Hsetb : find_fn ge (TAtom "__GI__IO_setb") = Some (Defined glibc__IO_setb)).
Context (Hfree_fn : find_fn ge (TAtom "free") = Some (Defined free_fn)) (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None) (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context (Hmalloc_fn : find_fn ge (TAtom "malloc") = Some (Defined malloc_fn))
  (Hmalloc2 : find_fn ge (TAtom "malloc#__libc_malloc2") = Some (Defined malloc2_fn)).
Context (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))).

(** The program logic uses the OS world for buffer allocation. *)
Local Instance hi_doalloc_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Installing a stream's first buffer needs no old buffer resource. *)
Lemma hi_setb_null fr fb freg fl oe nb ne a Φ :
  call_frame glibc__IO_setb [WPtr (mkPtr fb (Obj fb)); WPtr nb; WPtr ne; WInt a] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> 0 <= a < 2 ^ 32 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags (setb_flags fl a) -∗ pcell fb off_buf_base nb -∗
     pcell fb off_buf_end ne -∗ Φ RetVoid) -∗
  WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hr Ha. iIntros "Hl Hfl Hb He HK".
  iApply (hi_setb w0 registry ge Hfree_fn Hfh Hzf Hzg with "Hl Hfl Hb He [] HK"); try assumption.
  iLeft. done.
Qed.

(** The buffer allocator uses the proved glibc allocation call. *)
Definition hi_doalloc_malloc :=
  hi_malloc_rule w0 registry ge Hmalloc_fn Hmalloc2 dq mp tc dummy mpr tcr dr Hmp Htc.

(** The size-selection tail calls the proved allocator and buffer setter. *)
Definition hi_doalloc_L7 :=
  HAT.wp_doalloc_L7 w0 registry ge Hsetb hi_setb_null
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doalloc_malloc.

(** The block-size branch uses the same allocator and buffer setter. *)
Definition hi_doalloc_L28 :=
  HAT.wp_doalloc_L28 w0 registry ge Hsetb hi_setb_null
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doalloc_malloc.

(** The terminal branch installs a line-buffered stream buffer. *)
Definition hi_doalloc_L33 :=
  HAT.wp_doalloc_L33 w0 registry ge Hsetb hi_setb_null
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doalloc_malloc.

(** The stream's file kind determines whether its buffer is line-buffered. *)
Definition hi_doalloc_L5 :=
  HAM.wp_doalloc_L5 w0 registry ge Hreg Hext Hmaj Hisatty
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doalloc_L28 hi_doalloc_L33.

(** The file-stat call runs the proved wrapper of the kernel stat call. *)
Lemma hi_file_stat fr fb freg fd b reg o eb Φ :
  call_frame glibc__IO_file_stat [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + o) (Obj b))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> b + o + stat_size <= r_end reg ->
  live fb freg -∗ int_cell fb off_fileno fd -∗ live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live fb freg -∗ int_cell fb off_fileno fd -∗ live b reg -∗
     blk_any b o stat_size -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : language.expr (nanofil_lang registry ge)) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hr He Hfd Ho Hstatend. iIntros "Hl Hfd Hb Hs Herr HK".
  iApply (HRD.wp_glibc__IO_file_stat w0 registry ge Hreg Hext with "Hl Hfd Hb Hs Herr HK"); assumption.
Qed.

(** Buffer allocation now has no unproved callee or block triples. *)
Definition hi_doallocate :=
  HAD.wp_glibc__IO_file_doallocate w0 registry ge Hstat
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doalloc_L5 hi_doalloc_L7 hi_file_stat.

End rules.
