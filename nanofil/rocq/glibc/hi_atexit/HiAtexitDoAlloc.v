From Glibc Require Import GlibcProgram.
(** stdout gets its first buffer by asking the kernel about its file
    descriptor, choosing a buffer size, and calling glibc's allocator.
    This file joins the proofs of those steps. The resulting buffer
    belongs to the stream, and the allocator's thread cache stays idle. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsFstat OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers
  AllocLogic LibioSetb LibioDoAllocBase LibioDoAllocTail LibioDoAllocMode LibioDoAlloc
  HiAtexitBase HiAtexitSetb HiAtexitAlloc HiAtexitCloseIt.
From Glibc Require FileInv LibioDoAlloc LibioDoAllocMode LibioDoAllocTail LibioLogic LibioRead OsWorld SysWrappers.
Import ListNotations.
Open Scope Z_scope.

(** The allocation tail runs in the common interpreter logic. *)
(** The file-kind test runs in the common interpreter logic. *)
(** The complete allocation function runs in the common interpreter logic. *)
Import SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" glibc__IO_file_stat)
  `{Hfstat : !Defines ge "__GI___fstat64" glibc___fstat64}
  `{Hmaj : !Defines ge "__gnu_dev_major" glibc___gnu_dev_major}
  `{Hisatty : !Defines ge "__isatty_nostatus" glibc___isatty_nostatus}
  `{Hsetb : !Defines ge "__GI__IO_setb" glibc__IO_setb}.
Context `{Hfree_fn : !Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context `{Hmalloc_fn : !Defines ge "malloc" malloc_fn}
  `{Hmalloc2 : !Defines ge "malloc#__libc_malloc2" malloc2_fn}.
Context (dq : dfrac)
  (mp tc dummy : Z)
  (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))).


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
  iApply (hi_setb Hfh Hzf Hzg with "Hl Hfl Hb He [] HK"); try assumption.
  iLeft. done.
Qed.

(** The buffer allocator uses the proved glibc allocation call. *)
Definition hi_doalloc_malloc :=
  hi_malloc_rule dq mp tc dummy mpr tcr dr Hmp Htc.

(** The size-selection tail calls the proved allocator and buffer setter. *)
Definition hi_doalloc_L7 :=
  LibioDoAllocTail.wp_doalloc_L7 hi_setb_null
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doalloc_malloc.

(** The block-size branch uses the same allocator and buffer setter. *)
Definition hi_doalloc_L28 :=
  LibioDoAllocTail.wp_doalloc_L28 hi_setb_null
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doalloc_malloc.

(** The terminal branch installs a line-buffered stream buffer. *)
Definition hi_doalloc_L33 :=
  LibioDoAllocTail.wp_doalloc_L33 hi_setb_null
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doalloc_malloc.

(** The stream's file kind determines whether its buffer is line-buffered. *)
Definition hi_doalloc_L5 :=
  LibioDoAllocMode.wp_doalloc_L5 Hreg Hext
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
  iApply (LibioRead.wp_glibc__IO_file_stat Hreg Hext with "Hl Hfd Hb Hs Herr HK"); assumption.
Qed.

(** Buffer allocation now has no unproved callee or block triples. *)
Definition hi_doallocate :=
  LibioDoAlloc.wp_glibc__IO_file_doallocate Hstat
    (hi_malloc_state dq mp tc dummy mpr tcr dr) hi_doalloc_L5 hi_doalloc_L7 hi_file_stat.

End rules.
