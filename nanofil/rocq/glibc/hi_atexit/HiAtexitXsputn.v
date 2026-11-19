From Glibc Require Fix.
From Glibc Require Import Unit_io_fstat64_os Unit_io_write_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os.
From Glibc Require Import Unit_misc_makedev_os Unit_string_memcpy_os Unit_string_mempcpy_os Unit_termios_isatty_nostatus_os.
From Glibc Require Import GlibcProgram.
(** stdout's string-output function calls overflow and the shared-byte
    write rule. This file supplies both from proved glibc code. Its
    result is a bounded byte count or failure; safety does not require
    the operating system to accept every requested byte. *)

From Glibc Require Import GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv
  LibioLogic SysWrappers AllocLogic LibioDefaultXsputnBuf LibioXsputnBase
  LibioWriteDq AllocCall
  StreamOutputState HiAtexitXsputnOverflow HiAtexitGe HiAtexitFns.
From Glibc Require LibioXsputn.
Import ListNotations.
Open Scope Z_scope.
Import SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.
Import LibioXsputnBase LibioDefaultXsputnBuf.

Definition hi_xsputn_irisGS `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}
  (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv) :
  irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry)
  (Hext : sys_external ge).
Context (Hstat : ge_fn ge "__GI__IO_file_stat" Unit_libio_fileops_os.fn___GI__IO_file_stat)
  `{Hfstat : !Defines ge "__GI___fstat64" Unit_io_fstat64_os.fn___GI___fstat64}
  `{Hmaj : !Defines ge "__gnu_dev_major" Unit_misc_makedev_os.fn___gnu_dev_major}
  `{Hisatty : !Defines ge "__isatty_nostatus" Unit_termios_isatty_nostatus_os.fn___isatty_nostatus}
  `{Hsetb : !Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.
Context `{Hfree_fn : !Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None).
Context `{Hmalloc_fn : !Defines ge "malloc" malloc_fn}
  `{Hmalloc2 : !Defines ge "glibc_malloc#__libc_malloc2" malloc2_fn}.
Context (dq : dfrac)
  (mp tc dummy : Z)
  (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "glibc_malloc#mp_") (ge_globals ge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals ge) = Some (mkPtr tc (Obj tc))).
Context (Hda : ge_fn ge "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate)
  `{Hdab : !Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}
  `{Hwrite : !Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  `{Hdwf : !Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  `{Hcpy : !Defines ge "__GI_memcpy" Unit_string_memcpy_os.fn___GI_memcpy}
  `{Hpcpy : !Defines ge "__GI_mempcpy" Unit_string_mempcpy_os.fn___GI___mempcpy}
  `{Hdxf : !Defines ge "__GI__IO_default_xsputn" Unit_libio_genops_os.fn___GI__IO_default_xsputn}
  (Hfo : ge_fn ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow).

Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A write may accept only part of the borrowed bytes or fail.
    Both syscall branches return the caller's source share and keep its
    cancellation flags unchanged. The noncanceling branch requires the
    captured wrapper. *)
Lemma hi_file_write_dq : fwq_spec w0 registry ge.
Proof using Hext Hreg Hwrite.
  intros fr fb freg fl f2 fd tw off dq' b reg o c xs eb Φ Hfr Hc Hfb Hal Hend Hregend Hf2 Hf2r Hfd Hfl Heb
    Hb Ho Hbend Hbreg Hxs.
  iIntros "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK".
  iApply (LibioWriteDq.wp_glibc__IO_new_file_write_dq Hreg Hext
    fr fb freg fl f2 fd tw off dq' b reg c o xs eb with
    "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK"); try assumption.
Qed.

(** Writing a string preserves the stream's fields, its heap buffer
    and the allocator's idle state. The proof supplies every called
    function rather than assuming that any call is safe. *)
Lemma hi_xsputn fr eb fb freg vb vreg nb wp we dq' b' reg' so c' ys Φ :
  let n := Z.of_nat (length ys) in
  call_frame Unit_libio_fileops_os.fn__IO_new_file_xsputn [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b' + so) c'); WInt n] = Some fr ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb (fun _ _ => malloc_call_state dq mp tc dummy mpr tcr dr) fb nb -∗
  liveq dq' b' reg' -∗ bytesq dq' b' so ys -∗
  ▷ xs_post w0 registry ge eb (fun _ _ => malloc_call_state dq mp tc dummy mpr tcr dr)
    fb freg vb n dq' b' reg' so ys Φ -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hcpy Hda Hdab Hdwf Hdxf Hext Hfh Hfo Hfree_fn Hfstat Hfw Hisatty Hmaj Hmalloc2 Hmalloc_fn Hmove Hmove_fn Hmove_sym Hmp Hpcpy Hreg Hsetb Hstat Htc Hwrite Hzf Hzg.
  intros n Hfr Heb Hfb Hal Hend Hregend Hc Hb Hb8 Ho Hbend Hbreg Hys.
  iIntros "#Hvt Hl Hvtp Hwb Hos Hbl Hys HK".
  iApply (LibioXsputn.wp_glibc__IO_new_file_xsputn Hmove Hmove_fn Hmove_sym Hfw
    ltac:(split; [exact hi_file_write_dq | intros f2 fd H; left; exact (proj1 H)]) fr eb (fun _ _ => malloc_call_state dq mp tc dummy mpr tcr dr)
    fb freg vb vreg nb wp we dq' b' reg' so c' ys with "Hvt Hl Hvtp Hwb Hos Hbl Hys HK"); try assumption.
  exact (hi_xsputn_overflow Hreg Hext Hstat Hfh Hzf Hzg
    dq mp tc dummy mpr tcr dr Hmp Htc Hda Hfw eb Heb).
Qed.

End rules.

Section linked.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "glibc_malloc#mp_") (ge_globals hge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals hge) = Some (mkPtr tc (Obj tc))).

(** The linked program binds every function used by string output.
    This specialization supplies those bindings and the external
    memory-copy contract from the program's actual environment. *)
Definition hge_xsputn :=
  program_call_with (@HiAtexitXsputn.hi_xsputn_irisGS hlc Σ _ _ w0 glibc_os_registry hge) (hi_xsputn (glibc_program := program_of w0 glibc_os_registry hge) (Σ := Σ) (fun n c H => H) (hi_sys_external _)
    (hi_ge_file_stat _)
    hge_frees (proj1 hge_zgc_free) (proj2 hge_zgc_free)
    dq mp tc dummy mpr tcr dr Hmp Htc
    (hi_ge_doallocate _) (hi_ge_file_write _)
    (proj1 (hi_move InterpRuntime.free)) (proj1 (proj2 (hi_move _))) (proj2 (proj2 (hi_move _)))
    (hi_ge_overflow _)).

End linked.
