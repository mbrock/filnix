(** stdout's string-output function calls overflow and the shared-byte
    write rule. This file supplies both from proved glibc code. Its
    result is a bounded byte count or failure; safety does not require
    the operating system to accept every requested byte. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode FileInv
  LibioLogic SysWrappers MemFwdCode AllocLogic LibioGenCode LibioXsputnCode LibioDefaultXsputnBuf LibioXsputnBase
  LibioWriteDq HiAtexitBase HiAtexitSetb HiAtexitAlloc HiAtexitDoWrite
  HiAtexitOutputState HiAtexitXsputnRules HiAtexitXsputnOverflow HiAtexitGe HiAtexitFns.
Import ListNotations.
Open Scope Z_scope.
Import HOG.OB HOG.OB.SW HOG.OB.SW.FI.ML HOG.OB.SW.FI.LG HOG.OB.SW.FI.L
  HOG.OB.SW.OW HOG.OB.SW.FI HOG.OB.SW.ST.
Import HXS.XE.XL.XU.XW.XD.XC.XR.XF.XS.
Import XB XB.DX.RM.SM.TL.BY.BF.

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
Context (Hda : ge_fn ge "__GI__IO_file_doallocate" glibc__IO_file_doallocate)
  (Hdab : find_fn ge (TAtom "__GI__IO_doallocbuf") = Some (Defined glibc__IO_doallocbuf))
  (Hwrite : find_fn ge (TAtom "__GI___write") = Some (Defined glibc___libc_write))
  (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hdwf : find_fn ge (TAtom "_IO_new_do_write") = Some (Defined glibc__IO_new_do_write)).
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None) (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  (Hcpy : find_fn ge (TAtom "__GI_memcpy") = Some (Defined glibc_memcpy))
  (Hpcpy : find_fn ge (TAtom "__GI_mempcpy") = Some (Defined glibc_mempcpy))
  (Hdxf : find_fn ge (TAtom "__GI__IO_default_xsputn") = Some (Defined glibc__IO_default_xsputn))
  (Hfo : ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow).

(** String output uses the same OS world as its proved callees. *)
Local Instance hi_xsputn_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A write may accept only part of the borrowed bytes or fail.
    Both syscall branches return the caller's source share and keep its
    cancellation flags unchanged. The noncanceling branch requires the
    captured wrapper. *)
Lemma hi_file_write_dq : fwq_spec w0 registry ge.
Proof.
  intros fr fb freg fl f2 fd tw off dq' b reg o c xs eb Φ Hfr Hc Hfb Hal Hend Hregend Hf2 Hf2r Hfd Hfl Heb
    Hb Ho Hbend Hbreg Hxs.
  iIntros "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK".
  iApply (HWD.wp_glibc__IO_new_file_write_dq w0 registry ge Hreg Hext Hwrite
    fr fb freg fl f2 fd tw off dq' b reg c o xs eb with
    "Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr HK"); try assumption.
Qed.

(** Writing a string preserves the stream's fields, its heap buffer
    and the allocator's idle state. The proof supplies every called
    function rather than assuming that any call is safe. *)
Lemma hi_xsputn fr eb fb freg vb vreg nb wp we dq' b' reg' so c' ys Φ :
  let n := Z.of_nat (length ys) in
  call_frame glibc__IO_new_file_xsputn [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b' + so) c'); WInt n] = Some fr ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb (fun _ _ => hi_malloc_state dq mp tc dummy mpr tcr dr) fb nb -∗
  liveq dq' b' reg' -∗ bytesq dq' b' so ys -∗
  ▷ xs_post w0 registry ge eb (fun _ _ => hi_malloc_state dq mp tc dummy mpr tcr dr)
    fb freg vb n dq' b' reg' so ys Φ -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros n Hfr Heb Hfb Hal Hend Hregend Hc Hb Hb8 Ho Hbend Hbreg Hys.
  iIntros "#Hvt Hl Hvtp Hwb Hos Hbl Hys HK".
  iApply (HXS.wp_glibc__IO_new_file_xsputn w0 registry ge Hmove Hmove_fn Hmove_sym Hcpy Hpcpy Hdxf Hfw
    hi_file_write_dq fr eb (fun _ _ => hi_malloc_state dq mp tc dummy mpr tcr dr)
    fb freg vb vreg nb wp we dq' b' reg' so c' ys with "Hvt Hl Hvtp Hwb Hos Hbl Hys HK"); try assumption.
  exact (hi_xsputn_overflow w0 registry ge Hreg Hext Hstat Hfstat Hmaj Hisatty Hsetb Hfree_fn Hfh Hzf Hzg
    Hmalloc_fn Hmalloc2 dq mp tc dummy mpr tcr dr Hmp Htc Hda Hdab Hwrite Hfw Hdwf eb Heb).
Qed.

End rules.

Section linked.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (dq : dfrac) (mp tc dummy : Z) (mpr tcr dr : region).
Context (Hmp : lookup (TAtom "malloc#mp_") (ge_globals hge) = Some (mkPtr mp (Obj mp)))
  (Htc : lookup (TAtom "tcache") (ge_globals hge) = Some (mkPtr tc (Obj tc))).

(** The linked program binds every function used by string output.
    This specialization supplies those bindings and the external
    memory-copy contract from the program's actual environment. *)
Definition hge_xsputn :=
  hi_xsputn (Σ := Σ) w0 glibc_os_registry hge (fun n c H => H) (hi_sys_external _)
    (hi_ge_file_stat _) (hi_find___GI___fstat64 _) (hi_find___gnu_dev_major _) (hi_find___isatty_nostatus _)
    (hi_find___GI__IO_setb _) (hi_find_free _) hge_frees (proj1 hge_zgc_free) (proj2 hge_zgc_free)
    (hi_find_malloc _) (hi_find_malloc___libc_malloc2 _) dq mp tc dummy mpr tcr dr Hmp Htc
    (hi_ge_doallocate _) (hi_find___GI__IO_doallocbuf _) (hi_find___GI___write _) (hi_ge_file_write _)
    (hi_find__IO_new_do_write _) (proj1 (hi_move InterpRuntime.free)) (proj1 (proj2 (hi_move _))) (proj2 (proj2 (hi_move _)))
    (hi_find___GI_memcpy _) (hi_find___GI_mempcpy _) (hi_find___GI__IO_default_xsputn _) (hi_ge_overflow _).

End linked.
