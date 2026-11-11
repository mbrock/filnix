(** hi_atexit.c registers `c: close_stdout_hi` with `c: atexit`, so
    `c: exit` runs it before glibc's own cleanup. It asks
    `c: __fpending` and `c: ferror` about stdout, closes stdout with
    `c: fclose`, and calls `c: _exit(1)` when stdout had failed or the
    close failed while bytes were pending or the close itself failed.

    [wp_hi_close_stdout] is its triple in the linked genv [hge], from
    the state of stdout that HiAtexitFclose.v's [hi_fclose_stdout]
    takes: a heap buffer holding the pending bytes, the lock free, and
    stdout linked in the list of streams. The function either returns,
    with stdout out of the list, or ends the process in `c: _exit`.
    Either way any postcondition of a return holds. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode LibioDoWriteCode LibioGenCode
  LibioUnlinkCode LibioCloseItCode LibioFcloseCode FileInv LibioLogic SysWrappers AllocLogic LibioCloseSteps
  HiAtexitModule HiAtexitFns HiAtexitGe HiAtexitBase HiAtexitCloseIt HiAtexitFclose.
Import ListNotations.
Open Scope Z_scope.
Import HFC.FU.FT HFC.FU.FT.FN.CS HFC.FU.FT.FN.CS.SW HFC.FU.FT.FN.CS.SW.FI.ML HFC.FU.FT.FN.CS.SW.FI.LG
  HFC.FU.FT.FN.CS.SW.FI.L HFC.FU.FT.FN.CS.SW.OW HFC.FU.FT.FN.CS.SW.FI HFC.FU.FT.FN.CS.SW.ST.

(** hi_atexit.c's `c: close_stdout_hi`, renamed by link.pl. *)
Definition hi_close_fn : func := Eval vm_compute in
  match find_direct (TAtom "hi_atexit#close_stdout_hi") hi_module with
  | Some (Defined f) => f
  | _ => mkFunc (TAtom "hi_atexit#close_stdout_hi") (TAtom "local") RVoid [] []
  end.

(** A call of `c: close_stdout_hi` runs [hi_close_fn]. *)
Lemma hi_find_close : find_fn hge (TAtom "hi_atexit#close_stdout_hi") = Some (Defined hi_close_fn).
Proof. vm_compute. reflexivity. Qed.

(** The frame of `c: close_stdout_hi()`. *)
Definition hi_close_frame : frame := mkFrame hi_close_fn [] [] None (Enter (TAtom "start") None).

(** [hi_close_frame] is the frame of a call of [hi_close_fn]. *)
Lemma hi_close_call : call_frame hi_close_fn [] = Some hi_close_frame.
Proof. reflexivity. Qed.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world).
(** The stream predicates are opaque to type class search, so the
    proof mode's steps do not unfold them. *)
#[local] Hint Opaque live pcell int_cell icell bytes errno_any lock_state io_list_inv vtables_ro single_ro
  tcb_cleanup_inv stream_life : typeclass_instances.

(** The Iris instance for glibc's registry and [os_wi] w0. *)
Local Instance hi_close_irisGS : irisGS_gen hlc (nanofil_lang glibc_os_registry hge) Σ :=
  nanofil_irisGS glibc_os_registry (os_wi w0) hge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang glibc_os_registry hge)).

(** HiAtexitFclose.v's [hi_fclose_stdout] in [hge]: every premise about
    the genv by computation. *)
Definition hge_fclose_stdout :=
  hi_fclose_stdout (Σ := Σ) w0 glibc_os_registry hge (fun n c H => H) (hi_sys_external _)
    (hi_find___GI___write _) (hi_ge_file_write _) (hi_find_free _) hge_frees (proj1 hge_zgc_free)
    (proj2 hge_zgc_free) (hi_find___GI___close_nocancel _) (hi_ge_file_close _) (hi_find___GI__IO_setb _)
    (hi_find__IO_new_do_write _) (hi_find___GI__IO_unsave_markers _) (hi_find___GI___libc_cleanup_push_defer _)
    (hi_find___GI___libc_cleanup_pop_restore _) (hi_find___GI__IO_un_link _) (hi_find___GI__IO_default_finish _)
    (hi_ge_file_finish _) (hi_find__IO_file_close_maybe_unlink _).

(** `c: close_stdout_hi()`, stdout's stream fb as [hge_fclose_stdout]
    takes it and `c: stdout` at so holding it: either `c: _exit(1)` ends
    the process, or the function returns with stdout out of the list of
    streams pre ++ post, the thread's cleanup state and the other
    streams' lives back. *)
Lemma wp_hi_close_stdout pre post fb freg fl f2 fd tw off bb breg i xs rp rb we be eb vb vreg
    lb lbreg sb sreg fcp pin md so soreg Φ :
  let n := Z.of_nat (length xs) in
  let fp := mkPtr fb (Obj fb) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  lookup (TAtom "stdout") (ge_globals hge) = Some (mkPtr so (Obj so)) -> so mod 8 = 0 -> so + 8 <= r_end soreg ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals hge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals hge) = Some pin -> ptr_addr pin <> fb -> 0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals hge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> Z.land f2 32 = 0 -> Z.land f2 io_need_lock = 0 -> 0 <= f2 < 2 ^ 32 ->
  In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 -> Z.land fl io_no_writes = 0 ->
  Z.land fl io_currently_putting <> 0 -> Z.land fl io_user_buf = 0 -> has fl io_user_lock = false ->
  has fl io_linked = true -> has fl io_is_filebuf = true ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> r_kind breg = Heap ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb -> 0 < lb ->
  md = 0 \/ md = 2 ^ 32 - 1 ->
  vtables_ro hge vb vreg -∗ single_ro hge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live so soreg -∗ pcell so 0 fp -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr (mkPtr (bb + i + n) (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 72 null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
  io_list_inv hge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
  ▷ (tcb_cleanup_inv (ow_self w0) -∗ io_list_inv hge (pre ++ post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗
     Φ RetVoid) -∗
  WP (ERun hi_close_frame : sexpr) {{ Φ }}.
Proof.
  intros n fp wb base Hgso Hsoal Hsoend Hgout Hgin Hin Hinr Hfc Hfcr Hfb Hfal Hfend Hfreg Hf22 Hf232 Hnl Hf2r Hfd
    Hfdr Hfl Happ Hnw Hcp Hub Hul Hlnk Hfb8 He Hbk Hb Hi Hbend Hbreg Hy Hbe Hbec Hlb Hmd.
  iIntros "Hvt Hs Htcb Hso Hsoc Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol
    Hmode Hvtp H72 H80 H96 Hlp Hlk Hio Hlives HK".
  unfold file_size in Hfend. subst fp wb base.
  vm_compute in Hgso. injection Hgso as <-. vm_compute in Hgout. injection Hgout as <-.
  iApply (wp_live_fit1 w0 glibc_os_registry hge with "Hso"). iIntros ([Hso0 Hso48]) "Hso".
  iApply (wp_live_fit1 w0 glibc_os_registry hge with "Hl"). iIntros ([Hf0 Hf48]) "Hl".
  iApply (wp_live_fit1 w0 glibc_os_registry hge with "Hbl"). iIntros ([Hb0 Hb48]) "Hbl".
  unfold hi_close_frame. fs. fs. fchk "Hso". fldp "Hso" "Hsoc" "Hl".
  (* `c: __fpending(stdout)`. *)
  iApply wp_call_bind; [vx | exact (hi_find___fpending _) | reflexivity |]. iNext.
  iApply (HRD.wp_glibc___fpending w0 glibc_os_registry hge _ _ _ md (mkPtr (bb + i + Z.of_nat (length xs)) (Obj bb)) (mkPtr (bb + i) (Obj bb)) breg
            with "Hl Hmode Hwp Hwb Hbl"); [reflexivity | side | side | side | side | exact Hmd | reflexivity
                                            | cbn; lia | cbn; lia |].
  iNext. iIntros "Hl Hmode Hwp Hwb Hbl". resume.
  fs. fs. fchk "Hso". fldp "Hso" "Hsoc" "Hl".
  (* `c: ferror(stdout)`. *)
  iApply wp_call_bind; [vx | exact (hi_find_ferror _) | reflexivity |]. iNext.
  iApply (HRD.wp_glibc__IO_ferror w0 glibc_os_registry hge with "Hl Hfl Hfl2"); [reflexivity | side | side | side
                                                                                 | side | exact Hnl |].
  iNext. iIntros "Hl Hfl Hfl2". resume.
  fs. fs. fchk "Hso". fldp "Hso" "Hsoc" "Hl".
  (* `c: fclose(stdout)`. *)
  iApply wp_call_bind; [vx | exact (hi_find_fclose _) | reflexivity |]. iNext.
  iApply (hge_fclose_stdout _ pre post 69808 freg fl f2 fd tw off bb breg i xs rp rb we be eb vb vreg lb lbreg
            sb sreg fcp pin md with "Hvt Hs Htcb Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase
            Hbend Hcol Hmode Hvtp H72 H80 H96 Hlp Hlk Hio Hlives").
  all: lazymatch goal with
       | |- environments.envs_entails _ _ => idtac
       | |- _ => first [assumption | reflexivity | vm_compute; reflexivity | lia]
       end.
  iNext. iIntros (r fl' k tw' [Hpost Hk]) "Htcb _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hio Hlives _".
  resume. iClear "Hso Hsoc". fs.
  (* The branches: `c: _exit(1)`, or the return. *)
  all: repeat first [fs | brc].
  all: lazymatch goal with
       | |- context [Exec _ (Call _ (Global (TAtom "_exit")) _ :: _) _] =>
           iApply wp_call_bind; [vx | exact (hi_find__exit _) | reflexivity |]; iNext;
           iApply (wp_glibc__exit w0 glibc_os_registry hge (fun n c H => H) (hi_sys_external _)); reflexivity
       | |- _ => iApply wp_ret_void; iNext; iApply ("HK" with "Htcb Hio Hlives")
       end.
Qed.

End rules.
