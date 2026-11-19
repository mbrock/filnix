(** Hello writes its text with `c: fputs` on stdout and stderr. Each
    call finds the stream idle, takes its lock, orients it, writes the
    string with the stream's string writer and releases the lock.
    LibioFputs.v proves glibc's `c: fputs` for any stream predicate that
    can be opened for locking and orientation and that the string writer
    accepts. This file supplies such a predicate for an idle stream and
    proves the contract [fputs_spec] from it. *)

From Glibc Require Import Unit_io_write_os Unit_libio_fileops_os Unit_libio_genops_os Unit_libio_iofputs_os.
From Glibc Require Import GlibcProgram GlibcTactics GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic MemLogic StringLogic.
From Glibc Require Import Fix OsBlocks OsWorld OsRegistry SysWrappers FileInv FileIdle FileTidy LibioLogic
  PrintfStreamInv LibioPutsInv
  WordString StrlenLogic AllocRo LibioSetb LibioFputsSpec LibioFputs LibioStreamTidy HiAtexitStringBytes.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.
Open Scope Z_scope.

(** ## A tidy stream at a known mode

    The proof of `c: fputs` changes the stream's mode when it orients
    the stream, so it needs a stream predicate that names the mode. A
    tidy stream hides its mode, which is narrow or not yet chosen. The
    predicate here is a tidy stream whose mode is a parameter. *)

Section stream.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** This predicate holds of a tidy stream whose mode is the given
    mode. Every other argument means what it means for [file_tidy]. *)
Definition fputs_stream (vb : Z) (self : ptr) (fd flags2 : Z) (fp : ptr) (mode : Z) (held : option Z) : iProp Σ :=
  ∃ fb freg st nb, ⌜fp = mkPtr fb (Obj fb) /\ fb mod 8 = 0 /\ 0 < fb /\
     fb + file_size <= r_end freg /\ r_end freg <= 2 ^ 63 /\ flags_ok st /\
     idle_ok fd (fs_with_flags2 st 0) /\ fs_flags2 st = flags2 /\
     fs_vtable st = mkPtr (vb + vt_file) (Ro vb) /\ buf_ptrs_ok fb nb (fs_ptrs st) /\
     short_idle nb st /\ fs_mode st = mode⌝ ∗
    live fb freg ∗ file_fields fb st ∗ lock_inv self (fs_lock st) held ∗ buf_idle nb ∗
    wide_idle vb (fs_wide st) (fs_codecvt st).

(** A tidy stream is this predicate at its current mode. *)
Lemma fputs_stream_tidy vb self fd flags2 fp held :
  file_tidy vb self fp fd flags2 held ⊣⊢ ∃ mode, fputs_stream vb self fd flags2 fp mode held.
Proof using Type.
  iSplit.
  - iIntros "(%fb & %freg & %st & %nb & %Hp & H)". iExists (fs_mode st), fb, freg, st, nb. iFrame "H".
    iPureIntro. tauto.
  - iIntros "(%mode & %fb & %freg & %st & %nb & %Hp & H)". iExists fb, freg, st, nb. iFrame "H".
    iPureIntro. tauto.
Qed.

(** Taking the lock and orienting the stream borrow its flags, lock,
    mode and jump-table pointer. A tidy stream uses the narrow jump
    table, so orientation can only choose the narrow mode, which a tidy
    stream allows. *)
Lemma fputs_stream_open vb self fd flags2 fp mode held :
  fputs_stream vb self fd flags2 fp mode held ⊢ file_open vb self (fputs_stream vb self fd flags2) fp mode held.
Proof using Type.
  iIntros "(%fb & %freg & %st & %nb & %Hp & Hl & Hf & Hk & Hb & Hw)".
  destruct Hp as (-> & Hal & Hfb & Hend & Hreg & Hok & Hi & Hf2 & Hvt & Hbok & Hsh & Hm).
  iDestruct "Hf" as "(%Hlen & Hfl & Hps & Hfd & Hfl2 & Hold & %Hcl & Hcol & Hlp & Hoff & Hcv & Hwd & Hfrl & Hfrb &
    Hmd & Htot & Hvtp)".
  iDestruct "Hk" as (lb lreg Hlb) "Hk".
  pose proof Hok as (Hflr & _ & _ & _ & Hul & _).
  pose proof Hi as (_ & _ & Hmd0 & _). cbn [fs_with_flags2 fs_mode] in Hmd0.
  iExists fb, freg, (fs_flags st), lb, vt_file. rewrite Hm Hvt Hlb. iFrame "Hl Hfl Hlp Hmd Hvtp".
  iSplitR.
  { iPureIntro. split_and!; try first [reflexivity | assumption | lia]. left. split; [rewrite -Hm; exact Hmd0 | reflexivity]. }
  iSplitL "Hk"; [iExists lb, lreg; iSplit; done|].
  iIntros (mode' held' Hmv') "Hl Hfl Hlp Hk Hmd Hvtp".
  assert (Hm' : mode' = 0 \/ mode' = 2 ^ 32 - 1).
  { destruct Hmv' as [[H _] | [_ H]]; [exact H | unfold vt_file, vt_wfile in H; lia]. }
  iExists fb, freg, (fs_with_mode st mode'), nb. unfold fs_with_mode, file_fields.
  cbn [fs_flags fs_ptrs fs_fileno fs_flags2 fs_old_offset fs_column fs_lock fs_offset fs_codecvt fs_wide
    fs_freeres_list fs_freeres_buf fs_mode fs_total fs_vtable]. rewrite Hlb Hvt.
  iSplitR.
  { iPureIntro. unfold flags_ok, idle_ok, short_idle, fs_with_flags2, fs_ptr in *.
    cbn [fs_flags fs_flags2 fs_ptrs fs_fileno fs_mode fs_lock fs_column fs_vtable] in *. rewrite Hlb in Hi. tauto. }
  iFrame "Hl Hb Hw Hk Hfl Hps Hfd Hfl2 Hold Hcol Hlp Hoff Hcv Hwd Hfrl Hfrb Hmd Htot Hvtp". iSplit; done.
Qed.

End stream.

(** ## The contract

    The string writer of a tidy stream is [wp_xsputn_tidy]. It takes the
    string as bytes at the caller's share, so the proof lends the bytes
    of the word-aligned string to it and takes them back. *)

Section has_spec.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Context (Hreg : holds_os registry) (Hext : sys_external ge) (Hfree : free_rule w0 registry ge).
Context `{!Defines ge "__GI__IO_doallocbuf" Unit_libio_genops_os.fn___GI__IO_doallocbuf}.
Context `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}.
Context `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}.
Context `{!Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}.
Context (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  (Hov : ge_fn ge "_IO_new_file_overflow" Unit_libio_fileops_os.fn__IO_new_file_overflow)
  (Hxs_fn : ge_fn ge "_IO_new_file_xsputn" Unit_libio_fileops_os.fn__IO_new_file_xsputn)
  (Hxs_heap : xsputn_heap_rule).
Context (Hstrlen : find_fn ge (TAtom "__GI_strlen") = Some (Defined glibc_strlen))
  (Herrno : lookup (TAtom "__libc_errno") (ge_globals ge) = ow_errno w0)
  `{!Defines ge "fputs" Unit_libio_iofputs_os.fn___GI__IO_fputs}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).

(** The string writer accepts the idle stream with its lock held. It
    returns the stream at some mode, the caller's string and the
    thread's error cell. *)
Lemma fputs_stream_xsputn vb fd flags2 eb :
  Z.land flags2 2 = 0 -> ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  xsputn_spec_for w0 registry ge (fputs_stream vb (ow_self w0) fd flags2)
    (fun _ fp _ held => ∃ mode, fputs_stream vb (ow_self w0) fd flags2 fp mode held)%I
    (errno_any eb ∗ fputs_ro vb ∗ malloc_ro).
Proof using Type*.
  intros H2 He Hin fr fp p dq s Φ Hfr. assert (Hg := Herrno). rewrite He in Hg. iIntros "Hf Hstr (Herr & #Hro & #Hm) HK".
  iAssert (file_tidy vb (ow_self w0) fp fd flags2 (Some 0)) with "[Hf]" as "Hf".
  { iApply fputs_stream_tidy. iExists _. iExact "Hf". }
  iDestruct (hi_word_string_bytes with "Hstr") as (b reg so (Hp & Hcap & Hb & Hb8 & Hso & Hbend & Hbreg & Hys))
    "(Hbl & Hys & Hback)".
  rewrite Hp in Hfr.
  iApply (wp_xsputn_tidy Hreg Hext Hfree Hfw Hov Hxs_heap fr vb (ow_self w0) fp fd flags2 (Some 0) dq b reg so
    (ptr_cap p) s eb with "Hro Hm Hf Herr Hbl Hys"); try first [assumption | lia | left; assumption].
  iNext. iIntros (r Hr) "Hf Herr Hbl Hys". iDestruct ("Hback" with "Hbl Hys") as "Hstr".
  iApply ("HK" with "[%] [Hf] Hstr [$Herr $Hro $Hm]"); [destruct Hr; lia|].
  iApply (fputs_stream_tidy with "Hf").
Qed.

(** `c: fputs` meets its contract on an idle stream. The stream lock
    records its owner's thread pointer, and glibc's lock macros treat a
    null owner as no owner, so the thread pointer must not be null. *)
Lemma fputs_has_spec (Hself : ptr_addr (ow_self w0) <> 0) :
  HasSpec registry (os_wi w0) ge (TAtom "fputs") fputs_spec.
Proof using Type*.
  intros [vb p dq s fp fd eb]. exists Unit_libio_iofputs_os.fn___GI__IO_fputs. split; [exact defines|]. split; [eexists; reflexivity|].
  intros fr Φ Hfr. cbn [fs_pre fs_post fs_args fputs_spec fi_vb fi_p fi_dq fi_s fi_fp fi_fd fi_eb].
  iIntros "([%He %Hin] & Hstr & Hf & Herr & #Hro & #Hm) HK".
  iPoseProof "Hro" as (vreg sb sreg) "[#Hvt #Hs]".
  iDestruct (file_idle_tidy with "Hf") as (flags2 [H2 H32]) "Hf".
  iDestruct (fputs_stream_tidy with "Hf") as (mode) "Hf".
  iApply (wp_glibc__IO_fputs Hreg Hext vb vreg (errno_any eb ∗ fputs_ro vb ∗ malloc_ro) Hxs_fn
    (fputs_stream vb (ow_self w0) fd flags2) (fputs_stream_open vb (ow_self w0) fd flags2)
    (fputs_stream_xsputn vb fd flags2 eb H2 He Hin) fr p dq s fp mode sb sreg
    with "Hvt Hs Hstr Hf [$Herr $Hro $Hm]"); try assumption.
  iNext. iIntros (r Hr) "Hstr [%m Hf] (Herr & _ & _)".
  iApply "HK". iExists r. iSplit; [iPureIntro; split; [reflexivity | exact Hr]|]. iFrame "Hstr Herr".
  iApply file_idle_tidy. iExists flags2. iSplit; [done|]. iApply fputs_stream_tidy. iExists m. iExact "Hf".
Qed.

End has_spec.
