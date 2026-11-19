(** GNU Hello checks errno when closing an empty stream fails and clears
    errno when an earlier stream error accompanies a successful close.
    The OS invariant already keeps these four bytes in a live global
    object. These rules use that fact without acquiring a new lifetime
    token or changing the stream invariant. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic
  HelloClose.
From Glibc Require Import Unit_io_close_nocancel_os Unit_io_write_os Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_fileops_os.
From Glibc Require Import Unit_libio_genops_os Unit_libio_iofclose_os Unit_nptl_libcZ2dcleanup_os.
From Glibc Require Import GlibcProgram GlibcTactics LibioTactics OsBlocks OsWorld
  FileInv LibioLogic HelloCloseStream LeavesLogic OsRegistry SysWrappers AllocLogic.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L FileInv LibioLogic LibioCloseSteps
  LibioFcloseTail.
Open Scope Z_scope.

(** The address and four-byte extent come from the OS invariant and the
    runtime's address-space law, not from additional caller ownership. *)
Definition close_errno_mem eb m :=
  ∃ reg, live_at m eb reg ∧ 0 <= eb ∧ eb + 4 <= r_end reg ∧ r_end reg <= 2 ^ 48.

Section errno.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb))).

(** Every program step can recover errno's physical bounds from the
    current state interpretation, including after collection or a call. *)
Lemma close_errno_mem_facts σ : heap_interp (os_wi w0) σ -∗ ⌜close_errno_mem eb (ls_mem σ)⌝.
Proof using Type*.
  iIntros "Hσ". iDestruct (os_heap_errno w0 σ eb Herr with "Hσ") as %[_ (reg & Hl & _ & _ & Hend)].
  iDestruct "Hσ" as (h) "[_ %Hs]". destruct Hs as (_ & _ & Hr & _).
  destruct (R.address_space _ _ Hr eb reg (proj1 Hl)) as [Hb He].
  iPureIntro. exists reg. split; [exact Hl|]. cbn in Hend. repeat split; lia.
Qed.

(** The read and write checks validate the same four-byte errno range.
    Neither check consumes or manufactures an object lifetime token. *)
Lemma wp_close_errno_check f e ls l d mode v rest j Φ :
  value_x ge e P v = Some (WPtr (mkPtr eb (Obj eb))) ->
  ▷ WP (ERun (mkFrame f (put d (WPtr (mkPtr eb (Obj eb))) e) ls None (Exec l rest j)) : gexpr) {{ Φ }} -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let d A (Check 0 4 mode 1) [v] :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hv. iIntros "HK".
  iApply (wp_read_with registry (os_wi w0) ge True%I (close_errno_mem eb) _ _ [] with "[] [HK]").
  - iIntros (σ) "Hσ _". iApply (close_errno_mem_facts with "Hσ").
  - intros m fuel (reg & Hl & Hb & Hend & He).
    apply rule_let with (classes := [P]) (xs := [WPtr (mkPtr eb (Obj eb))]);
      [reflexivity | reflexivity | cbn; rewrite Hv; reflexivity |].
    apply op_check. cbn [ptr_addr ptr_cap]. unfold raw_address.
    rewrite Z.add_0_r Z.mod_small; [|lia].
    apply (access_obj _ _ reg); [exact (proj1 Hl)|lia|lia|apply Z.mod_1_r].
  - done.
  - iNext. iIntros "_". iExact "HK".
Qed.

(** A signed load reads exactly the four owned errno bytes and keeps
    them available for later tests or stores. *)
Lemma wp_close_errno_load f e ls l dst v rest j bs Φ :
  value_x ge e A v = Some (WPtr (mkPtr eb (Obj eb))) -> length bs = 4%nat ->
  bytes eb 0 bs -∗
  ▷ (bytes eb 0 bs -∗ WP (ERun (mkFrame f (put dst (WInt (close_w bs)) e) ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (Let dst W (RawLoad (LdNarrow Sw) 0) [v] :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hv Hlen. iIntros "Hb HK".
  iApply (wp_read_with registry (os_wi w0) ge (bytes eb 0 bs)
    (fun m => close_errno_mem eb m ∧ all_agree m (byte_ps eb 0 bs)) _ _ [] with "Hb HK").
  - iIntros (σ) "Hσ Hb". iDestruct (close_errno_mem_facts with "Hσ") as %Hmem.
    iDestruct (pts_facts with "Hσ Hb") as %[Hbs _]. iPureIntro. auto.
  - intros m fuel [(reg & Hl & Hbase & Hend & He) Hbs].
    destruct bs as [|a [|b [|c [|d [|u bs]]]]]; try discriminate Hlen.
    pose proof (byte_ps_agree _ _ _ _ _ 0%nat a Hl Hbs eq_refl) as (E0 & _).
    pose proof (byte_ps_agree _ _ _ _ _ 1%nat b Hl Hbs eq_refl) as (E1 & _).
    pose proof (byte_ps_agree _ _ _ _ _ 2%nat c Hl Hbs eq_refl) as (E2 & _).
    pose proof (byte_ps_agree _ _ _ _ _ 3%nat d Hl Hbs eq_refl) as (E3 & _).
    apply rule_let with (classes := [A]) (xs := [WPtr (mkPtr eb (Obj eb))]);
      [reflexivity | reflexivity | cbn; rewrite Hv; reflexivity |].
    assert (Ha : raw_address eb 0 = eb) by (unfold raw_address; rewrite Z.add_0_r; apply Z.mod_small; lia).
    assert (Haccess : access_res m eb (Obj eb) 4 Read 1 = Some ok).
    { apply (access_obj _ _ reg); [exact (proj1 Hl)|lia|lia|apply Z.mod_1_r]. }
    cbn - [access_res raw_address load_bytes extension]. rewrite Ha.
    unfold int_load_res. cbn - [access_res load_bytes extension]. rewrite Haccess.
    change (Some (OpRes (RVal (WInt (extension Sw
      (((m_bytes m (eb + 3) * 256 + m_bytes m (eb + 2)) * 256 +
        m_bytes m (eb + 1)) * 256 + m_bytes m (eb + 0)) mod 2 ^ 32))) m) =
      Some (OpRes (RVal (WInt (close_w [a; b; c; d]))) m)).
    cbn [Z.of_nat Z.add] in E0, E1, E2, E3.
    rewrite E0 E1 E2 E3. reflexivity.
Qed.

(** Clearing errno changes four bytes without changing their shadow
    capabilities or any other memory. The public store rule preserves
    the caller's ownership, and the OS store law keeps errno live. *)
Lemma wp_close_errno_zero f e ls l a rest j bs Φ :
  value_x ge e A a = Some (WPtr (mkPtr eb (Obj eb))) -> length bs = 4%nat ->
  bytes eb 0 bs -∗
  ▷ (bytes eb 0 (le_bytes 0 4) -∗ WP (ERun (mkFrame f e ls None (Exec l rest j)) : gexpr) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec l (RawStore Ww 0 (Const 0) a :: rest) j)) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Ha Hlen. iIntros "Hb HK".
  iApply (wp_write_with registry (os_wi w0) ge True%I (close_errno_mem eb)
    (byte_ps eb 0 bs) (byte_ps eb 0 (le_bytes 0 4)) _ _ [] (fun m => store_bytes m eb 4 0) with "Hb [] [HK]").
  - rewrite !byte_ps_keys length_le_bytes Hlen. reflexivity.
  - iIntros (σ) "Hσ _". iApply (close_errno_mem_facts with "Hσ").
  - intros m fuel (Hbs & Hd & _) (reg & Hl & Hb & Hend & He).
    destruct (store_after m eb reg 0 bs 0 Hd Hl Hbs) as [Hnew Hframe].
    rewrite Hlen Z.add_0_r in Hnew, Hframe. cbn in Hnew, Hframe.
    split; [|split; [reflexivity|split; [|split]]].
    + apply rule_raw_store with (vk := W) (x := WInt 0) (p := mkPtr eb (Obj eb));
        [reflexivity|reflexivity|exact Ha|].
      cbn - [access_res raw_address store_bytes]. unfold raw_address. rewrite Z.add_0_r Z.mod_small; [|lia].
      rewrite (access_obj _ _ reg); [reflexivity|exact (proj1 Hl)|lia|lia|apply Z.mod_1_r].
    + apply store_bytes_kept. intros x Hx. exists eb, reg. split; [exact (proj1 Hl)|lia].
    + exact Hnew.
    + rewrite byte_ps_keys Hlen in Hframe.
      rewrite byte_ps_keys length_le_bytes. exact Hframe.
  - intros m w h Hps Hw. apply (os_wi_store w0 m); [reflexivity| |exact Hw].
    intros key v Hin. apply byte_ps_elem in Hin as (i & x & Hi & -> & ->). done.
  - done.
  - iNext. iIntros "Hb _". iApply ("HK" with "Hb").
Qed.
End errno.

Section paths.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (eb : Z) (Herr : ow_errno w0 = Some (mkPtr eb (Obj eb)))
  (Hglobal : lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)))
  `{!Defines ge "__errno_location" errno_location_fn}.

(** The actual clear block returns EOF after storing zero. The auxiliary
    capability pieces remain unchanged, so the caller receives errno_any. *)
Lemma wp_close_stream_L38 e (E : iProp Σ) Φ :
  errno_any eb -∗ E -∗
  (errno_any eb -∗ E -∗ Φ (Ret (WInt (2 ^ 32 - 1)))) -∗
  WP (ERun (mkFrame close_stream_fn e [] None
    (Exec (TAtom "L38") (b_insts (cs_block "L38")) (b_jump (cs_block "L38")))) : gexpr) {{ Φ }}.
Proof using Type*.
  iIntros "Herr HE HK".
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_glibc_errno_location registry (os_wi w0) ge _ _ Hglobal). resume.
  iApply (wp_close_errno_check eb Herr); [vx|]. iNext.
  iDestruct "Herr" as (bs cs [Hbs Hcs]) "Hp".
  rewrite pts_app. iDestruct "Hp" as "[Hb Haux]".
  iApply (wp_close_errno_zero eb Herr with "Hb"); [vx|exact Hbs|].
  iNext. iIntros "Hb". iApply wp_goto. iNext.
  iApply (wp_enter _ _ _ _ _ _ _ _ (cs_block "L40")); [reflexivity|reflexivity|]. iNext.
  iApply wp_ret; [reflexivity|reflexivity|]. iNext.
  iApply ("HK" with "[Hb Haux] HE"). iExists (le_bytes 0 4), cs.
  rewrite pts_app. iFrame. iPureIntro. rewrite length_le_bytes. auto.
Qed.

(** The read block compares the signed four-byte errno value with EBADF.
    Its saved fclose result still controls whether the shared return
    path clears errno. This proof accepts any saved integer, not only
    successful closes. *)
Lemma wp_close_stream_L27 e k (E : iProp Σ) Φ :
  lookup (TAtom "v14") e = Some (WInt k) ->
  errno_any eb -∗ E -∗
  (∀ r, ⌜r = 0 ∨ r = 2 ^ 32 - 1⌝ -∗ errno_any eb -∗ E -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (mkFrame close_stream_fn e [] None
    (Exec (TAtom "L27") (b_insts (cs_block "L27")) (b_jump (cs_block "L27")))) : gexpr) {{ Φ }}.
Proof using Type*.
  intros Hk. iIntros "Herr HE HK".
  iApply wp_call_bind; [vx|apply defines|reflexivity|]. iNext.
  iApply (wp_glibc_errno_location registry (os_wi w0) ge _ _ Hglobal). resume.
  iApply (wp_close_errno_check eb Herr); [vx|]. iNext.
  iDestruct "Herr" as (bs cs [Hbs Hcs]) "Hp".
  rewrite pts_app. iDestruct "Hp" as "[Hb Haux]".
  iApply (wp_close_errno_load eb Herr with "Hb"); [vx|exact Hbs|].
  iNext. iIntros "Hb".
  iAssert (errno_any eb) with "[Hb Haux]" as "Herr".
  { iExists bs, cs. rewrite pts_app. iFrame. auto. }
  step. iApply wp_goto. iNext.
  iApply (wp_enter _ _ _ _ _ _ _ _ (cs_block "L22")); [reflexivity|vx|]. iNext.
  let b := eval vm_compute in (cs_block "L22") in change (cs_block "L22") with b.
  cbn [b_insts b_jump].
  repeat first [step | branch_cases].
  all: lazymatch goal with
  | |- context [Call _ (Global (TAtom "__errno_location")) _] =>
      iApply (wp_close_stream_L38 with "Herr HE"); iIntros "Herr HE";
      iApply ("HK" with "[%] Herr HE"); auto
  | |- _ => iApply wp_ret; [reflexivity|reflexivity|]; iNext;
      iApply ("HK" with "[%] Herr HE"); auto
  end.
Qed.

(** The caller no longer needs to prove either errno block. Both blocks
    preserve the cleanup state and remaining streams owned through E. *)
Lemma close_stream_errno_complete (E : iProp Σ) Φ :
  (∀ r, ⌜r = 0 ∨ r = 2 ^ 32 - 1⌝ -∗ (errno_any eb ∗ E) -∗ Φ (Ret (WInt r))) -∗
  close_stream_errno_paths (errno_any eb ∗ E) Φ.
Proof using Type*.
  iIntros "HK" (e l [-> | ->] [k Hk]) "[Herr HE]".
  - iApply (wp_close_stream_L27 with "Herr HE"); [exact Hk|].
    iIntros (r Hr) "Herr HE". iApply ("HK" with "[%] [$Herr $HE]"). exact Hr.
  - iApply (wp_close_stream_L38 with "Herr HE").
    iIntros "Herr HE". iApply ("HK" with "[%] [$Herr $HE]"). auto.
Qed.
End paths.

Section close.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation gexpr := (language.expr (nanofil_lang registry ge)).
Context (Hreg : holds_os registry) (Hext : sys_external ge).
Context `{!Defines ge "__fpending" Unit_libio___fpending_os.fn___fpending}
  `{!Defines ge "ferror" Unit_libio_ferror_os.fn__IO_ferror}
  `{!Defines ge "fclose" Unit_libio_iofclose_os.fn__IO_new_fclose}
  `{!Defines ge "__GI___write" Unit_io_write_os.fn___GI___libc_write}
  (Hfw : ge_fn ge "_IO_new_file_write" Unit_libio_fileops_os.fn__IO_new_file_write)
  `{!Defines ge "free" free_fn}
  (Hfh : frees_heap (ge_free ge))
  (Hzf : find_fn ge zgc_free_name = None)
  (Hzg : lookup zgc_free_name (ge_globals ge) = None)
  `{!Defines ge "__GI___close_nocancel" Unit_io_close_nocancel_os.fn___GI___close_nocancel}
  (Hfc : ge_fn ge "__GI__IO_file_close" Unit_libio_fileops_os.fn___GI__IO_file_close)
  `{!Defines ge "__GI__IO_setb" Unit_libio_genops_os.fn___GI__IO_setb}
  `{!Defines ge "_IO_new_do_write" Unit_libio_fileops_os.fn__IO_new_do_write}
  `{!Defines ge "__GI__IO_unsave_markers" Unit_libio_genops_os.fn___GI__IO_unsave_markers}
  `{!Defines ge "__GI___libc_cleanup_push_defer" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer}
  `{!Defines ge "__GI___libc_cleanup_pop_restore" Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore}
  `{!Defines ge "__GI__IO_un_link" Unit_libio_genops_os.fn___GI__IO_un_link}
  `{!Defines ge "__GI__IO_default_finish" Unit_libio_genops_os.fn___GI__IO_default_finish}
  (Hff : ge_fn ge "_IO_new_file_finish" Unit_libio_fileops_os.fn__IO_new_file_finish)
  `{!Defines ge "_IO_file_close_maybe_unlink" Unit_libio_fileops_os.fn__IO_file_close_maybe_unlink}
  `{!Defines ge "__errno_location" errno_location_fn}.

(** The full stdout rule removes stdout from the stream list and returns
    zero or EOF with cleanup, remaining stream lifetimes, errno and E.
    It uses the same stream shape and fclose links as the conditional
    rule, adding only the actual errno function and global links.
    No error branch is delegated to a caller continuation. *)
Lemma wp_hello_close_stream_stdout_full pre post fb freg fl f2 fd tw off bb breg i xs rp rb we be eb vb vreg
    lb lbreg sb sreg fcp pin md (E : iProp Σ) Φ :
  let n := Z.of_nat (length xs) in
  let fp := mkPtr fb (Obj fb) in
  let wb := mkPtr (bb + i) (Obj bb) in
  let base := mkPtr bb (Obj bb) in
  let Q := (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (pre ++ post) ∗
    ([∗ list] g ∈ pre ++ post, stream_life g) ∗ errno_any eb ∗ E)%I in
  lookup (TAtom "__libc_errno") (ge_globals ge) = Some (mkPtr eb (Obj eb)) ->
  lookup (TAtom "_IO_2_1_stdout_") (ge_globals ge) = Some fp ->
  lookup (TAtom "_IO_2_1_stdin_") (ge_globals ge) = Some pin -> ptr_addr pin <> fb -> 0 <= ptr_addr pin < 2 ^ 64 ->
  lookup (TAtom "glibc_genops#flush_cleanup") (ge_globals ge) = Some fcp -> 0 <= ptr_addr fcp < 2 ^ 64 ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 2 = 0 -> Z.land f2 32 = 0 -> Z.land f2 io_need_lock = 0 -> 0 <= f2 < 2 ^ 32 ->
  In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  0 <= fl < 2 ^ 32 -> Z.land fl io_is_appending = 0 -> Z.land fl io_no_writes = 0 ->
  Z.land fl io_currently_putting <> 0 -> Z.land fl io_user_buf = 0 -> has fl io_user_lock = false ->
  has fl io_linked = true -> has fl io_is_filebuf = true ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> r_kind breg = Heap ->
  0 < bb -> 0 <= i -> bb + i + n <= r_end breg -> r_end breg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs -> 0 <= ptr_addr be < 2 ^ 64 -> ptr_cap be = Obj bb -> 0 < lb ->
  md = 0 ∨ md = 2 ^ 32 - 1 ->
  vtables_ro ge vb vreg -∗ single_ro ge sb sreg -∗ tcb_cleanup_inv (ow_self w0) -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
  icell fb off_total_written tw -∗ icell fb off_offset off -∗ live bb breg -∗ bytes bb i xs -∗ errno_any eb -∗
  pcell fb off_read_ptr rp -∗ pcell fb 16 wb -∗ pcell fb 24 rb -∗ pcell fb off_write_base wb -∗
  pcell fb off_write_ptr (mkPtr (bb + i + n) (Obj bb)) -∗ pcell fb off_write_end we -∗
  pcell fb off_buf_base base -∗ pcell fb off_buf_end be -∗
  bytes fb off_column [0; 0] -∗ int_cell fb off_mode md -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  pcell fb 72 null -∗ pcell fb 80 null -∗ pcell fb 96 null -∗
  pcell fb off_lock (mkPtr lb (Obj lb)) -∗ lock_state lb lbreg 0 0 null -∗
  io_list_inv ge (pre ++ fp :: post) -∗ ([∗ list] g ∈ pre ++ post, stream_life g) -∗ E -∗
  (∀ r, ⌜r = 0 ∨ r = 2 ^ 32 - 1⌝ -∗ Q -∗ Φ (Ret (WInt r))) -∗
  WP (ERun (hello_close_stream_frame fp) : gexpr) {{ Φ }}.
Proof using Type*.
  intros n fp wb base Q Herrno Hgout Hgin Hin Hinr Hfcg Hfcr Hfb Hfal Hfend Hfreg Hf22 Hf232 Hnl Hf2r Hfd
    Hfdr Hfl Happ Hnw Hcp Hub Hul Hlnk Hfb8 He Hbk Hb Hi Hbend Hbreg Hy Hbe Hbec Hlb Hmd.
  iIntros "Hvt Hs Htcb Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol
    Hmode Hvtp H72 H80 H96 Hlp Hlk Hio Hlives HE HK".
  iApply (wp_hello_close_stream_stdout Hreg Hext Hfw Hfh Hzf Hzg Hfc Hff
    pre post fb freg fl f2 fd tw off bb breg i xs rp rb we be eb vb vreg lb lbreg sb sreg fcp pin md E
    with "Hvt Hs Htcb Hl Hfl Hfl2 Hfd Htw Hoff Hbl Hxs Herr Hrp Hre Hrb Hwb Hwp Hwe Hbase Hbend Hcol
      Hmode Hvtp H72 H80 H96 Hlp Hlk Hio Hlives HE"); try assumption.
  iSplit; [|iExact "HK"].
  iIntros (e l Hl' [k Hk]) "(Htcb & Hio & Hlives & Herr & HE)".
  destruct Hl' as [-> | ->].
  - iApply (wp_close_stream_L27 eb He Herrno e k
      (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (pre ++ post) ∗
       ([∗ list] g ∈ pre ++ post, stream_life g) ∗ E)%I
      with "Herr [Htcb Hio Hlives HE] [HK]"); [exact Hk|iFrame|].
    iIntros (r Hr) "Herr (Htcb & Hio & Hlives & HE)".
    iApply ("HK" with "[%] [$Htcb $Hio $Hlives $Herr $HE]"). exact Hr.
  - iApply (wp_close_stream_L38 eb He Herrno e
      (tcb_cleanup_inv (ow_self w0) ∗ io_list_inv ge (pre ++ post) ∗
       ([∗ list] g ∈ pre ++ post, stream_life g) ∗ E)%I
      with "Herr [Htcb Hio Hlives HE] [HK]"); [iFrame|].
    iIntros "Herr (Htcb & Hio & Hlives & HE)".
    iApply ("HK" with "[%] [$Htcb $Hio $Hlives $Herr $HE]"). auto.
Qed.
End close.
