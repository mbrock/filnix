From Glibc Require Import GlibcProgram.
(** The flush of `c: _IO_new_file_xsputn` (LibioXsputnBase.v
    describes the function), from block `c: L96`, once the bytes that
    fit are in the buffer and T are left:

    ```
    if (to_do + must_flush > 0)
      { if (_IO_OVERFLOW (f, EOF) == EOF)
          return to_do == 0 ? EOF : n - to_do;
        ... }
    return n - to_do;
    ```

    [wp_xs_L96] returns n when nothing is left and no newline asks for
    a flush; else it calls `c: _IO_new_file_overflow(f, EOF)` through
    the jump table ([overflow_spec]), returns when that fails and goes
    on at LibioXsputnWrite.v's [wp_xs_L132] when it succeeds. *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioReadCode LibioDoWriteCode LibioXsputnCode LibioDefaultXsputnCopy
  LibioDefaultXsputnBuf LibioDefaultXsputnTail LibioDefaultXsputn LibioXsputnBase
  LibioXsputnSetp LibioXsputnFlags
  LibioXsputnReset LibioXsputnCall LibioXsputnDo
  LibioXsputnWrite.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputn LibioDefaultXsputnBuf LibioDefaultXsputnBytes LibioDefaultXsputnCopy LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioLogic LibioXsputnBase LibioXsputnCall LibioXsputnDo LibioXsputnFlags LibioXsputnReset LibioXsputnSetp LibioXsputnWrite OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L96` of `c: _IO_new_file_xsputn`, after its phis. *)
Definition xs_L96 : block := Eval vm_compute in
  match find_block (TAtom "L96") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L96") [] [] JRetVoid end.


Import LibioXsputnWrite LibioXsputnDo LibioXsputnCall LibioXsputnReset LibioXsputnFlags LibioXsputnSetp LibioXsputnBase LibioDefaultXsputn LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioDefaultXsputnBytes LibioDefaultXsputnBuf LibioDefaultXsputnCopy SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The genv's copies and `c: __GI__IO_default_xsputn` are glibc's, as
    LibioXsputnBase.v asks. *)
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  `{Hcpy : !Defines ge "__GI_memcpy" glibc_memcpy}
  `{Hpcpy : !Defines ge "__GI_mempcpy" glibc_mempcpy}
  `{Hdxf : !Defines ge "__GI__IO_default_xsputn" glibc__IO_default_xsputn}.
(** The jump table's write is glibc's `c: _IO_new_file_write`, which
    writes bytes at a share ([fwq_spec]). *)
Context (Hfw : ge_fn ge "_IO_new_file_write" glibc__IO_new_file_write)
  (Hfwq : fwq_spec w0 registry ge).


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise, through the environment's puts. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** Block `c: L96` on, T of the n bytes left from s and the flush
    flag mf: the return, or the overflow and then [wp_xs_L132]. *)
Lemma wp_xs_L96 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys T mf e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= T <= n -> (T < n -> nb <> None) -> mf = 0 \/ mf = 1 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.5") e = Some (WInt T) ->
  lookup (TAtom "pr.6") e = Some (WInt mf) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b' + so + (n - T)) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Exec (TAtom "L96") (b_insts xs_L96) (b_jump xs_L96)))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Heb Hfb Hfal Hfend Hfreg Hc' Hb'0 Hb8' Hso Hyend Hyreg Hy HT Hprogress Hmf Hv0 Hc0 Hv4 Hp5 Hp6 Hp1.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp Hwb Hos Hl' Hys HK".
  cbn [xs_L96 b_insts b_jump]. step. step. step.
  destruct (Z.eq_dec (T + mf) 0) as [Htm | Htm].
  { (* Nothing left, no flush: L122 returns n. *)
    assert (T = 0) by lia. assert (mf = 0) by lia. subst T mf.
    branch_as true. step. step. iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' Hys"). split; [right; unwrap2; lia | exact Hprogress]. }
  assert (Htm' : 0 < T + mf) by lia. clear Htm.
  assert (Hse : sign_extension (2 ^ 32) (2 ^ 31) (mf mod 2 ^ 32) = mf) by (destruct Hmf as [-> | ->]; reflexivity).
  assert (Hmf' : 0 <= mf <= 1) by lia. rewrite Hse. branch_as false.
  (* L120: the jump table, checked against `c: __io_vtables`. *)
  iPoseProof (vtables_slot ge vb vreg slot_overflow "_IO_new_file_overflow" with "Hvt") as "#Hsw"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_overflow")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfo). done. }
  iPoseProof "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)".
  unfold io_vtables_size in Hvend.
  step. step. norm. check "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". step. step. step. step. step. branch_as true.
  (* iw_1.join: the overflow slot and the call of `c: EOF`. *)
  step. step. norm.
  check_read_dq "Hvl'" by ar.
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsw Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hfo) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfo) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfo) | apply (ge_fn_check _ _ _ Hfo) | vx |
    apply (ge_fn_find _ _ _ Hfo) | reflexivity | reflexivity |].
  iNext.
  iApply (Hov with "Hvt Hl Hvtp Hwb Hos"); [reflexivity | right; reflexivity | exact Hfb | exact Hfal
    | unfold file_size; lia | exact Hfreg |].
  iNext. iIntros (r nb' wp' we' [Hr Hnb]) "Hl Hvtp Hwb Hos". resume.
  assert (Hr32 : r = 2 ^ 32 - 1 \/ r = 0) by (destruct Hr as [-> | ->]; [left | right]; reflexivity).
  rewrite (Z.mod_small r); [|lia]. step.
  destruct Hr32 as [-> | ->].
  - (* `c: EOF`: L130 returns `c: EOF` or n - T. *)
    branch_as false. step. step.
    destruct (Z.eq_dec T 0) as [-> | HT0].
    + branch_as false. step. iApply wp_ret; [reflexivity | vx |]. iNext.
      iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' Hys"). split; [left; reflexivity | intros _; exact Hnb].
    + branch_as true. step. step. step. step. iApply wp_ret; [reflexivity | vx |]. iNext.
      iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' Hys"). split; [right; unwrap2; lia | intros _; exact Hnb].
  - (* The flush went: L132. *)
    branch_as true.
    iApply (wp_xs_L132 Hmove Hmove_fn Hmove_sym Hfw Hfwq eb X fb freg vb vreg nb' wp' we'
              dq b' reg' so c' ys T with "Hvt Hl Hvtp Hwb Hos Hl' Hys HK"); try close_side.
    all: unfold n in *; try lia. all: lk_fin.
Qed.

End rules.
