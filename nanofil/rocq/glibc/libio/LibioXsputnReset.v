From Glibc Require Import GlibcProgram.
(** The start of `c: _IO_setg` and `c: _IO_setp` in the
    `c: new_do_write` inlined in `c: _IO_new_file_xsputn`
    (LibioXsputnBase.v describes the function), block `c: iw_2.L70`,
    once the jump table's write returned:

    ```
    _IO_setg (fp, fp->_IO_buf_base, fp->_IO_buf_base, fp->_IO_buf_base);
    fp->_IO_write_base = fp->_IO_write_ptr = fp->_IO_buf_base;
    if (fp->_mode <= 0 && ...)
    ```

    [wp_xs_L70] stores the buffer's base as the read pointer, read end,
    read base, write pointer and write base, finds the mode narrow
    ([mode_sle]) and goes on at LibioXsputnFlags.v's [wp_xs_L122]. *)

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
  LibioXsputnSetp LibioXsputnFlags.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputn LibioDefaultXsputnBuf LibioDefaultXsputnBytes LibioDefaultXsputnCopy LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioLogic LibioXsputnBase LibioXsputnFlags LibioXsputnSetp OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** A narrow mode, 0 or -1, is at most 0 as a signed `c: int`. *)
Lemma mode_sle m : m = 0 \/ m = 2 ^ 32 - 1 ->
  (if sign_extension (2 ^ 32) (2 ^ 31) (m mod 2 ^ 32) <=? sign_extension (2 ^ 32) (2 ^ 31) (0 mod 2 ^ 32)
   then 1 else 0) = 1.
Proof. intros [-> | ->]; reflexivity. Qed.


Import LibioXsputnFlags LibioXsputnSetp LibioXsputnBase LibioDefaultXsputn LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioDefaultXsputnBytes LibioDefaultXsputnBuf LibioDefaultXsputnCopy SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

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


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A lookup premise, through the environment's puts. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** A pointer load of the buffer's base from the cell H. *)
Ltac ldb H := load "Hl" H "Hbl".

(** Block `c: iw_2.L70` on, r of the d bytes written of the T left:
    `c: _IO_setg` and `c: _IO_setp` store the buffer's base as every
    read and write pointer, the mode is narrow, and [wp_xs_L122] goes
    on. *)
Lemma wp_xs_L70 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys T d r e from Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> nb <> None ->
  c' = Obj b' \/ c' = Ro b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= r <= d -> 0 < d <= T -> T <= n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk14") e = Some (WPtr (mkPtr (fb + off_buf_end) (Obj fb))) ->
  lookup (TAtom "chk15") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.5") e = Some (WInt T) ->
  lookup (TAtom "iw_2.v67") e = Some (WInt r) -> lookup (TAtom "v175") e = Some (WInt d) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b' + so + (n - T)) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Enter (TAtom "iw_2.L70") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Hfb Hfal Hfend Hfreg Hnb Hc' Hb8' Hso Hyend Hyreg Hy Hr Hd HT Hv0 Hc0 Hc14 Hc15 Hv4 Hp5 Hv67 Hv175 Hp1.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp ((Hrp & Hre & Hrb & Hwb & Hbb & Hbe) & Hwp & Hwe & Hroom) (Hxf & HX) Hl' Hys HK".
  iDestruct "Hxf" as (fl f2 fd tw off m (Happ & Hf2 & Hfd & Hm & Hflags & Hfd31 & Hf2160)) "(Hfl & Hfl2 & Hfdc & Htw & Hoff & Hcol & Hmode & Herr)".
  iDestruct "Hmode" as "[%Hm32 Hmode]".
  iDestruct (wroom_cap with "Hroom") as (reg (Hb1 & Hb2 & Hcap)) "[Hbl Hroom]".
  step. step. step. check "Hl". ldb "Hbb". check "Hl". store "Hl" "Hrb". step. check "Hl". ldb "Hbb". check "Hl". store "Hl" "Hrp".
  step. check "Hl". ldb "Hbb". check "Hl". store "Hl" "Hre". step. step. check "Hl". ldb "Hbb". check "Hl". store "Hl" "Hwp".
  check "Hl". store "Hl" "Hwb". step. step. check "Hl". load_s32 "Hl" "Hmode". step.
  rewrite (mode_sle _ Hm). branch_as false.
  iDestruct ("Hroom" with "Hbl") as "Hroom".
  iApply (wp_xs_L122 Hmove Hmove_fn Hmove_sym eb X fb freg vb vreg nb wp we dq b' reg'
            so c' ys T d r fl f2 fd tw off m with "Hvt Hl Hvtp Hrp Hre Hrb Hwb Hbb Hbe Hwp Hwe Hroom Hfl Hfl2 Hfdc Htw
            Hoff Hcol [$Hmode //] Herr HX Hl' Hys HK"); try close_side.
  all: lk_fin.
Qed.

End rules.
