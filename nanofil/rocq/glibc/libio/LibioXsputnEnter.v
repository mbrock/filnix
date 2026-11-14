From Glibc Require Import GlibcProgram.
(** The stream writer computes how many bytes fit before it must flush.
    Line buffering also checks whether those bytes contain a newline.

    ```
    if ((f->_flags & _IO_LINE_BUF) && (f->_flags & _IO_CURRENTLY_PUTTING))
      { count = f->_IO_buf_end - f->_IO_write_ptr;
        if (count >= n)
          { for (p = s + n; p > s; )
              if (p[-1] == '\n') { count = p - s; must_flush = 1; break; } else p--; } }
    else if (f->_IO_write_end > f->_IO_write_ptr)
      count = f->_IO_write_end - f->_IO_write_ptr;
    ```

    The line-buffered path scans backward for the last newline that fits.
    The other path uses the space between the write pointer and write end.
    Both paths then continue with the buffer-filling proof. *)

From Glibc Require Import GlibcTactics LibioTactics GlibcSymFunc.
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
  LibioXsputnWrite LibioXsputnFlush
  LibioXsputnFill.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputn LibioDefaultXsputnBuf LibioDefaultXsputnBytes LibioDefaultXsputnCopy LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioLogic LibioXsputnBase LibioXsputnCall LibioXsputnDo LibioXsputnFill LibioXsputnFlags LibioXsputnFlush LibioXsputnReset LibioXsputnSetp LibioXsputnWrite OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.


Import LibioXsputnFill LibioXsputnFlush LibioXsputnWrite LibioXsputnDo LibioXsputnCall LibioXsputnReset LibioXsputnFlags LibioXsputnSetp LibioXsputnBase LibioDefaultXsputn LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioDefaultXsputnBytes LibioDefaultXsputnBuf LibioDefaultXsputnCopy SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic LibioCloseSteps.

(** A stream's write pointer and write end lie in its buffer, with its
    capability, and the buffer ends at an address. *)
Lemma wroom_ptrs `{!gen_heapGS piece pval Σ} nb wp we :
  wroom nb wp we ⊢ ⌜ptr_cap wp = ptr_cap (nb_base nb) /\ ptr_cap we = ptr_cap (nb_base nb) /\
    0 <= ptr_addr wp <= ptr_addr (nb_end nb) /\ 0 <= ptr_addr we <= ptr_addr (nb_end nb) /\
    ptr_addr (nb_end nb) <= 2 ^ 63 /\ ptr_addr (nb_end nb) - ptr_addr wp < 2 ^ 63⌝ ∗ wroom nb wp we.
Proof.
  destruct nb as [[b sz] |]; cbn.
  - iIntros "(%reg & %xs & %cs & %Hok & H)". iSplit; [|iExists reg, xs, cs; iFrame; done]. iPureIntro.
    destruct Hok as (H1 & H2 & H3 & H4 & H5 & _ & _ & _ & [H6 H7] & [H8 H9] & _). split_and!; first [assumption | lia].
  - iIntros "[-> ->]". iSplit; [|done]. iPureIntro. cbn. split_and!; first [reflexivity | lia].
Qed.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The program supplies glibc's copy routines and default stream writer.
    Memory moves use the registered external contract. *)
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


(** The execution goal uses the language selected by the program context. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** Environment lookups reduce through earlier assignments before arithmetic identifies the resulting values. *)
Ltac lk_fin := first [assumption | lookups; first [reflexivity | do 2 f_equal; unwrap2; lia
  | do 3 f_equal; cbn [ptr_addr]; unfold off_write_end, off_buf_base, off_buf_end; unwrap2; lia]].

(** The ordinary path computes the space up to the write end, or zero when no space remains. *)
Lemma wp_xs_L19 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 < n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr (b' + so) c')) ->
  lookup (TAtom "v4") e = Some (WInt n) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Enter (TAtom "L19") (Some (TAtom "L25")))) : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Heb Hfb Hfal Hfend Hfreg Hc' Hb'0 Hb8' Hso Hyend Hyreg Hy Hn0 Hv0 Hc0 Hv2 Hv4.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp (Hwc & Hwp & Hwe & Hroom) Hos Hl' Hys HK".
  iDestruct (wroom_ptrs with "Hroom") as "[%Hp Hroom]". destruct Hp as (Hwpc & Hwec & Hwpa & Hwea & Hend & Hdif).
  iDestruct (wroom_cap with "Hroom") as (reg (Hb1 & Hb2 & Hcap)) "[Hbl Hroom]".
  step.
  sym_frun "Hl Hwe Hwp Hbl" [TAtom "L20"].
  - (* L73: the room. *)
    assert (Hlt : ptr_addr wp < ptr_addr we).
    { cbn [cond_bit] in Hsym_yes.
      destruct (Z.ltb_spec (ptr_addr wp) (ptr_addr we)); [assumption|].
      cbn in Hsym_yes. contradiction. }
    step.
    iDestruct ("Hroom" with "Hbl") as "Hroom".
    iApply (wp_xs_L20 Hmove Hmove_fn Hmove_sym Hfw Hfwq eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys 0 (ptr_addr we - ptr_addr wp) with "Hvt Hl Hvtp [$Hwc $Hwp $Hwe $Hroom] Hos Hl' Hys HK");
      try close_side.
    all: unfold n in *; try lia. all: lookups; try reflexivity. all: do 2 f_equal; unwrap2; lia.
  - (* No room: L20 with none. *)
    step. iDestruct ("Hroom" with "Hbl") as "Hroom".
    iApply (wp_xs_L20 Hmove Hmove_fn Hmove_sym Hfw Hfwq eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys 0 0 with "Hvt Hl Hvtp [$Hwc $Hwp $Hwe $Hroom] Hos Hl' Hys HK"); try close_side.
    all: unfold n in *; try lia. all: lookups; reflexivity.
Qed.

(** The line-buffered path computes the space up to the buffer's end.
    When the input fits, it scans for the last newline to decide whether to flush. *)
Lemma wp_xs_L18 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 < b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 < n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v2") e = Some (WPtr (mkPtr (b' + so) c')) ->
  lookup (TAtom "v4") e = Some (WInt n) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ xs_post w0 registry ge eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Enter (TAtom "L18") (Some (TAtom "L25")))) : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Heb Hfb Hfal Hfend Hfreg Hc' Hb'0 Hb8' Hso Hyend Hyreg Hy Hn0 Hv0 Hc0 Hv2 Hv4.
  unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp ((Hrp & Hre & Hrb & Hwb & Hbb & Hbe) & Hwp & Hwe & Hroom) Hos Hl' Hys HK".
  iDestruct (wroom_ptrs with "Hroom") as "[%Hp Hroom]". destruct Hp as (Hwpc & Hwec & Hwpa & Hwea & Hend & Hdif).
  iDestruct (wroom_cap with "Hroom") as (reg (Hb1 & Hb2 & Hcap)) "[Hbl Hroom]".
  step. step. check "Hl". iEval (rewrite -Hcap) in "Hbl". load "Hl" "Hbe" "Hbl". iEval (rewrite Hcap) in "Hbl".
  step. iEval (rewrite -Hwpc) in "Hbl". load "Hl" "Hwp" "Hbl". iEval (rewrite Hwpc) in "Hbl". step. step. step. step.
  iDestruct ("Hroom" with "Hbl") as "Hroom".
  set (cnt0 := ptr_addr (nb_end nb) - ptr_addr wp).
  destruct (Z_lt_le_dec cnt0 n) as [Hlt | Hge].
  - (* Less room than bytes: L20 with it. *)
    branch_as true. step.
    iApply (wp_xs_L20 Hmove Hmove_fn Hmove_sym Hfw Hfwq eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys 0 cnt0 with "Hvt Hl Hvtp [$Hrp $Hre $Hrb $Hwb $Hbb $Hbe $Hwp $Hwe $Hroom] Hos Hl' Hys HK");
      try close_side.
    all: unfold n, cnt0 in *; try lia. all: lookups; try reflexivity. all: do 2 f_equal; unwrap2; lia.
  - (* L40: the scan back from s + n. *)
    branch_as false. step. step. step. step.
    assert (Hcr : 0 <= cnt0 < 2 ^ 63) by (unfold cnt0; lia).
    iApply (wp_xs_scan dq b' reg' so c' ys cnt0 Hc' Hso Hyend Hyreg Hy Hcr $! _ (Z.of_nat (length ys))
              with "[%] Hl' Hys").
    { unfold n in *. split_and!; [lookups; reflexivity | | | lia | lia].
      - lookups. do 3 f_equal. cbn [ptr_addr]. unwrap2. lia.
      - lookups. do 2 f_equal. unwrap2. reflexivity. }
    iIntros (e' cnt mf (Hsame & Hp10 & Hp6 & Hc)) "Hl' Hys".
    iApply (wp_xs_L20 Hmove Hmove_fn Hmove_sym Hfw Hfwq eb X fb freg vb vreg nb wp we
              dq b' reg' so c' ys mf cnt with "Hvt Hl Hvtp [$Hrp $Hre $Hrb $Hwb $Hbb $Hbe $Hwp $Hwe $Hroom] Hos Hl' Hys HK");
      try assumption.
    all: unfold n, cnt0 in *; try lia.
    all: try (destruct Hc as [[-> ->] | [-> ?]]; lia).
    all: rewrite Hsame; [|reflexivity]; lookups; reflexivity.
Qed.

End rules.
