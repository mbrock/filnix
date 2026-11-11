(** This file proves the terminal test of `c: _IO_file_doallocate` (LibioDoAllocBase.v
    describes the function). Block `c: L5` sees a character device in
    the stat buffer's `c: st_mode` and asks `c: __gnu_dev_major` of its
    `c: st_rdev`; block `c: L48` asks `c: __isatty_nostatus` of the
    descriptor. A terminal goes on to `c: L33`, which makes the stream
    line-buffered; any other stream goes to `c: L28`. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode LibioReadCode FileInv LibioLogic SysWrappers
  LibioSetb LibioDoAllocBase.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDoAllocModeOn (R : Runtime) (LG0 : LogicSig R).
Module DB := LibioDoAllocBaseOn R LG0.
Import DB DB.SW DB.SW.FI.ML DB.SW.FI.LG DB.SW.FI.L DB.SW.OW DB.SW.FI DB.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
(** The registry holds the OS contracts, and the genv's externals
    are the system calls. *)
Context (Hreg : holds_os registry) (Hext : sys_external ge).
(** The genv defines `c: __gnu_dev_major`. *)
Context (Hmaj : find_fn ge (TAtom "__gnu_dev_major") = Some (Defined glibc___gnu_dev_major)).
(** The genv defines `c: __isatty_nostatus`. *)
Context (Hisatty : find_fn ge (TAtom "__isatty_nostatus") = Some (Defined glibc___isatty_nostatus)).

Local Instance doalloc_mode_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The allocator's state, which `c: malloc` takes and gives back. *)
Context (Mres : iProp Σ).
(** Block `c: L28`, as LibioDoAllocTail.v proves it ([wp_doalloc_L28]). *)
Context (HL28 : forall fb freg fl oe sb sreg bs3 from e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < sb -> sb mod 16 = 0 -> sb + 144 <= r_end sreg -> r_end sreg <= 2 ^ 48 -> length bs3 = 8%nat ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr sb (Obj sb))) ->
  lookup (TAtom "chk4") e = Some (WPtr (mkPtr (sb + 24) (Obj sb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗
  live sb sreg -∗ bytes sb 56 bs3 -∗
  ▷ (∀ bb sz, ⌜0 < sz <= 8192 /\ 0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     live fb freg -∗ int_cell fb off_flags (setb_flags fl 1) -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ Mres -∗ Φ (Ret (WInt 1))) -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate e [] None (Enter (TAtom "L28") (Some from))) : sexpr) {{ Φ }}).

(** Block `c: L33`, as LibioDoAllocTail.v proves it ([wp_doalloc_L33]). *)
Context (HL33 : forall fb freg fl oe sb sreg bs3 from e Φ,
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < sb -> sb mod 16 = 0 -> sb + 144 <= r_end sreg -> r_end sreg <= 2 ^ 48 -> length bs3 = 8%nat ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_fileno) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr sb (Obj sb))) ->
  lookup (TAtom "chk4") e = Some (WPtr (mkPtr (sb + 24) (Obj sb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗
  live sb sreg -∗ bytes sb 56 bs3 -∗
  ▷ (∀ bb sz, ⌜0 < sz <= 8192 /\ 0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     live fb freg -∗ int_cell fb off_flags (setb_flags (Z.lor fl io_line_buf) 1) -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ Mres -∗ Φ (Ret (WInt 1))) -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate e [] None (Enter (TAtom "L33") (Some from))) : sexpr) {{ Φ }}).

(** Block `c: L48`, which asks `c: __isatty_nostatus` of the descriptor
    and makes a terminal line-buffered. *)
Lemma wp_doalloc_L48 fb freg fl fd eb oe sb sreg bs3 from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < sb -> sb mod 16 = 0 -> sb + 144 <= r_end sreg -> r_end sreg <= 2 ^ 48 -> length bs3 = 8%nat ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_fileno) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr sb (Obj sb))) ->
  lookup (TAtom "chk4") e = Some (WPtr (mkPtr (sb + 24) (Obj sb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗ live sb sreg -∗ bytes sb 56 bs3 -∗
  ▷ doalloc_k Mres fb freg fl fd eb Φ -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate e [] None (Enter (TAtom "L48") (Some from))) : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hsb Hsal Hsend Hsreg Hl3 He Hfd Hv0 Hc0 Hv4 Hc4.
  iIntros "Hl Hfl [%Hfdr Hfdb] Herr Hb Hbe HM Hsl Hb3 HK". unfold file_size in Hend.
  st. st. norm. chk "Hl". load_int "Hl Hfdb".
  iApply wp_call_bind; [vx | exact Hisatty | reflexivity |]. iNext.
  iApply (wp_glibc___isatty_nostatus w0 registry ge Hreg Hext with "Herr");
    [reflexivity | apply Z.mod_pos_bound; lia | exact He | rewrite Z.mod_small; [exact Hfd | lia] |].
  iNext. iIntros (r Hr) "Herr". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  cbn [fr_fn fr_env fr_locals fr_doomed fr_at]. st. st.
  st. destruct Hr as [-> | ->]; br.
  - iApply (HL28 with "Hl Hfl Hb Hbe HM Hsl Hb3"); try side.
    iNext. iIntros (bb sz Hbb) "Hl Hfl Hb Hbe Hbo HM".
    iApply ("HK" $! fl bb sz with "[%] Hl Hfl [$Hfdb //] Hb Hbe Hbo Herr HM"). split; [left; reflexivity | lia].
  - iApply (HL33 with "Hl Hfl Hb Hbe HM Hsl Hb3"); try side.
    iNext. iIntros (bb sz Hbb) "Hl Hfl Hb Hbe Hbo HM".
    iApply ("HK" $! (Z.lor fl io_line_buf) bb sz with "[%] Hl Hfl [$Hfdb //] Hb Hbe Hbo Herr HM").
    split; [right; reflexivity | lia].
Qed.

(** Block `c: L5`, the test of `c: st_mode` for a character device and
    of its major number for a terminal. *)
Lemma wp_doalloc_L5 fb freg fl fd eb oe sb sreg bs1 bs2 bs3 e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < sb -> sb mod 16 = 0 -> sb + 144 <= r_end sreg -> r_end sreg <= 2 ^ 48 ->
  length bs1 = 4%nat -> length bs2 = 8%nat -> length bs3 = 8%nat ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_fileno) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WPtr (mkPtr sb (Obj sb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ Mres -∗
  live sb sreg -∗ bytes sb 24 bs1 -∗ bytes sb 40 bs2 -∗ bytes sb 56 bs3 -∗
  ▷ doalloc_k Mres fb freg fl fd eb Φ -∗
  WP (ERun (mkFrame glibc__IO_file_doallocate e [] None (Enter (TAtom "L5") (Some (TAtom "L13")))) : sexpr)
    {{ Φ }}.
Proof.
  intros Hfb Hal Hend Hfreg Hsb Hsal Hsend Hsreg Hl1 Hl2 Hl3 He Hfd Hv0 Hc0 Hv4.
  iIntros "Hl Hfl Hfd Herr Hb Hbe HM Hsl Hb1 Hb2 Hb3 HK".
  st. st. norm. chk "Hsl".
  iApply (wp_raw_load_sub_bytes_dq with "Hsl Hb1");
    [reflexivity | vx | rewrite Hl1; reflexivity | reflexivity | left; reflexivity | ar |].
  iNext. iIntros "Hsl Hb1". st. st. brk Ec.
  - st. st. norm. chk "Hsl".
    iApply (wp_raw_load_bytes8 w0 registry ge with "Hsl Hb2"); [reflexivity | vx | exact Hl2 | reflexivity | ar |].
    iNext. iIntros "Hsl Hb2".
    iApply wp_call_bind; [vx | exact Hmaj | reflexivity |]. iNext.
    iApply (wp_glibc___gnu_dev_major w0 registry ge); [reflexivity | apply Z.mod_pos_bound; lia |].
    iNext. iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
    st. brk Ej.
    + st. st. st. st. brk Ek.
      * st. br. iApply (HL33 with "Hl Hfl Hb Hbe HM Hsl Hb3"); try side.
        iNext. iIntros (bb sz Hbb) "Hl Hfl Hb Hbe Hbo HM".
        iApply ("HK" $! (Z.lor fl io_line_buf) bb sz with "[%] Hl Hfl Hfd Hb Hbe Hbo Herr HM").
        split; [right; reflexivity | lia].
      * iApply (wp_doalloc_L48 with "Hl Hfl Hfd Herr Hb Hbe HM Hsl Hb3 HK"); try side.
    + st. br. iApply (wp_doalloc_L48 with "Hl Hfl Hfd Herr Hb Hbe HM Hsl Hb3 HK"); try side.
  - iApply (HL28 with "Hl Hfl Hb Hbe HM Hsl Hb3"); try side.
    iNext. iIntros (bb sz Hbb) "Hl Hfl Hb Hbe Hbo HM".
    iApply ("HK" $! fl bb sz with "[%] Hl Hfl Hfd Hb Hbe Hbo Herr HM"). split; [left; reflexivity | lia].
Qed.

End rules.
End LibioDoAllocModeOn.
