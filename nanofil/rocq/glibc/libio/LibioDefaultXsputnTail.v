(** The end of each round of `c: _IO_default_xsputn`'s loop
    (LibioGenCode.v), from block `c: L22`, once the room in the buffer
    is filled:

    ```
    if (more == 0 || _IO_OVERFLOW (f, (unsigned char) *s++) == EOF)
      break;
    more--;
    ```

    and the return of `c: n - more` after the loop (`c: L19`). The
    overflow is the jump table's, `c: _IO_new_file_overflow`, through
    `c: _IO_file_jumps`' overflow slot, as [overflow_spec] states it
    over the stream's [wbuf] and its rest os. The next round, block
    `c: L16`, is the loop's head, a premise here ([dx_loop]), which
    LibioDefaultXsputn.v proves by Löb induction. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioDoWriteCode LibioDefaultXsputnCopy LibioDefaultXsputnBuf
  LibioDefaultXsputnBytes.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L16` of `c: _IO_default_xsputn`, the loop's head. *)
Definition dx_L16 : block := Eval vm_compute in
  match find_block (TAtom "L16") (fn_blocks glibc__IO_default_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L16") [] [] JRetVoid end.

(** Block `c: L22`, after its phis. *)
Definition dx_L22 : block := Eval vm_compute in
  match find_block (TAtom "L22") (fn_blocks glibc__IO_default_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L22") [] [] JRetVoid end.

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDefaultXsputnTailOn (R : Runtime) (LG0 : LogicSig R).
Module BY := LibioDefaultXsputnBytesOn R LG0.
Import BY BY.BF BY.BF.CP BY.BF.CP.CS BY.BF.CP.SW BY.BF.CP.SW.FI.ML BY.BF.CP.SW.FI.LG BY.BF.CP.SW.FI.L
  BY.BF.CP.SW.OW BY.BF.CP.SW.FI BY.BF.CP.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance dx_tail_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** What `c: _IO_default_xsputn(f, s, n)` leaves: the count k it
    wrote, at most n, the stream with any buffer and its rest os, and
    the source back. *)
Definition dx_post (os : Z -> option (Z * Z) -> iProp Σ) (fb : Z) (freg : region) (vb n : Z) (dq : dfrac)
    (b' : Z) (reg' : region) (so : Z) (ys : list Z) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ k nb' wp' we', ⌜0 <= k <= n⌝ -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
    wbuf fb nb' wp' we' -∗ os fb nb' -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗ Φ (Ret (WInt k)).

(** The loop's head with t of the n bytes ys from offset so of b' left
    to write, s past the others: the triple [wp_dx_loop] proves. *)
Definition dx_loop (os : Z -> option (Z * Z) -> iProp Σ) (fb : Z) (freg : region) (vb : Z) (vreg : region)
    (dq : dfrac) (b' : Z) (reg' : region) (so : Z) (c' : cap) (ys : list Z) (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  let n := Z.of_nat (length ys) in
  ∀ e t nb wp we, ⌜lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
      lookup (TAtom "v4") e = Some (WInt n) /\ lookup (TAtom "pr.7") e = Some (WInt t) /\
      lookup (TAtom "pr.2") e = Some (WPtr (mkPtr (b' + (so + (n - t))) c')) /\ 0 <= t <= n⌝ -∗
    live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ wbuf fb nb wp we -∗ os fb nb -∗
    liveq dq b' reg' -∗ bytesq dq b' so ys -∗ ▷ dx_post os fb freg vb n dq b' reg' so ys Φ -∗
    WP (ERun (mkFrame glibc__IO_default_xsputn e [] None (Exec (TAtom "L16") (b_insts dx_L16) (b_jump dx_L16)))
          : sexpr) {{ Φ }}.

(** Block `c: L22` on, t bytes left and s at the next: return n - t
    when none are left; else hand the next byte to the jump table's
    overflow and return n - t if it fails, or run the loop again on
    the t - 1 left. *)
Lemma wp_dx_L22 os fb freg vb vreg nb wp we dq b' reg' so c' ys t e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge os -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  c' = Obj b' \/ c' = Ro b' -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= t <= n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb))) ->
  lookup (TAtom "v4") e = Some (WInt n) -> lookup (TAtom "pr.8") e = Some (WInt t) ->
  lookup (TAtom "pr.3") e = Some (WPtr (mkPtr (b' + (so + (n - t))) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ os fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ dx_loop os fb freg vb vreg dq b' reg' so c' ys Φ -∗
  ▷ dx_post os fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_default_xsputn e [] None (Exec (TAtom "L22") (b_insts dx_L22) (b_jump dx_L22)))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Hfb Hfal Hfend Hfreg Hc' Hso Hyend Hyreg Hy Ht Hv0 Hc0 Hv4 Hp8 Hp3. unfold file_size in Hfend.
  iIntros "#Hvt Hl Hvtp Hwb Hos Hl' Hys IH HK".
  iApply (wp_live_fit w0 registry ge with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  cbn [dx_L22 b_insts b_jump]. st.
  destruct (Z.eq_dec t 0) as [-> | Ht0].
  { (* No byte left: L100, then L19 returns n. *)
    fbrv false. fs. fbr. fs. fs.
    iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' Hys"). unwrap2. lia. }
  fbrv true.
  (* L99: the jump table, checked against `c: __io_vtables`. *)
  iPoseProof (vtables_slot ge vb vreg slot_overflow "_IO_new_file_overflow" with "Hvt") as "#Hsw"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_new_file_overflow")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hfo). done. }
  iPoseProof "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & _)".
  unfold io_vtables_size in Hvend.
  fs. fs. norm. fchk "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_file in *; lia |].
  iNext. iIntros "Hl Hvtp #Hvl'". fs. fs. fs. fs. fs. fbrv true.
  (* iw_1.join: the overflow slot, the next byte, and the call. *)
  fs. fs. norm.
  iApply (wp_check_read_dq with "Hvl'"); [reflexivity | vx | right; reflexivity | ar | ar | ar |].
  iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsw Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hfo) |].
  iNext. iIntros "_ _ _". fs.
  set (j := Z.to_nat (n - t)).
  destruct (lookup_lt_is_Some_2 ys j ltac:(lia)) as [y Hyj].
  iDestruct (bytesq_at _ _ _ _ j y Hyj with "Hys") as "[Hy1 Hyb]".
  iApply (wp_check_read_dq with "Hl'");
    [reflexivity | vx | exact Hc' | cbn; unfold raw_address; unwrap2; lia | cbn; unfold raw_address; unwrap2; lia
    | apply Z.mod_1_r |].
  iNext. iIntros "Hl'".
  iApply (wp_raw_load_sub_bytes_dq with "Hl' Hy1");
    [reflexivity | vx | reflexivity | reflexivity | exact Hc' | cbn; unfold raw_address; unwrap2; lia |].
  iNext. iIntros "Hl' Hy1". iDestruct ("Hyb" with "Hy1") as "Hys". fs.
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hfo) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hfo) | apply (ge_fn_check _ _ _ Hfo) | vx |
    apply (ge_fn_find _ _ _ Hfo) | reflexivity | reflexivity |].
  iNext.
  match goal with |- context [WInt ?X :: nil] => set (ch := X) end.
  assert (Hch : 0 <= ch < 256).
  { unfold ch. match goal with |- context [?Y mod 256] =>
      pose proof (Z.mod_pos_bound Y 256 ltac:(lia)); set (Z0 := Y mod 256) in * end.
    rewrite (Z.mod_small Z0); [|lia]. rewrite (Z.mod_small Z0); [|lia]. lia. }
  iApply (Hov with "Hvt Hl Hvtp Hwb Hos"); [reflexivity | exact Hch | exact Hfb | exact Hfal | unfold file_size; lia | exact Hfreg |].
  iNext. iIntros (r nb' wp' we' Hr) "Hl Hvtp Hwb Hos". resume.
  assert (Hr32 : 0 <= r < 2 ^ 32) by lia. rewrite (Z.mod_small r); [|lia].
  st. fs. fs.
  destruct (Z.eq_dec r (2 ^ 32 - 1)) as [-> | Hne].
  - (* `c: EOF`: L19 returns n - t. *)
    fbrv false. fs. fs.
    iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' Hys"). unwrap2. lia.
  - (* The byte went: L96 runs the loop again on t - 1. *)
    assert (r = ch) by lia. fbrv true. fs. fs. fs. fs.
    iApply ("IH" with "[%] Hl Hvtp Hwb Hos Hl' Hys HK").
    unfold n in *. split_and!; try (lookups; reflexivity); try lia.
    all: lookups; first [do 3 f_equal; cbn [ptr_addr]; unwrap2; lia | do 2 f_equal; unwrap2; lia].
Qed.

End rules.
End LibioDefaultXsputnTailOn.
