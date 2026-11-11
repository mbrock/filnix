(** The byte loop of `c: _IO_default_xsputn` (LibioGenCode.v), which
    copies a count of at most 20 bytes one at a time:

    ```
    char *p = f->_IO_write_ptr;
    for (i = count; --i >= 0; )
      *p++ = *s++;
    f->_IO_write_ptr = p;
    ```

    Block `c: L76` is the loop's head, its phis `c: pr.11` (the count
    left), `c: pr.10` (p) and `c: pr.6` (s); `c: L77` copies one byte
    and `c: L79` stores p back. [wp_dx_bytes] runs the loop, by Löb
    induction over the head, from any count left, and hands the caller
    the environment at `c: L51` (the names the loop binds aside, it is
    the one at the head), the buffer with new contents and the write
    pointer past the count. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioDoWriteCode LibioDefaultXsputnCopy LibioDefaultXsputnBuf.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L76` of `c: _IO_default_xsputn`, the byte loop's head. *)
Definition dx_L76 : block := Eval vm_compute in
  match find_block (TAtom "L76") (fn_blocks glibc__IO_default_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L76") [] [] JRetVoid end.

(** The names the byte loop binds. *)
Definition dx_loop_names : list name :=
  map TAtom ["pr.11"; "pr.10"; "pr.6"; "v81"; "v82"; "v84"; "v86"; "chk7"; "v87"; "chk8"; "v89"; "chk9"].

(** The rules over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioDefaultXsputnBytesOn (R : Runtime) (LG0 : LogicSig R).
Module BF := LibioBufOn R LG0.
Import BF BF.CP BF.CP.CS BF.CP.SW BF.CP.SW.FI.ML BF.CP.SW.FI.LG BF.CP.SW.FI.L BF.CP.SW.OW BF.CP.SW.FI
  BF.CP.SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance dx_bytes_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The byte loop at its head, i of cnt bytes left: p at offset
    k0 + cnt - i of the buffer b, s at offset j0 + cnt - i of the bytes
    ys from offset so of the source b'. It copies the i bytes, stores
    p, past the cnt bytes, as the write pointer, and enters `c: L51`. *)
Lemma wp_dx_bytes fb freg b reg sz k0 cnt dq b' reg' so c' ys j0 wp0 :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < b -> b + sz <= r_end reg -> r_end reg <= 2 ^ 63 -> 0 <= k0 -> k0 + cnt <= sz ->
  c' = Obj b' \/ c' = Ro b' -> 0 <= so -> 0 <= j0 -> j0 + cnt <= Z.of_nat (length ys) ->
  b' + so + Z.of_nat (length ys) <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  ⊢ ∀ e i xs Φ, ⌜lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) /\
      lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_write_ptr) (Obj fb))) /\
      lookup (TAtom "pr.11") e = Some (WInt i) /\
      lookup (TAtom "pr.10") e = Some (WPtr (mkPtr (b + (k0 + (cnt - i))) (Obj b))) /\
      lookup (TAtom "pr.6") e = Some (WPtr (mkPtr (b' + (so + (j0 + (cnt - i)))) c')) /\
      0 <= i <= cnt /\ length xs = Z.to_nat sz /\ Forall (fun x => 0 <= x < 256) xs⌝ -∗
    live fb freg -∗ pcell fb off_write_ptr wp0 -∗ live b reg -∗ bytes b 0 xs -∗
    liveq dq b' reg' -∗ bytesq dq b' so ys -∗
    ▷ (∀ e' xs', ⌜same_out dx_loop_names e e' /\
         lookup (TAtom "pr.6") e' = Some (WPtr (mkPtr (b' + (so + (j0 + cnt))) c')) /\
         length xs' = Z.to_nat sz /\ Forall (fun x => 0 <= x < 256) xs'⌝ -∗
       live fb freg -∗ pcell fb off_write_ptr (mkPtr (b + (k0 + cnt)) (Obj b)) -∗ live b reg -∗
       bytes b 0 xs' -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
       WP (ERun (mkFrame glibc__IO_default_xsputn e' [] None (Enter (TAtom "L51") (Some (TAtom "L79"))))
             : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame glibc__IO_default_xsputn e [] None (Exec (TAtom "L76") (b_insts dx_L76) (b_jump dx_L76)))
          : sexpr) {{ Φ }}.
Proof.
  intros Hfb Hfal Hfend Hfreg Hb Hbend Hbreg Hk0 Hkc Hc' Hso Hj0 Hjc Hyend Hyreg. unfold file_size in Hfend.
  iLöb as "IH". iIntros (e i xs Φ (Hv0 & Hc0 & Hi & Hp10 & Hp6 & Hir & Hlx & Hx)) "Hl Hwp Hbl Hxs Hl' Hy HK".
  iApply (wp_live_fit w0 registry ge with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  cbn [dx_L76 b_insts b_jump]. st. fs.
  destruct (Z.eq_dec i 0) as [-> | Hi0].
  - (* L79: store p, past all cnt bytes, as the write pointer. *)
    fbrv true. fs. fs. norm. fchk "Hl". fstp "Hl" "Hwp". fs.
    iApply ("HK" $! _ xs with "[%] Hl [Hwp] Hbl Hxs Hl' Hy").
    + split; [same_tac|]. split; [lookups; rewrite Z.sub_0_r; reflexivity|]. split; assumption.
    + rewrite Z.sub_0_r. iExact "Hwp".
  - (* L77: copy one byte. *)
    fbrv false. fs. fs. fs.
    set (j := Z.to_nat (j0 + (cnt - i))).
    destruct (lookup_lt_is_Some_2 ys j ltac:(lia)) as [y Hyj].
    iDestruct (bytesq_at _ _ _ _ j y Hyj with "Hy") as "[Hy1 Hyb]".
    iApply (wp_check_read_dq with "Hl'");
      [reflexivity | vx | exact Hc' | cbn; unfold raw_address; unwrap2; lia | cbn; unfold raw_address; unwrap2; lia
      | apply Z.mod_1_r |].
    iNext. iIntros "Hl'".
    iApply (wp_raw_load_sub_bytes_dq with "Hl' Hy1");
      [reflexivity | vx | reflexivity | reflexivity | exact Hc' | cbn; unfold raw_address; unwrap2; lia |].
    iNext. iIntros "Hl' Hy1". iDestruct ("Hyb" with "Hy1") as "Hy".
    fchk "Hbl".
    set (k := Z.to_nat (k0 + (cnt - i))).
    destruct (lookup_lt_is_Some_2 xs k ltac:(lia)) as [x Hxk].
    iEval (rewrite (bytes_at b xs k x Hxk)) in "Hxs". iDestruct "Hxs" as "(Hx1 & Hxb & Hx2)".
    iApply (wp_raw_store_byte with "Hbl Hxb");
      [vx | vx | reflexivity | cbn; unfold raw_address; unwrap2; lia | wi_store |].
    iNext. iIntros "Hbl Hxb".
    iDestruct (bytes_put with "[$Hx1 $Hxb $Hx2]") as "Hxs"; [lia|].
    fs. fs.
    iApply ("IH" $! _ (i - 1) with "[%] Hl Hwp Hbl Hxs Hl' Hy [HK]").
    + split_and!; try (lookups; reflexivity).
      * lookups. do 3 f_equal. unfold raw_address. unwrap2. reflexivity.
      * lookups. do 3 f_equal. cbn [ptr_addr]. unwrap2. lia.
      * lookups. do 3 f_equal. cbn [ptr_addr]. unwrap2. lia.
      * lia.
      * lia.
      * rewrite length_insert. exact Hlx.
      * apply Forall_insert; [exact Hx | apply Z.mod_pos_bound; lia].
    + iNext. iIntros (e' xs' (Hsame & Hp6' & Hlx' & Hx')) "Hl Hwp Hbl Hxs Hl' Hy".
      iApply ("HK" $! e' xs' with "[%] Hl Hwp Hbl Hxs Hl' Hy"). split; [|split; [exact Hp6' | split; assumption]].
      eapply same_out_trans; [|exact Hsame]. same_tac.
Qed.

End rules.
End LibioDefaultXsputnBytesOn.
