From Glibc Require Import GlibcProgram.
(** The state, the premises and the last blocks of
    `c: _IO_new_file_xsputn(f, s, n)` (LibioXsputnCode.v), the jump
    table's string output of a narrow stream:

    ```
    if (n <= 0) return 0;
    if ((f->_flags & _IO_LINE_BUF) && (f->_flags & _IO_CURRENTLY_PUTTING))
      { count = f->_IO_buf_end - f->_IO_write_ptr;
        if (count >= n) scan s[0..n) backwards for '\n' ... }
    else if (f->_IO_write_end > f->_IO_write_ptr)
      count = f->_IO_write_end - f->_IO_write_ptr;
    copy min (count, n) bytes into the buffer; to_do = n - that;
    if (to_do + must_flush > 0)
      { if (_IO_OVERFLOW (f, EOF) == EOF) return to_do == 0 ? EOF : n - to_do;
        block = f->_IO_buf_end - f->_IO_buf_base;
        do_write = to_do - (block >= 128 ? to_do % block : 0);
        if (do_write) { count = new_do_write (f, s, do_write); to_do -= count;
                        if (count < do_write) return n - to_do; }
        if (to_do) to_do -= _IO_default_xsputn (f, s + do_write, to_do);
      }
    return n - to_do;
    ```

    The stream is LibioDefaultXsputnBuf.v's: its life, its jump table
    pointer and its write side [wbuf], and a rest that the overflow
    reads, here [xos]: the fields the function and `c: new_do_write`
    read or write ([xfields]) and any other predicate X of the stream
    and its buffer. The fields keep what LibioDoWriteCall.v asks of
    `c: new_do_write`: no `c: _IO_IS_APPENDING`, `c: _cur_column` 0 and
    a narrow mode, 0 or -1, which `c: puts` sets.

    The source is n bytes ys of an object b' at any share dq, read-only
    like a string literal, so the jump table's write must take a share:
    [fwq_spec] is LibioWrite.v's [wp_glibc__IO_new_file_write] over
    [liveq] and [bytesq] instead of [live] and [bytes], a premise here.

    | Name | Part |
    |---|---|
    | [xfields], [xos] | the stream's fields beside [wbuf] |
    | [fwq_spec] | the jump table's write of bytes at a share |
    | [xs_post] | what the function leaves |
    | [wp_xs_scan] | the newline scan, blocks `c: L50` to `c: L59` |
    | [wp_xs_L178] | `c: _IO_default_xsputn` of the rest and the return | *)

From Glibc Require Import GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine Symbolic
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry SysCode MemFwdCode FileInv LibioLogic SysWrappers
  LibioCloseSteps LibioGenCode LibioReadCode LibioDoWriteCode LibioXsputnCode LibioDefaultXsputnCopy LibioDefaultXsputnBuf
  LibioDefaultXsputnTail LibioDefaultXsputn.
From Glibc Require FileInv LibioCloseSteps LibioDefaultXsputn LibioDefaultXsputnBuf LibioDefaultXsputnBytes LibioDefaultXsputnCopy LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** Block `c: L50` of `c: _IO_new_file_xsputn`, the scan's head, after its phi. *)
Definition xs_L50 : block := Eval vm_compute in
  match find_block (TAtom "L50") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L50") [] [] JRetVoid end.

(** Block `c: L20`, after its phis: the count and the flush flag. *)
Definition xs_L20 : block := Eval vm_compute in
  match find_block (TAtom "L20") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L20") [] [] JRetVoid end.

(** Block `c: L178`, after its phi: the bytes left. *)
Definition xs_L178 : block := Eval vm_compute in
  match find_block (TAtom "L178") (fn_blocks glibc__IO_new_file_xsputn) with
  | Some b => b | None => mkBlock (TAtom "L178") [] [] JRetVoid end.

(** The names the scan binds, with the two phis of `c: L20`. *)
Definition xs_scan_names : list name :=
  map TAtom ["pr.14"; "v56"; "v57"; "v58"; "v63"; "chk4"; "v64"; "v65"; "v68"; "v70"; "v71"; "pr.10"; "pr.6"].

(** A buffered output stream keeps the standard file flags except for
    the error, line-buffering and writing bits. It starts writing when
    it obtains a buffer. Naming this relation lets callers recover the
    overflow premises after the flags have been existentially hidden. *)
Definition xs_flags (nb : option (Z * Z)) (fl : Z) : Prop :=
  Z.land fl (Z.lnot 2592) = 4222427268 /\
  match nb with None => Z.land fl 2048 = 0 | Some _ => Z.land fl 2048 <> 0 end.

(** Setting the error bit preserves the buffer's writing state and
    every fixed flag. A failed write therefore keeps the output invariant. *)
Lemma xs_flags_error nb fl : xs_flags nb fl -> xs_flags nb (Z.lor fl io_err_seen).
Proof.
  intros [Hfixed Hput]. unfold xs_flags. rewrite !Z.land_lor_distr_l.
  change (Z.land io_err_seen (Z.lnot 2592)) with 0.
  change (Z.land io_err_seen 2048) with 0.
  rewrite !Z.lor_0_r. split; assumption.
Qed.

(** A fixed flag mask can be read from the output invariant. The
    premise excludes the three bits that output may change. *)
Lemma xs_flags_mask nb fl mask :
  Z.land (Z.lnot 2592) mask = mask -> xs_flags nb fl ->
  Z.land fl mask = Z.land 4222427268 mask.
Proof.
  intros Hmask [Hfixed _]. apply (f_equal (fun f => Z.land f mask)) in Hfixed.
  rewrite -Z.land_assoc Hmask in Hfixed. exact Hfixed.
Qed.


Import LibioDefaultXsputn LibioDefaultXsputnRoom LibioDefaultXsputnTail LibioDefaultXsputnBytes LibioDefaultXsputnBuf LibioDefaultXsputnCopy LibioCloseSteps SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

Section defs.
Context `{!gen_heapGS piece pval Σ}.

(** String output needs an open descriptor and flags that allow
    writing and later closing the stream. These fields retain those
    facts alongside the output count, offset and thread error cell.
    The column stays zero, and the mode allows only byte output. *)
Definition xfields_body (w0 : os_world) (eb fb : Z) (nb : option (Z * Z)) (fl f2 fd tw off m : Z) : iProp Σ :=
  ⌜Z.land fl io_is_appending = 0 /\ Z.land f2 2 = 0 /\ In fd (ow_fds w0) /\
                        (m = 0 \/ m = 2 ^ 32 - 1) /\ xs_flags nb fl /\
                        0 <= fd < 2 ^ 31 /\ Z.land f2 160 = 0⌝ ∗
    int_cell fb off_flags fl ∗ int_cell fb off_flags2 f2 ∗ int_cell fb off_fileno fd ∗
    icell fb off_total_written tw ∗ icell fb off_offset off ∗ bytes fb off_column [0; 0] ∗
    int_cell fb off_mode m ∗ errno_any eb.

(** The string-output invariant hides the field values. Callers that
    must orient a stream can instead keep its mode explicit in the
    same field ownership predicate. *)
Definition xfields (w0 : os_world) (eb fb : Z) (nb : option (Z * Z)) : iProp Σ :=
  ∃ fl f2 fd tw off m, xfields_body w0 eb fb nb fl f2 fd tw off m.

(** Overflow keeps the output fields together with the caller's
    remaining resources for this stream and buffer. *)
Definition xos (w0 : os_world) (eb : Z) (X : Z -> option (Z * Z) -> iProp Σ) (fb : Z) (nb : option (Z * Z))
    : iProp Σ := xfields w0 eb fb nb ∗ X fb nb.

(** A run of bytes at a share is its first j bytes and the rest. *)
Lemma bytesq_split dq b o ys (j : nat) : (j <= length ys)%nat ->
  bytesq dq b o ys ⊣⊢ bytesq dq b o (take j ys) ∗ bytesq dq b (o + Z.of_nat j) (drop j ys).
Proof.
  intros H. rewrite -{1}(take_drop j ys) /bytesq byte_ps_app ptsq_app length_take_le; [done | lia].
Qed.

End defs.

Import ProgramAbbreviations.
Section rules_values.
Context {hlc : has_lc}
  {Σ : gFunctors}
  {invGS_gen0 : invGS_gen hlc Σ}
  {gen_heapGS0 : gen_heapGS piece pval Σ}
  (w0 : os_world)
  (registry : name -> option (contract os_world))
  (ge : genv).
Existing Instance invGS_gen0.
Existing Instance gen_heapGS0.
Local Instance xs_base_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).
Definition fwq_spec : Prop :=
  forall fr fb freg fl f2 fd tw off dq b reg o c xs eb Φ,
  call_frame glibc__IO_new_file_write
    [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + o) c); WInt (Z.of_nat (length xs))] = Some fr ->
  (c = Obj b \/ c = Ro b) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (Z.land f2 2 = 0 \/
    Z.land f2 2 = 2 /\ find_fn ge (TAtom "__GI___write_nocancel") = Some (Defined glibc___write_nocancel)) ->
  0 <= f2 < 2 ^ 32 -> In fd (ow_fds w0) -> 0 <= fl < 2 ^ 32 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  0 < b -> 0 <= o -> b + o + Z.of_nat (length xs) <= r_end reg -> r_end reg <= 2 ^ 63 ->
  Forall (fun x => 0 <= x < 256) xs ->
  ⊢ live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
    icell fb off_total_written tw -∗ icell fb off_offset off -∗ liveq dq b reg -∗ bytesq dq b o xs -∗
    errno_any eb -∗
    ▷ (∀ r fl' tw' off', ⌜fw_post (Z.of_nat (length xs)) fl r fl' /\ 0 <= fl' < 2 ^ 32⌝ -∗
       live fb freg -∗ int_cell fb off_flags fl' -∗ int_cell fb off_flags2 f2 -∗ int_cell fb off_fileno fd -∗
       icell fb off_total_written tw' -∗ icell fb off_offset off' -∗ liveq dq b reg -∗ bytesq dq b o xs -∗
       errno_any eb -∗ Φ (Ret (WInt r))) -∗
    WP (ERun fr : sexpr) {{ Φ }}.
Definition xs_post (eb : Z) (X : Z -> option (Z * Z) -> iProp Σ) (fb : Z) (freg : region) (vb n : Z)
    (dq : dfrac) (b' : Z) (reg' : region) (so : Z) (ys : list Z)
    (Φ : language.val (nanofil_lang registry ge) -> iProp Σ) : iProp Σ :=
  ∀ r nb' wp' we', ⌜(r = 2 ^ 64 - 1 \/ 0 <= r <= n) /\ (0 < n -> nb' <> None)⌝ -∗ live fb freg -∗
    pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗ wbuf fb nb' wp' we' -∗ xos w0 eb X fb nb' -∗
    liveq dq b' reg' -∗ bytesq dq b' so ys -∗ Φ (Ret (WInt r)).
Lemma sb_ne_nl z : 0 <= z < 256 -> z <> 10 ->
  ((sign_extension 256 128 (z + 0) mod 2 ^ 32) mod 2 ^ 32 =? 10 mod 2 ^ 32) = false.
Proof.
  intros Hz H10. unfold sign_extension. rewrite Z.add_0_r (Z.mod_small z 256); [|lia].
  apply Z.eqb_neq. destruct (128 <=? z); Z.div_mod_to_equations; lia.
Qed.
End rules_values.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
(** The registry holds `c: zmemmove`'s contract, and the genv's
    `c: __GI_memcpy`, `c: __GI_mempcpy` and
    `c: __GI__IO_default_xsputn` are glibc's. *)
Context (Hmove : registry (TAtom "zmemmove") = Some (void_only (memmove_contract os_world)))
  (Hmove_fn : find_fn ge (TAtom "zmemmove") = None)
  (Hmove_sym : lookup (TAtom "zmemmove") (ge_globals ge) = None)
  `{Hcpy : !Defines ge "__GI_memcpy" glibc_memcpy}
  `{Hpcpy : !Defines ge "__GI_mempcpy" glibc_mempcpy}
  `{Hdxf : !Defines ge "__GI__IO_default_xsputn" glibc__IO_default_xsputn}.


(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** The stream's write function borrows the source bytes instead of owning
    them exclusively. It returns that share and the exact cancellation flags
    even if the write fails. A set NOTCANCEL bit requires the captured
    noncanceling wrapper. The result still permits partial writes and failure. *)

(** String output returns either EOF or a count no greater than n.
    A nonempty input leaves an allocated buffer even when output
    fails. The stream's remaining resources and the source are returned
    to the caller. *)

(** A byte other than a newline, loaded signed and widened, is not
    the newline's code. *)

(** The newline scan, blocks `c: L50` to `c: L59`, at the head with p
    at offset i of the n bytes ys from offset so of b': it reads back
    from p for a `c: '\n'` and enters `c: L20` with count cnt0 and no
    flush when none is found, or with the count up to and including the
    last one and a flush. *)
Lemma wp_xs_scan dq b' reg' so c' ys cnt0 :
  let n := Z.of_nat (length ys) in
  c' = Obj b' \/ c' = Ro b' -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= cnt0 < 2 ^ 63 ->
  ⊢ ∀ e i Φ, ⌜lookup (TAtom "v2") e = Some (WPtr (mkPtr (b' + so) c')) /\
      lookup (TAtom "pr.14") e = Some (WPtr (mkPtr (b' + so + i) c')) /\
      lookup (TAtom "v39") e = Some (WInt cnt0) /\ 0 <= i <= n⌝ -∗
    liveq dq b' reg' -∗ bytesq dq b' so ys -∗
    (∀ e' cnt mf, ⌜same_out xs_scan_names e e' /\ lookup (TAtom "pr.10") e' = Some (WInt cnt) /\
         lookup (TAtom "pr.6") e' = Some (WInt mf) /\ ((mf = 0 /\ cnt = cnt0) \/ (mf = 1 /\ 1 <= cnt <= n))⌝ -∗
       liveq dq b' reg' -∗ bytesq dq b' so ys -∗
       WP (ERun (mkFrame glibc__IO_new_file_xsputn e' [] None (Exec (TAtom "L20") (b_insts xs_L20) (b_jump xs_L20)))
             : sexpr) {{ Φ }}) -∗
    WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Exec (TAtom "L50") (b_insts xs_L50) (b_jump xs_L50)))
          : sexpr) {{ Φ }}.
Proof.
  intros n Hc' Hso Hyend Hyreg Hy Hcr.
  iLöb as "IH". iIntros (e i Φ (Hv2 & Hp14 & Hv39 & Hi)) "Hl' Hys HK".
  iApply (wp_live_fit with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  cbn [xs_L50 b_insts b_jump]. step. step. step.
  destruct (Z.eq_dec i 0) as [-> | Hi0].
  - (* p is s: no newline; L20 from L50. *)
    branch_as true. step.
    iApply ("HK" $! _ cnt0 0 with "[%] Hl' Hys").
    split; [same_tac|]. split_and!; [lookups; unwrap2; reflexivity | lookups; reflexivity | left; split; reflexivity].
  - branch_as false. step. step.
    set (j := Z.to_nat (i - 1)).
    destruct (lookup_lt_is_Some_2 ys j ltac:(lia)) as [y Hyj].
    pose proof (Forall_lookup_1 _ _ _ _ Hy Hyj) as Hyr.
    iDestruct (bytesq_at _ _ _ _ j y Hyj with "Hys") as "[Hy1 Hyb]".
    iApply (wp_check_read_dq with "Hl'");
      [reflexivity | vx | exact Hc' | cbn; unfold raw_address; unwrap2; lia | cbn; unfold raw_address; unwrap2; lia
      | apply Z.mod_1_r |].
    iNext. iIntros "Hl'".
    iApply (wp_raw_load_sub_bytes_dq with "Hl' Hy1");
      [reflexivity | vx | reflexivity | reflexivity | exact Hc' | cbn; unfold raw_address; unwrap2; lia |].
    iNext. iIntros "Hl' Hy1". iDestruct ("Hyb" with "Hy1") as "Hys". step.
    destruct (Z.eq_dec y 10) as [-> | Hy10].
    + (* A newline at j: L59, the count j + 1, then L20. *)
      branch_as false. step. step. step. step. step. step.
      iApply ("HK" $! _ i 1 with "[%] Hl' Hys").
      split; [same_tac|]. split_and!; [|lookups; reflexivity|right; split; [reflexivity | lia]].
      lookups. do 2 f_equal. cbn [ptr_addr]. unfold raw_address. unwrap2. lia.
    + eapply step_wand; [eapply wp_branch; inst; vx |].
      rewrite (sb_ne_nl y Hyr Hy10). change ((if false then 1 else 0) mod 2 ^ 32 =? 0) with true.
      cbn [edge_label]. step.
      iApply ("IH" $! _ (i - 1) with "[%] Hl' Hys [HK]").
      * split_and!; [lookups; reflexivity | | lookups; reflexivity | lia | lia].
        lookups. do 3 f_equal. cbn [ptr_addr]. unfold raw_address. unwrap2. lia.
      * iIntros (e' cnt mf (Hsame & Hp10 & Hp6 & Hc)) "Hl' Hys".
        iApply ("HK" $! e' cnt mf with "[%] Hl' Hys"). split_and!; try assumption.
        eapply same_out_trans; [|exact Hsame]. same_tac.
Qed.

(** Block `c: L178` on, t bytes left past s, d of them just written:
    `c: _IO_default_xsputn` of the t bytes from s + d, when there are
    any, and the return of n less those it left. *)
Lemma wp_xs_L178 eb X fb freg vb vreg nb wp we dq b' reg' so c' ys t d e Φ :
  let n := Z.of_nat (length ys) in
  overflow_spec w0 registry ge (xos w0 eb X) -> ge_fn ge "_IO_new_file_overflow" glibc__IO_new_file_overflow ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 -> nb <> None ->
  c' = Obj b' \/ c' = Ro b' -> b' mod 8 = 0 -> 0 <= so -> b' + so + n <= r_end reg' -> r_end reg' <= 2 ^ 63 ->
  Forall (fun y => 0 <= y < 256) ys -> 0 <= t -> 0 <= d -> t + d <= n ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v4") e = Some (WInt n) ->
  lookup (TAtom "pr.3") e = Some (WInt t) -> lookup (TAtom "v175") e = Some (WInt d) ->
  lookup (TAtom "pr.1") e = Some (WPtr (mkPtr (b' + so + (n - t - d)) c')) ->
  vtables_ro ge vb vreg -∗ live fb freg -∗ pcell fb off_vtable (mkPtr (vb + vt_file) (Ro vb)) -∗
  wbuf fb nb wp we -∗ xos w0 eb X fb nb -∗ liveq dq b' reg' -∗ bytesq dq b' so ys -∗
  ▷ (xs_post w0 registry ge) eb X fb freg vb n dq b' reg' so ys Φ -∗
  WP (ERun (mkFrame glibc__IO_new_file_xsputn e [] None (Exec (TAtom "L178") (b_insts xs_L178) (b_jump xs_L178)))
        : sexpr) {{ Φ }}.
Proof.
  intros n Hov Hfo Hfb Hfal Hfend Hfreg Hnb Hc' Hb8' Hso Hyend Hyreg Hy Ht Hd Htd Hv0 Hv4 Hp3 Hv175 Hp1.
  iIntros "#Hvt Hl Hvtp Hwb Hos Hl' Hys HK".
  iApply (wp_live_fit with "Hl'"). iIntros ([Hb'0 _]) "Hl'".
  cbn [xs_L178 b_insts b_jump]. step.
  destruct (Z.eq_dec t 0) as [-> | Ht0].
  - (* Nothing left: L122 returns n. *)
    branch_as true. step. step. iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' Hys"). split; [right; unwrap2; lia | intros _; exact Hnb].
  - branch_as false. step. step.
    set (j := Z.to_nat (n - t)).
    iEval (rewrite (bytesq_split dq b' so ys j); [|lia]) in "Hys". iDestruct "Hys" as "[Hys1 Hys2]".
    assert (Hlj : Z.of_nat (length (drop j ys)) = t) by (rewrite length_drop; lia).
    iApply (wp_call_bind _ _ _ _ _ _ _ _ _ _ _ _ ([WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b' + (so + Z.of_nat j)) c'); WInt (Z.of_nat (length (drop j ys)))]));
      [| exact Hdxf | reflexivity |].
    { cbn -[put]. lookups. rewrite Hlj. do 5 f_equal; unfold j; unwrap2; lia. }
    iNext.
    iApply (wp_glibc__IO_default_xsputn Hmove Hmove_fn Hmove_sym _ (xos w0 eb X) fb freg vb
              vreg nb wp we dq b' reg' (so + Z.of_nat j) c' (drop j ys) with "Hvt Hl Hvtp Hwb Hos Hl' Hys2");
      [reflexivity | exact Hov | exact Hfo | exact Hfb | exact Hfal | exact Hfend | exact Hfreg | exact Hc' | exact Hb8'
      | lia | lia | exact Hyreg | apply Forall_drop; exact Hy |].
    iNext. iIntros (k nb' wp' we' [Hk Hprogress]) "Hl Hvtp Hwb Hos Hl' Hys2". resume.
    rewrite Hlj in Hk. rewrite (Z.mod_small k); [|lia].
    step. step. step. step. iApply wp_ret; [reflexivity | vx |]. iNext.
    iApply ("HK" with "[%] Hl Hvtp Hwb Hos Hl' [Hys1 Hys2]").
    { split; [right; unwrap2; lia | intros _; apply Hprogress; rewrite Hlj; lia]. }
    iApply (bytesq_split dq b' so ys j); [lia|]. iFrame.
Qed.

End rules.
