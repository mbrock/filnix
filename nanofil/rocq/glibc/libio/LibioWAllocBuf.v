(** A wide stream keeps its wide characters in a second buffer, and it
    has no such buffer before its first wide output.
    `c: _IO_wdoallocbuf` gives the stream that buffer. An unbuffered
    stream gets room for one character inside its own wide data, and
    any other stream gets a buffer from the heap. This file proves the
    function for both kinds of stream.

    The stream also needs its ordinary buffer of bytes, because it
    converts the wide characters into bytes there. The wide output
    asks `c: _IO_doallocbuf` for that buffer, and this file proves that
    function for a wide stream as well. *)

From Glibc Require Import GlibcProgram GlibcTactics LibioTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioSetb LibioPutsInv
  LibioReadCode LibioDoAllocBase LibioWIdle LibioWAllocCode LibioWAllocSetb LibioWAllocFile.
From Glibc Require FileInv LibioLogic OsWorld SysWrappers.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Import LibioDoAllocBase SysWrappers FileInv.ML FileInv.LG FileInv.L OsWorld FileInv LibioLogic.

(** The compiled code tests the unbuffered bit of the flags in 32-bit
    steps. This lemma says that the steps compute the bit of the flags
    word itself. *)
Lemma unbuffered_test fl : 0 <= fl < 2 ^ 32 ->
  Z.land (fl mod 2 ^ 32) (2 mod 2 ^ 32) mod 2 ^ 32 = Z.land fl 2.
Proof.
  intros H. change (2 mod 2 ^ 32) with 2. rewrite (Z.mod_small fl); [|lia]. apply Z.mod_small.
  apply land_lt32; lia.
Qed.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_wsetb` frees an old heap buffer with `c: free`, as
    [free_rule] of [LibioSetb](LibioSetb.v) states. *)
Context (Hfree : free_rule w0 registry ge).
(** The genv defines `c: _IO_wsetb`. *)
Context `{Hwsetbf : !Defines ge "__GI__IO_wsetb" glibc__IO_wsetb}.
(** The genv defines `c: _IO_wfile_doallocate` at the symbol that the
    allocation slot of the wide jump table holds. *)
Context (Hwdaf : ge_fn ge "_IO_wfile_doallocate" glibc__IO_wfile_doallocate).

(** ## A stream without a wide buffer

    `c: _IO_wdoallocbuf` returns at once when the stream has a wide
    buffer. A stream without one takes one of two paths, and the
    unbuffered bit of its flags chooses between them. This section
    proves each path. *)

(** An unbuffered stream gets the short buffer of its wide data object
    wd. The function passes the buffer to `c: _IO_wsetb` with a zero
    last argument, so the owner bit of `c: _flags2` is set and a later
    close does not free the buffer. *)
Lemma wp_glibc__IO_wdoallocbuf_short fr fb freg fl f2 wd wreg oe Φ :
  call_frame glibc__IO_wdoallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  Z.land fl io_unbuffered <> 0 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗
  pcell fb off_wide (mkPtr wd (Obj wd)) -∗ live wd wreg -∗ pcell wd 48 null -∗ pcell wd 56 oe -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 (wsetb_flags2 f2 0) -∗
     pcell fb off_wide (mkPtr wd (Obj wd)) -∗ live wd wreg -∗
     pcell wd 48 (mkPtr (wd + woff_shortbuf) (Obj wd)) -∗
     pcell wd 56 (mkPtr (wd + woff_shortbuf + 4) (Obj wd)) -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hfree Hwsetbf.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Hub. injection Hfr as <-.
  iIntros "Hl [%Hfr Hfl] Hf2 Hw Hwl Hb He HK". assert (Hend' := Hend). unfold file_size in Hend'.
  unfold io_unbuffered in Hub.
  step. step. norm. check "Hl". load_pointer "Hl Hw Hwl" by ar. iNext. iIntros "Hl Hw Hwl".
  step. norm. check "Hwl". load_pointer "Hwl Hb [//]" by ar. iNext. iIntros "Hwl Hb _".
  step. step. branch. step. check "Hl". load_s32_group "Hl Hfl". step. step.
  branch_symbolic. rewrite (unbuffered_test fl Hfr).
  replace (Z.land fl 2 =? 0 mod 2 ^ 32) with false by (symmetry; apply Z.eqb_neq; exact Hub).
  change ((if false then 1 else 0) mod 2 ^ 32 =? 0) with true. cbn [edge_label].
  step. step. norm. check "Hl". load_pointer "Hl Hw Hwl" by ar. iNext. iIntros "Hl Hw Hwl".
  step. load_pointer "Hl Hw Hwl" by ar. iNext. iIntros "Hl Hw Hwl". step. step. norm.
  iApply wp_call_bind; [vx | exact Hwsetbf | reflexivity |]. iNext.
  iApply (wp_glibc__IO_wsetb_null Hfree _ fb freg f2 wd wreg oe _ _ 0 with "Hl Hf2 Hw Hwl Hb He"); try libio_side.
  iNext. iIntros "Hl Hf2 Hw Hwl Hb He". iExists _. iSplit; [iPureIntro; reflexivity|]. iNext.
  iApply wp_ret_void. iNext. iApply ("HK" with "Hl [$Hfl //] Hf2 Hw Hwl Hb He").
  Unshelve. exact freg.
Qed.

(** A buffered stream gets a buffer from the heap. The function finds
    the allocation function in the stream's wide jump table and calls
    it. For a file that function is `c: _IO_wfile_doallocate`. The
    memory that the call needs depends on the stream's narrow buffer.
    The lemma therefore assumes that the call is safe when it owns the
    stream's flags, the wide buffer's base and some further memory R.
    The call must return 1 and give back the memory Q. *)
Lemma wp_glibc__IO_wdoallocbuf_alloc fr fb freg fl wd wreg vb vreg (R Q : iProp Σ) Φ :
  call_frame glibc__IO_wdoallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  Z.land fl io_unbuffered = 0 ->
  (forall cfr Ψ, call_frame glibc__IO_wfile_doallocate [WPtr (mkPtr fb (Obj fb))] = Some cfr ->
     live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
     live wd wreg -∗ pcell wd 48 null -∗ R -∗
     ▷ (Q -∗ Ψ (Ret (WInt 1))) -∗ WP (ERun cfr : sexpr) {{ Ψ }}) ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 null -∗ pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ R -∗
  ▷ (pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ Q -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hwdaf.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Hub Hcallee. injection Hfr as <-.
  iIntros "#Hvt #Hwvt Hl Hfl Hw Hwl Hb Hwvtp HR HK". assert (Hend' := Hend). unfold file_size in Hend'.
  unfold io_unbuffered in Hub.
  iPoseProof (wvtables_slot ge vb slot_doallocate "_IO_wfile_doallocate" with "Hwvt") as "#Hsd"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_wfile_doallocate")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hwdaf). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  step. step. norm. check "Hl". load_pointer "Hl Hw Hwl" by ar. iNext. iIntros "Hl Hw Hwl".
  step. norm. check "Hwl". load_pointer "Hwl Hb [//]" by ar. iNext. iIntros "Hwl Hb _".
  step. step. branch. step. check "Hl". iDestruct "Hfl" as "[%Hflr Hfl]". load_s32_group "Hl Hfl". step. step.
  unfold woff_vtable. branch_symbolic. rewrite (unbuffered_test fl Hflr) Hub.
  change ((if 0 =? 0 mod 2 ^ 32 then 1 else 0) mod 2 ^ 32 =? 0) with false. cbn [edge_label].
  step. step. load_pointer "Hl Hw Hwl" by ar. iNext. iIntros "Hl Hw Hwl". step. norm. check "Hwl".
  iApply (wp_raw_load_pointer_dq with "Hwl Hwvtp Hvl");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_wfile in *; lia |].
  iNext. iIntros "Hwl Hwvtp #Hvl'". step. norm.
  check_read_dq "Hvl'" by ar. iNext. iIntros "_".
  iApply (wp_raw_load_pointer_dq with "Hvl' Hsd Hfc");
    [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hwdaf) |].
  iNext. iIntros "_ _ _".
  iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hwdaf) |]. iNext.
  iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hwdaf) | apply (ge_fn_check _ _ _ Hwdaf) | vx |
    apply (ge_fn_find _ _ _ Hwdaf) | reflexivity | reflexivity |].
  iNext. iApply (Hcallee _ _ eq_refl with "Hl [$Hfl //] Hw Hwl Hb HR"). iNext. iIntros "HQ".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  step. branch. step. iApply wp_ret_void. iNext. iApply ("HK" with "Hwvtp HQ").
  Unshelve. exact freg.
Qed.

(** ## The narrow function on a wide stream

    `c: _IO_wfile_overflow` also calls the narrow `c: _IO_doallocbuf`,
    because a wide stream converts its characters into the narrow
    buffer. This section proves the two paths that a wide stream takes
    through that function. *)

(** A stream that has a narrow buffer returns at once. The function
    only loads the buffer's base x, and that load needs a share of the
    life of the object that x names. The lemma takes shares rather than
    whole lives, because the short buffer lies inside the stream object
    itself, so its caller splits the stream's life in two. *)
Lemma wp_glibc__IO_doallocbuf_have fr fb freg x reg' dq1 dq3 Φ :
  call_frame glibc__IO_doallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < ptr_addr x < 2 ^ 64 ->
  liveq dq1 fb freg -∗ pcell fb off_buf_base x -∗ live_capq dq3 (ptr_cap x) reg' -∗
  ▷ (liveq dq1 fb freg -∗ pcell fb off_buf_base x -∗ live_capq dq3 (ptr_cap x) reg' -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Type.
  intros Hfr Hfb Hal Hend Hfreg Hx. injection Hfr as <-.
  iIntros "Hl Hb Hxl HK". assert (Hend' := Hend). unfold file_size in Hend'.
  step. step. norm. check_read_dq "Hl" by ar. iNext. iIntros "Hl".
  iApply (wp_raw_load_pointer_dq with "Hl Hb Hxl"); [reflexivity | vx | left; reflexivity | ar | ar | lia |].
  iNext. iIntros "Hl Hb Hxl". step. step. branch_as false. step. iApply wp_ret_void. iNext.
  iApply ("HK" with "Hl Hb Hxl").
Qed.

(** A wide stream that has no narrow buffer asks its jump table for
    one. The table of a wide stream names `c: _IO_wfile_doallocate` as
    its allocation function, so the stream calls that function. An
    unbuffered wide stream makes the same call, because only a stream
    that is not wide uses the short buffer here. The lemma assumes
    that the call is safe when it owns the memory R, and that the call
    returns 1 and gives back the memory Q. *)
Lemma wp_glibc__IO_doallocbuf_wide fr fb freg fl vb vreg (R Q : iProp Σ) Φ :
  call_frame glibc__IO_doallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (forall cfr Ψ, call_frame glibc__IO_wfile_doallocate [WPtr (mkPtr fb (Obj fb))] = Some cfr ->
     live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode 1 -∗ pcell fb off_buf_base null -∗
     pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ R -∗
     ▷ (Q -∗ Ψ (Ret (WInt 1))) -∗ WP (ERun cfr : sexpr) {{ Ψ }}) ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode 1 -∗ pcell fb off_buf_base null -∗
  pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ R -∗
  ▷ (Q -∗ Φ RetVoid) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hwdaf.
  intros Hfr Hfb Hal Hend Hfreg Hcallee. injection Hfr as <-.
  iIntros "#Hvt #Hwvt Hl Hfl Hmd Hb Hvtp HR HK". assert (Hend' := Hend). unfold file_size in Hend'.
  iPoseProof (wvtables_slot ge vb slot_doallocate "_IO_wfile_doallocate" with "Hwvt") as "#Hsd"; [cbn; tauto|].
  iAssert (live_capq DfracDiscarded (ptr_cap (sym_ptr ge "_IO_wfile_doallocate")) vreg) as "Hfc".
  { rewrite (ge_fn_cap _ _ _ Hwdaf). done. }
  iDestruct "Hvt" as "((%Hvg & %Hvend & %Hval & %Hvb & %Hvreg) & Hvl & Hslots)".
  unfold io_vtables_size in Hvend.
  step. step. norm. check "Hl". load_pointer "Hl Hb [//]" by ar. iNext. iIntros "Hl Hb _".
  step. step. branch. step. check "Hl". iDestruct "Hfl" as "[%Hflr Hfl]". load_s32_group "Hl Hfl". step. step.
  iDestruct "Hmd" as "[%Hmdr Hmd]".
  branch_symbolic. rewrite (unbuffered_test fl Hflr).
  destruct (Z.eq_dec (Z.land fl 2) 0) as [Hub | Hub].
  1: rewrite Hub. 1: change ((if 0 =? 0 mod 2 ^ 32 then 1 else 0) mod 2 ^ 32 =? 0) with false. 1: cbn [edge_label].
  1: step. 1: branch.
  2: replace (Z.land fl 2 =? 0 mod 2 ^ 32) with false by (symmetry; apply Z.eqb_neq; exact Hub).
  2: change ((if false then 1 else 0) mod 2 ^ 32 =? 0) with true. 2: cbn [edge_label].
  2: step. 2: step. 2: check "Hl". 2: load_s32_group "Hl Hmd". 2: step. 2: step. 2: step. 2: branch.
  all: step; step; norm; check "Hl".
  all: iApply (wp_raw_load_pointer_dq with "Hl Hvtp Hvl");
      [reflexivity | vx | left; reflexivity | ar | ar | cbn; unfold vt_wfile in *; lia |].
  all: iNext; iIntros "Hl Hvtp #Hvl'"; step; step; step; step; step; branch_as true.
  all: step; step; norm; check_read_dq "Hvl'" by ar.
  all: iNext; iIntros "_".
  all: iApply (wp_raw_load_pointer_dq with "Hvl' Hsd Hfc");
      [reflexivity | vx | right; reflexivity | ar | ar | apply (ge_fn_addr _ _ _ Hwdaf) |].
  all: iNext; iIntros "_ _ _".
  all: iApply wp_check_function; [vx | apply (ge_fn_check _ _ _ Hwdaf) |]; iNext.
  all: iApply wp_raw_call_bind; [vx | apply (ge_fn_cap _ _ _ Hwdaf) | apply (ge_fn_check _ _ _ Hwdaf) | vx |
      apply (ge_fn_find _ _ _ Hwdaf) | reflexivity | reflexivity |].
  all: iNext; iApply (Hcallee _ _ eq_refl with "Hl [$Hfl //] [$Hmd //] Hb Hvtp HR"); iNext; iIntros "HQ".
  all: iExists _; iSplit; [iPureIntro; reflexivity|]; iNext; cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  all: step; branch; step; iApply wp_ret_void; iNext; iApply ("HK" with "HQ").
  Unshelve. all: exact freg.
Qed.

(** ## The complete contracts

    Two lemmas above assume that the call of `c: _IO_wfile_doallocate`
    is safe. This section removes that assumption. It uses the proofs
    in [LibioWAllocFile](LibioWAllocFile.v), which cover a stream with
    a narrow heap buffer, a stream with the short narrow buffer, and a
    stream with no narrow buffer. The proof of `c: _IO_wfile_overflow`
    can then apply one lemma for each of these streams. *)

(** The genv defines `c: _IO_file_doallocate`. *)
Context `{Hdaf : !Defines ge "__GI__IO_file_doallocate" glibc__IO_file_doallocate}.
(** The proposition Mres stands for the allocator's state. A call of
    `c: malloc` takes it and gives it back. *)
Context (Mres : iProp Σ).
(** `c: malloc(n)` returns a fresh object of at least n zero bytes, in
    the form that [LibioWAllocFile](LibioWAllocFile.v) assumes. *)
Context (Hmalloc : forall f e ls lab d v rest j n Φ,
  arg_x ge e (Arg L v) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  Mres -∗
  ▷ (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ -∗
       obj base (heap_req 16 n) -∗ Mres -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec lab rest j))
             : language.expr (nanofil_lang registry ge)) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d P) (Global (TAtom "malloc")) [Arg L v] :: rest) j))
        : language.expr (nanofil_lang registry ge)) {{ Φ }}).
(** A stream without a narrow buffer gets one from
    `c: _IO_file_doallocate`. The proofs assume that this function is
    safe on a wide stream and that it installs a fresh buffer, as
    [LibioWAllocFile](LibioWAllocFile.v) also assumes. *)
Context (Hda_wide : forall fr fb freg fl fd eb oe vb vreg Φ,
  call_frame glibc__IO_file_doallocate [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
  Mres -∗
  ▷ (pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ doalloc_k Mres fb freg fl fd eb Φ) -∗
  WP (ERun fr : sexpr) {{ Φ }}).

(** A buffered stream with neither buffer gets both from
    `c: _IO_wdoallocbuf`: a fresh narrow buffer of sz bytes and a wide
    heap buffer for sz characters. *)
Lemma wp_glibc__IO_wdoallocbuf_from_null fr fb freg fl fd eb noe vb vreg f2 wd wreg oe Φ :
  call_frame glibc__IO_wdoallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  Z.land fl io_unbuffered = 0 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end noe -∗
  pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
  int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 null -∗ pcell wd 56 oe -∗
  pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ Mres -∗
  ▷ (∀ fl1 bb sz, ⌜(fl1 = fl \/ fl1 = Z.lor fl io_line_buf) /\ 0 < sz <= 8192 /\ 0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
     pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
     int_cell fb off_flags (setb_flags fl1 1) -∗ int_cell fb off_fileno fd -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ errno_any eb -∗ walloc_k Mres fb freg f2 wd wreg (4 * sz) (fun _ => Φ RetVoid)) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hfree Hwsetbf Hwdaf Hdaf Hmalloc Hda_wide.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Herrno Hfd Hfd31 Hub.
  iIntros "#Hvt #Hwvt Hl Hfl Hfd Herr Hnb Hne Hvtp Hf2 Hw Hwl Hb He Hwvtp HM HK".
  iCombine "Hvt Hwvt Hfd Herr Hnb Hne Hvtp Hf2 He HM HK" as "HR".
  iApply (wp_glibc__IO_wdoallocbuf_alloc fr fb freg fl wd wreg vb vreg _
            (pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ Φ RetVoid)%I
            with "Hvt Hwvt Hl Hfl Hw Hwl Hb Hwvtp HR"); try first [assumption | libio_side].
  2: iNext; iIntros "Hwvtp HQ"; iApply ("HQ" with "Hwvtp").
  intros cfr Ψ Hcfr.
  iIntros "Hl Hfl Hw Hwl Hb (#Hvt & #Hwvt & Hfd & Herr & Hnb & Hne & Hvtp & Hf2 & He & HM & HK) HΨ".
  iApply (wp_glibc__IO_wfile_doallocate_null Hfree Mres Hmalloc Hda_wide cfr fb freg fl fd eb noe vb vreg
            f2 wd wreg WbNone oe with "Hvt Hwvt Hl Hfl Hfd Herr Hnb Hne Hvtp Hf2 Hw Hwl Hb He [//] HM");
    try first [assumption | exact I | libio_side].
  iNext. iIntros (fl1 bb sz Hc) "Hvtp Hfl Hfd Hnb Hne Hbo Herr". iIntros (p Hp) "Hl Hf2 Hw Hwl Hb He Hwb HM".
  iApply "HΨ". iIntros "Hwvtp".
  iApply ("HK" $! fl1 bb sz with "[//] Hwvtp Hvtp Hfl Hfd Hnb Hne Hbo Herr [//] Hl Hf2 Hw Hwl Hb He Hwb HM").
Qed.

(** A buffered stream that already has a narrow heap buffer of sz
    bytes keeps it, and `c: _IO_wdoallocbuf` gives it a wide heap
    buffer for [wide_count] fl sz characters. *)
Lemma wp_glibc__IO_wdoallocbuf_from_heap fr fb freg fl vb vreg f2 wd wreg oe bb sz breg Φ :
  call_frame glibc__IO_wdoallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  0 < bb -> 0 < sz < 2 ^ 62 -> bb + sz < 2 ^ 64 -> Z.land fl io_unbuffered = 0 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗
  pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗ live bb breg -∗
  int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 null -∗ pcell wd 56 oe -∗
  pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ Mres -∗
  ▷ (pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
     int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗
     pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗ live bb breg -∗
     walloc_k Mres fb freg f2 wd wreg (4 * wide_count fl sz) (fun _ => Φ RetVoid)) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hfree Hwsetbf Hwdaf Hmalloc.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Hbb Hsz Hbe Hub.
  iIntros "#Hvt #Hwvt Hl Hfl Hnb Hne Hbl Hf2 Hw Hwl Hb He Hwvtp HM HK".
  iCombine "Hnb Hne Hbl Hf2 He HM HK" as "HR".
  iApply (wp_glibc__IO_wdoallocbuf_alloc fr fb freg fl wd wreg vb vreg _
            (pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ Φ RetVoid)%I
            with "Hvt Hwvt Hl Hfl Hw Hwl Hb Hwvtp HR"); try first [assumption | libio_side].
  2: iNext; iIntros "Hwvtp HQ"; iApply ("HQ" with "Hwvtp").
  intros cfr Ψ Hcfr. iIntros "Hl Hfl Hw Hwl Hb (Hnb & Hne & Hbl & Hf2 & He & HM & HK) HΨ".
  iApply (wp_glibc__IO_wfile_doallocate_heap Hfree Mres Hmalloc cfr fb freg fl f2 wd wreg WbNone oe bb sz breg
            with "Hl Hfl Hnb Hne Hbl Hf2 Hw Hwl Hb He [//] HM"); try first [assumption | exact I | libio_side].
  iNext. iIntros "Hfl Hnb Hne Hbl". iIntros (p Hp) "Hl Hf2 Hw Hwl Hb He Hwb HM".
  iApply "HΨ". iIntros "Hwvtp".
  iApply ("HK" with "Hwvtp Hfl Hnb Hne Hbl [//] Hl Hf2 Hw Hwl Hb He Hwb HM").
Qed.

(** A buffered stream whose narrow buffer is the one-byte short buffer
    keeps it, and `c: _IO_wdoallocbuf` gives it a wide heap buffer for
    one character. A stream is in this state when it was unbuffered
    while it got its narrow buffer and became buffered afterwards. *)
Lemma wp_glibc__IO_wdoallocbuf_from_short fr fb freg fl vb vreg f2 wd wreg oe Φ :
  call_frame glibc__IO_wdoallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  Z.land fl io_unbuffered = 0 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr (fb + 131) (Obj fb)) -∗
  pcell fb off_buf_end (mkPtr (fb + 132) (Obj fb)) -∗
  int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 null -∗ pcell wd 56 oe -∗
  pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ Mres -∗
  ▷ (pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
     int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr (fb + 131) (Obj fb)) -∗
     pcell fb off_buf_end (mkPtr (fb + 132) (Obj fb)) -∗
     walloc_k Mres fb freg f2 wd wreg 4 (fun _ => Φ RetVoid)) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hfree Hwsetbf Hwdaf Hmalloc.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Hub.
  iIntros "#Hvt #Hwvt Hl Hfl Hnb Hne Hf2 Hw Hwl Hb He Hwvtp HM HK".
  iCombine "Hnb Hne Hf2 He HM HK" as "HR".
  iApply (wp_glibc__IO_wdoallocbuf_alloc fr fb freg fl wd wreg vb vreg _
            (pcell wd woff_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ Φ RetVoid)%I
            with "Hvt Hwvt Hl Hfl Hw Hwl Hb Hwvtp HR"); try first [assumption | libio_side].
  2: iNext; iIntros "Hwvtp HQ"; iApply ("HQ" with "Hwvtp").
  intros cfr Ψ Hcfr. iIntros "Hl Hfl Hw Hwl Hb (Hnb & Hne & Hf2 & He & HM & HK) HΨ".
  iApply (wp_glibc__IO_wfile_doallocate_short Hfree Mres Hmalloc cfr fb freg fl f2 wd wreg WbNone oe
            with "Hl Hfl Hnb Hne Hf2 Hw Hwl Hb He [//] HM"); try first [assumption | exact I | libio_side].
  iNext. iIntros "Hfl Hnb Hne". iIntros (p Hp) "Hl Hf2 Hw Hwl Hb He Hwb HM".
  iApply "HΨ". iIntros "Hwvtp".
  iApply ("HK" with "Hwvtp Hfl Hnb Hne [//] Hl Hf2 Hw Hwl Hb He Hwb HM").
Qed.

(** A wide stream without a narrow buffer gets one from the narrow
    `c: _IO_doallocbuf`, and with it a new wide heap buffer for as many
    characters. The old wide buffer w may be of any kind. It is the
    short wide buffer when `c: _IO_wdoallocbuf` has just served an
    unbuffered stream, and `c: _IO_wsetb` then replaces it without a
    call of `c: free`. *)
Lemma wp_glibc__IO_doallocbuf_wide_null fr fb freg fl fd eb noe vb vreg f2 wd wreg w oe Φ :
  call_frame glibc__IO_doallocbuf [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 -> wbuf_user_ok w f2 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_mode 1 -∗ int_cell fb off_fileno fd -∗
  errno_any eb -∗ pcell fb off_buf_base null -∗ pcell fb off_buf_end noe -∗
  pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
  int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 (wbuf_base wd w) -∗ pcell wd 56 oe -∗ wbuf_idle w -∗ Mres -∗
  ▷ (∀ fl1 bb sz, ⌜(fl1 = fl \/ fl1 = Z.lor fl io_line_buf) /\ 0 < sz <= 8192 /\ 0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     int_cell fb off_mode 1 -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
     int_cell fb off_flags (setb_flags fl1 1) -∗ int_cell fb off_fileno fd -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ errno_any eb -∗ walloc_k Mres fb freg f2 wd wreg (4 * sz) (fun _ => Φ RetVoid)) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hfree Hwsetbf Hwdaf Hdaf Hmalloc Hda_wide.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Herrno Hfd Hfd31 Hu.
  iIntros "#Hvt #Hwvt Hl Hfl Hmd Hfd Herr Hnb Hne Hvtp Hf2 Hw Hwl Hb He Hold HM HK".
  iCombine "Hvt Hwvt Hfd Herr Hne Hf2 Hw Hwl Hb He Hold HM HK" as "HR".
  iApply (wp_glibc__IO_doallocbuf_wide fr fb freg fl vb vreg _ (Φ RetVoid)
            with "Hvt Hwvt Hl Hfl Hmd Hnb Hvtp HR"); try first [assumption | libio_side].
  2: iNext; iIntros "HQ"; iExact "HQ".
  intros cfr Ψ Hcfr.
  iIntros "Hl Hfl Hmd Hnb Hvtp (#Hvt & #Hwvt & Hfd & Herr & Hne & Hf2 & Hw & Hwl & Hb & He & Hold & HM & HK) HΨ".
  iApply (wp_glibc__IO_wfile_doallocate_null Hfree Mres Hmalloc Hda_wide cfr fb freg fl fd eb noe vb vreg
            f2 wd wreg w oe with "Hvt Hwvt Hl Hfl Hfd Herr Hnb Hne Hvtp Hf2 Hw Hwl Hb He Hold HM");
    try first [assumption | libio_side].
  iNext. iIntros (fl1 bb sz Hc) "Hvtp Hfl Hfd Hnb Hne Hbo Herr". iIntros (p Hp) "Hl Hf2 Hw Hwl Hb He Hwb HM".
  iApply "HΨ".
  iApply ("HK" $! fl1 bb sz with "[//] Hmd Hvtp Hfl Hfd Hnb Hne Hbo Herr [//] Hl Hf2 Hw Hwl Hb He Hwb HM").
Qed.

End rules.
