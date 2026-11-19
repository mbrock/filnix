(** A wide stream needs two buffers before its first output: the
    narrow buffer that holds the converted bytes, and a wide buffer
    that holds the characters before conversion.
    `c: _IO_wfile_doallocate` provides both. It asks
    `c: _IO_file_doallocate` for a narrow buffer when the stream has
    none, and then it allocates a wide buffer with room for as many
    wide characters as the narrow buffer has bytes. This file proves
    the function for each narrow buffer that a wide stream can have
    when the call happens.

    A caller runs this function in the middle of a write, when the
    stream as a whole is between two consistent states. The contracts
    therefore ask only for the fields that the function reads and
    writes, as the contract of `c: _IO_wsetb` in
    [LibioWAllocSetb](LibioWAllocSetb.v) does. *)

From Glibc Require Import Unit_libio_filedoalloc_os Unit_libio_wfiledoalloc_os Unit_libio_wgenops_os.
From Glibc Require Import GlibcProgram GlibcTactics OsTactics.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsRegistry FileInv LibioLogic SysWrappers LibioSetb LibioPutsInv
  LibioDoAllocBase LibioWIdle LibioWAllocSetb.
From Glibc Require Import Fix.
Import ListNotations.
Open Scope Z_scope.

Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

Import LibioDoAllocBase SysWrappers Fix.ML0 Fix.LG0 Fix.LG0.L OsWorld FileInv LibioLogic.

(** ## The size of the wide buffer

    The function measures the narrow buffer and allocates four bytes
    of wide buffer for each of its bytes. A narrow buffer that the
    stream does not own is measured differently, and this section
    names the result. *)

(** The function [wide_count] gives the number of wide characters that
    the function allocates for a narrow buffer of sz bytes on a stream
    with the flags fl. When bit 0 of the flags, `c: _IO_USER_BUF`, is
    set, the function divides the size by four and rounds up. *)
Definition wide_count (fl sz : Z) : Z := if Z.land fl 1 =? 0 then sz else (sz + 3) / 4.

(** The count is positive for a narrow buffer that is not empty, and
    it is never larger than the buffer's size. *)
Lemma wide_count_range fl sz : 0 < sz -> 0 < wide_count fl sz <= sz.
Proof. intros H. unfold wide_count. destruct (Z.land fl 1 =? 0); [lia|]. Z.div_mod_to_equations. lia. Qed.

(** A narrow buffer that `c: _IO_file_doallocate` installed belongs to
    the stream, so the function allocates one wide character for each
    of its bytes. *)
Lemma wide_count_owned fl sz : wide_count (setb_flags fl 1) sz = sz.
Proof.
  unfold wide_count, setb_flags. cbn [Z.eqb]. rewrite -Z.land_assoc. change (Z.land 4294967294 1) with 0.
  rewrite Z.land_0_r. reflexivity.
Qed.

(** The one-byte short buffer gets one wide character whether or not
    the stream owns it. *)
Lemma wide_count_one fl : wide_count fl 1 = 1.
Proof. unfold wide_count. destruct (Z.land fl 1 =? 0); reflexivity. Qed.

(** A number has bit 0 either clear or set. The proof of the measuring
    block uses this to decide the branch on `c: _IO_USER_BUF`. *)
Lemma land1_cases x : Z.land x 1 = 0 \/ Z.land x 1 = 1.
Proof.
  pose proof (Z.land_ones x 1 ltac:(lia)) as H. change (Z.ones 1) with 1 in H. rewrite H. change (2 ^ 1) with 2.
  pose proof (Z.mod_pos_bound x 2 ltac:(lia)). lia.
Qed.

(** The compiled code rounds the size up in three 64-bit steps. This
    lemma says that the steps compute the quotient that [wide_count]
    names. *)
Lemma wide_count_steps sz : 0 < sz < 2 ^ 62 ->
  (((((sz mod 2 ^ 64 + 4 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64 - 1 mod 2 ^ 64) mod 2 ^ 64) mod 2 ^ 64
     / 2 ^ ((2 mod 2 ^ 32) mod 64)) mod 2 ^ 64 = (sz + 3) / 4.
Proof.
  intros H. change (2 ^ ((2 mod 2 ^ 32) mod 64)) with 4. change (4 mod 2 ^ 64) with 4. change (1 mod 2 ^ 64) with 1.
  rewrite (Z.mod_small sz); [|lia]. rewrite (Z.mod_small (sz + 4)); [|lia]. rewrite (Z.mod_small (sz + 4)); [|lia].
  rewrite (Z.mod_small (sz + 4 - 1)); [|lia]. rewrite (Z.mod_small (sz + 4 - 1)); [|lia].
  replace (sz + 4 - 1) with (sz + 3) by lia.
  apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.

Import ProgramAbbreviations.
Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** `c: _IO_wsetb` frees an old heap buffer with `c: free`, as
    [free_rule] of [LibioSetb](LibioSetb.v) states. *)
Context (Hfree : free_rule w0 registry ge).
(** The genv defines `c: _IO_wsetb`. *)
Context `{Hwsetbf : !Defines ge "__GI__IO_wsetb" Unit_libio_wgenops_os.fn___GI__IO_wsetb}.
(** The proposition Mres stands for the allocator's state. A call of
    `c: malloc` takes it and gives it back. *)
Context (Mres : iProp Σ).
(** `c: malloc(n)` returns a fresh object of at least n zero bytes.
    The hypothesis has the form that
    [LibioDoAllocTail](LibioDoAllocTail.v) uses for the narrow
    buffer. *)
Context (Hmalloc : forall f e ls lab d v rest j n Φ,
  arg_x ge e (Arg L v) = Some (WInt n) -> 0 <= n < 2 ^ 64 ->
  Mres -∗
  ▷ (∀ base, ⌜0 < base /\ base mod 16 = 0 /\ base + req_extent (heap_req 16 n) <= 2 ^ 48⌝ -∗
       obj base (heap_req 16 n) -∗ Mres -∗
       WP (ERun (mkFrame f (put d (WPtr (mkPtr base (Obj base))) e) ls None (Exec lab rest j))
             : language.expr (nanofil_lang registry ge)) {{ Φ }}) -∗
  WP (ERun (mkFrame f e ls None (Exec lab (Call (CResult d P) (Global (TAtom "malloc")) [Arg L v] :: rest) j))
        : language.expr (nanofil_lang registry ge)) {{ Φ }}).

(** ## The wide allocation

    Every path through the function ends in the same block, which
    allocates the wide buffer and installs it. This section proves
    that block once, for any old wide buffer. *)

(** The function returns 1 after it installs a wide heap buffer of n
    bytes. The predicate [walloc_k] says what the caller's
    continuation Φ receives then: the fields that `c: _IO_wsetb` wrote,
    with the owner bit clear, and the new buffer p, which holds zero
    bytes. *)
Definition walloc_k (fb : Z) (freg : region) (f2 wd : Z) (wreg : region) (n : Z)
    (Φ : outcome -> iProp Σ) : iProp Σ :=
  ∀ p, ⌜0 < p /\ p mod 16 = 0 /\ p + n <= 2 ^ 48⌝ -∗
    live fb freg -∗ int_cell fb off_flags2 (wsetb_flags2 f2 1) -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
    live wd wreg -∗ pcell wd 48 (mkPtr p (Obj p)) -∗ pcell wd 56 (mkPtr (p + n) (Obj p)) -∗
    wbuf_idle (WbHeap p n) -∗ Mres -∗ Φ (Ret (WInt 1)).

(** Block `c: L26` receives the number n of wide characters from one of
    two earlier blocks. It allocates 4n bytes and passes them to
    `c: _IO_wsetb`, which frees the old wide buffer w when the stream
    owns it. The model's `c: malloc` always returns an object, so the
    block never returns `c: EOF`. *)
Lemma wp_wfile_doalloc_L26 fb freg f2 wd wreg w oe n from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  0 < n < 2 ^ 62 -> wbuf_user_ok w f2 ->
  (from = TAtom "L24" /\ (exists v, lookup (TAtom "v33") e = Some (WInt v) /\ v mod 2 ^ 64 = n)) \/
  (from = TAtom "L6" /\ (exists v, lookup (TAtom "v23") e = Some (WInt v) /\ v mod 2 ^ 64 = n)) ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v11") e = Some (WInt 0) ->
  live fb freg -∗ int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 (wbuf_base wd w) -∗ pcell wd 56 oe -∗ wbuf_idle w -∗ Mres -∗
  ▷ walloc_k fb freg f2 wd wreg (4 * n) Φ -∗
  WP (ERun (mkFrame Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate e [] None (Enter (TAtom "L26") (Some from))) : sexpr) {{ Φ }}.
Proof using Hfree Hmalloc Hwsetbf.
  intros Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Hn Hu Hfrom Hv0 Hv11.
  iIntros "Hl Hfl Hw Hwl Hb He Hold HM HK".
  destruct Hfrom as [[-> (v & Hv & Hvs)] | [-> (v & Hv & Hvs)]]; step; rewrite Hvs.
  all: step.
  all: replace ((n mod 2 ^ 64 * 2 ^ ((2 mod 2 ^ 32) mod 64)) mod 2 ^ 64) with (4 * n)
    by (change (2 ^ ((2 mod 2 ^ 32) mod 64)) with 4; rewrite (Z.mod_small n); [|lia]; rewrite Z.mod_small; lia).
  all: iApply (Hmalloc _ _ _ _ _ _ _ _ (4 * n) with "HM"); [cbn; rewrite Z.mod_small; [reflexivity | lia] | lia |].
  all: iNext; iIntros (p (Hp0 & Hp16 & Hpext)) "Ho HM".
  all: assert (Hx : 4 * n <= req_extent (heap_req 16 (4 * n))) by (cbn; Z.div_mod_to_equations; lia).
  all: step; step; branch_as true; step; step; norm.
  all: iApply wp_call_bind; [vx | exact Hwsetbf | reflexivity |]; iNext.
  all: iApply (wp_glibc__IO_wsetb Hfree _ fb freg f2 wd wreg w oe _ _ 1 with "Hl Hfl Hw Hwl Hb He Hold");
    try first [exact Hu | libio_side].
  all: iNext; iIntros "Hl Hfl Hw Hwl Hb He"; iExists _; iSplit; [iPureIntro; reflexivity|]; iNext.
  all: iApply wp_ret; [reflexivity | vx |]; iNext.
  all: rewrite obj_zero_block; [|lia]; iDestruct "Ho" as "(Hbl & Hxs & Hcs)".
  all: iDestruct (bytes_take_drop p 0 _ (Z.to_nat (4 * n)) with "Hxs") as "[Hxs _]"; [rewrite length_replicate; lia|].
  all: iDestruct (auxes_take_drop p 0 _ (Z.to_nat (4 * n)) with "Hcs") as "[Hcs _]"; [rewrite length_replicate; lia|].
  all: rewrite !take_replicate.
  all: replace (Nat.min (Z.to_nat (4 * n)) (Z.to_nat (req_extent (heap_req 16 (4 * n))))) with (Z.to_nat (4 * n)) by lia.
  all: change (1 mod 2 ^ 32) with 1.
  all: iApply ("HK" $! p with "[%] Hl Hfl Hw Hwl Hb He [Hbl Hxs Hcs] HM"); [lia|].
  all: iExists _, _, _; iFrame "Hbl Hxs Hcs"; iPureIntro; cbn in Hpext, Hx |- *.
  all: rewrite !length_replicate; repeat split; try apply Forall_replicate; try lia.
  all: clear -Hp16; Z.div_mod_to_equations; lia.
Qed.

(** ## A stream that already has a narrow buffer

    The function reads the narrow buffer's base and end to measure it.
    A load of a pointer needs the life of the object that the pointer
    names. The narrow buffer is either a heap object of its own or the
    one-byte short buffer inside the stream object, so this section
    proves the measuring block once for each. *)

(** The function subtracts the two pointers and then loads the stream's
    flags, whichever kind of narrow buffer the stream has. This tactic
    runs those instructions for both proofs below. *)
Local Ltac measure_flags := step; step; step; check "Hl"; load_s32_group "Hl Hfl"; step.

(** The function next tests whether the stream owns its narrow buffer.
    This tactic proves the rest of the function for both answers, for
    a narrow buffer of sz bytes on a stream with the flags fl. *)
Local Ltac measure_count fl sz w oe :=
  change (1 mod 2 ^ 32) with 1; rewrite (Z.mod_small fl); [|lia];
  unfold wide_count; let E := fresh "E" in
  destruct (land1_cases fl) as [E | E]; rewrite E; cbn [Z.eqb]; branch;
  [ iApply (wp_wfile_doalloc_L26 _ _ _ _ _ w oe sz with "Hl Hf2 Hw Hwl Hb He Hold HM HK");
      try first [solve [right; split; [reflexivity|]; eexists; split; [lk_prove | apply Z.mod_small; lia]]
                | libio_side]
  | do 5 step;
    iApply (wp_wfile_doalloc_L26 _ _ _ _ _ w oe ((sz + 3) / 4) with "Hl Hf2 Hw Hwl Hb He Hold HM HK");
      try first [solve [left; split; [reflexivity|]; eexists; split; [lk_prove | apply wide_count_steps; lia]]
                | solve [Z.div_mod_to_equations; lia] | libio_side] ].

(** Block `c: L6` measures a narrow heap buffer of sz bytes at bb. The
    stream keeps the narrow fields unchanged, and it gets a wide buffer
    for [wide_count] fl sz characters. The size must be below 2^62,
    because the function multiplies the count by four in 64 bits. *)
Lemma wp_wfile_doalloc_L6_heap fb freg fl f2 wd wreg w oe bb sz breg from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  0 < bb -> 0 < sz < 2 ^ 62 -> bb + sz < 2 ^ 64 -> wbuf_user_ok w f2 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v11") e = Some (WInt 0) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗
  pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗ live bb breg -∗
  int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 (wbuf_base wd w) -∗ pcell wd 56 oe -∗ wbuf_idle w -∗ Mres -∗
  ▷ (int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗
     pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗ live bb breg -∗
     walloc_k fb freg f2 wd wreg (4 * wide_count fl sz) Φ) -∗
  WP (ERun (mkFrame Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate e [] None (Enter (TAtom "L6") (Some from))) : sexpr) {{ Φ }}.
Proof using Hfree Hmalloc Hwsetbf.
  intros Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Hbb Hsz Hbe Hu Hv0 Hv11 Hc0.
  iIntros "Hl [%Hfr Hfl] Hnb Hne Hbl Hf2 Hw Hwl Hb He Hold HM HK". unfold file_size in Hend.
  step. step. norm. check "Hl". load_pointer "Hl Hne Hbl" by ar. iNext. iIntros "Hl Hne Hbl".
  step. norm. check "Hl". load_pointer "Hl Hnb Hbl" by ar. iNext. iIntros "Hl Hnb Hbl".
  measure_flags.
  replace (((bb + sz) mod 2 ^ 64 - bb mod 2 ^ 64) mod 2 ^ 64) with sz by (rewrite !Z.mod_small; lia).
  iSpecialize ("HK" with "[$Hfl //] Hnb Hne Hbl"). measure_count fl sz w oe.
Qed.

(** Block `c: L6` measures the short buffer, which is one byte inside
    the stream object. Each pointer load borrows half of the stream's
    life as the life of the object that the pointer names. *)
Lemma wp_wfile_doalloc_L6_short fb freg fl f2 wd wreg w oe from e Φ :
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 -> wbuf_user_ok w f2 ->
  lookup (TAtom "v0") e = Some (WPtr (mkPtr fb (Obj fb))) -> lookup (TAtom "v11") e = Some (WInt 0) ->
  lookup (TAtom "chk0") e = Some (WPtr (mkPtr (fb + off_buf_base) (Obj fb))) ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr (fb + 131) (Obj fb)) -∗
  pcell fb off_buf_end (mkPtr (fb + 132) (Obj fb)) -∗
  int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 (wbuf_base wd w) -∗ pcell wd 56 oe -∗ wbuf_idle w -∗ Mres -∗
  ▷ (int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr (fb + 131) (Obj fb)) -∗
     pcell fb off_buf_end (mkPtr (fb + 132) (Obj fb)) -∗
     walloc_k fb freg f2 wd wreg (4 * wide_count fl 1) Φ) -∗
  WP (ERun (mkFrame Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate e [] None (Enter (TAtom "L6") (Some from))) : sexpr) {{ Φ }}.
Proof using Hfree Hmalloc Hwsetbf.
  intros Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Hu Hv0 Hv11 Hc0.
  iIntros "Hl [%Hfr Hfl] Hnb Hne Hf2 Hw Hwl Hb He Hold HM HK". unfold file_size in Hend.
  step. step. norm. check "Hl". iDestruct (live_halves with "Hl") as "[Hl Hl2]".
  iApply (wp_raw_load_pointer_dq with "Hl Hne Hl2");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn [ptr_addr]; lia |].
  iNext. iIntros "Hl Hne Hl2". iDestruct (live_halves with "[$Hl $Hl2]") as "Hl".
  step. norm. check "Hl". iDestruct (live_halves with "Hl") as "[Hl Hl2]".
  iApply (wp_raw_load_pointer_dq with "Hl Hnb Hl2");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn [ptr_addr]; lia |].
  iNext. iIntros "Hl Hnb Hl2". iDestruct (live_halves with "[$Hl $Hl2]") as "Hl".
  measure_flags.
  replace (((fb + 132) mod 2 ^ 64 - (fb + 131) mod 2 ^ 64) mod 2 ^ 64) with 1 by (rewrite !Z.mod_small; lia).
  iSpecialize ("HK" with "[$Hfl //] Hnb Hne"). measure_count fl 1 w oe.
Qed.

(** ## The whole function

    The function first tests whether the stream has a narrow buffer.
    This section proves it from its entry for a narrow heap buffer,
    for the short buffer, and for a stream without a narrow buffer. In
    each case the old wide buffer w may be of any kind, because
    `c: _IO_doallocbuf` can call the function on a wide stream that
    already uses its short wide buffer. *)

(** A stream with a narrow heap buffer keeps it and gets a wide buffer
    for [wide_count] fl sz characters. *)
Lemma wp_glibc__IO_wfile_doallocate_heap fr fb freg fl f2 wd wreg w oe bb sz breg Φ :
  call_frame Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  0 < bb -> 0 < sz < 2 ^ 62 -> bb + sz < 2 ^ 64 -> wbuf_user_ok w f2 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗
  pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗ live bb breg -∗
  int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 (wbuf_base wd w) -∗ pcell wd 56 oe -∗ wbuf_idle w -∗ Mres -∗
  ▷ (int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗
     pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗ live bb breg -∗
     walloc_k fb freg f2 wd wreg (4 * wide_count fl sz) Φ) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hfree Hmalloc Hwsetbf.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Hbb Hsz Hbe Hu. injection Hfr as <-.
  iIntros "Hl Hfl Hnb Hne Hbl Hf2 Hw Hwl Hb He Hold HM HK".
  assert (Hend' := Hend). unfold file_size in Hend'.
  step. step. norm. check "Hl". load_pointer "Hl Hnb Hbl" by ar. iNext. iIntros "Hl Hnb Hbl".
  step. step. step. branch_as true.
  iApply (wp_wfile_doalloc_L6_heap with "Hl Hfl Hnb Hne Hbl Hf2 Hw Hwl Hb He Hold HM HK"); try libio_side.
Qed.

(** A stream that uses its one-byte short buffer keeps it and gets a
    wide buffer for one character, which is four bytes. *)
Lemma wp_glibc__IO_wfile_doallocate_short fr fb freg fl f2 wd wreg w oe Φ :
  call_frame Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 -> wbuf_user_ok w f2 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr (fb + 131) (Obj fb)) -∗
  pcell fb off_buf_end (mkPtr (fb + 132) (Obj fb)) -∗
  int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 (wbuf_base wd w) -∗ pcell wd 56 oe -∗ wbuf_idle w -∗ Mres -∗
  ▷ (int_cell fb off_flags fl -∗ pcell fb off_buf_base (mkPtr (fb + 131) (Obj fb)) -∗
     pcell fb off_buf_end (mkPtr (fb + 132) (Obj fb)) -∗ walloc_k fb freg f2 wd wreg 4 Φ) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hfree Hmalloc Hwsetbf.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Hu. injection Hfr as <-.
  iIntros "Hl Hfl Hnb Hne Hf2 Hw Hwl Hb He Hold HM HK".
  assert (Hend' := Hend). unfold file_size in Hend'.
  step. step. norm. check "Hl". iDestruct (live_halves with "Hl") as "[Hl Hl2]".
  iApply (wp_raw_load_pointer_dq with "Hl Hnb Hl2");
    [reflexivity | vx | left; reflexivity | ar | ar | cbn [ptr_addr]; lia |].
  iNext. iIntros "Hl Hnb Hl2". iDestruct (live_halves with "[$Hl $Hl2]") as "Hl".
  step. step. step. branch_as true.
  iApply (wp_wfile_doalloc_L6_short with "Hl Hfl Hnb Hne Hf2 Hw Hwl Hb He Hold HM [HK]"); try libio_side.
  rewrite wide_count_one. iExact "HK".
Qed.

(** The genv defines `c: _IO_file_doallocate`. *)
Context `{Hdaf : !Defines ge "__GI__IO_file_doallocate" Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate}.
(** A stream without a narrow buffer gets a fresh one from
    `c: _IO_file_doallocate`. That function looks up the stat function
    in the stream's jump table, and a wide stream uses the wide table.
    The proof therefore assumes the contract that
    [LibioDoAlloc](LibioDoAlloc.v) proves for a narrow stream, stated
    for the wide table. The predicate [doalloc_k] of
    [LibioDoAllocBase](LibioDoAllocBase.v) says what the caller
    receives. *)
Context (Hda_wide : forall fr fb freg fl fd eb oe vb vreg Φ,
  call_frame Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end oe -∗ pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
  Mres -∗
  ▷ (pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗ doalloc_k Mres fb freg fl fd eb Φ) -∗
  WP (ERun fr : sexpr) {{ Φ }}).

(** A stream without a narrow buffer gets both buffers. The narrow one
    is the fresh buffer of sz bytes that `c: _IO_file_doallocate`
    installs, which may also make the stream line-buffered, and the
    wide one has room for sz characters. *)
Lemma wp_glibc__IO_wfile_doallocate_null fr fb freg fl fd eb noe vb vreg f2 wd wreg w oe Φ :
  call_frame Unit_libio_wfiledoalloc_os.fn__IO_wfile_doallocate [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  0 < wd -> wd mod 8 = 0 -> wd + 232 <= r_end wreg -> r_end wreg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) -> 0 <= fd < 2 ^ 31 -> wbuf_user_ok w f2 ->
  vtables_ro ge vb vreg -∗ wvtables_ro ge vb -∗
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  pcell fb off_buf_base null -∗ pcell fb off_buf_end noe -∗
  pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
  int_cell fb off_flags2 f2 -∗ pcell fb off_wide (mkPtr wd (Obj wd)) -∗
  live wd wreg -∗ pcell wd 48 (wbuf_base wd w) -∗ pcell wd 56 oe -∗ wbuf_idle w -∗ Mres -∗
  ▷ (∀ fl1 bb sz, ⌜(fl1 = fl \/ fl1 = Z.lor fl io_line_buf) /\ 0 < sz <= 8192 /\ 0 < bb /\ bb + sz <= 2 ^ 48⌝ -∗
     pcell fb off_vtable (mkPtr (vb + vt_wfile) (Ro vb)) -∗
     int_cell fb off_flags (setb_flags fl1 1) -∗ int_cell fb off_fileno fd -∗
     pcell fb off_buf_base (mkPtr bb (Obj bb)) -∗ pcell fb off_buf_end (mkPtr (bb + sz) (Obj bb)) -∗
     new_buf bb sz -∗ errno_any eb -∗ walloc_k fb freg f2 wd wreg (4 * sz) Φ) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof using Hfree Hmalloc Hwsetbf Hdaf Hda_wide.
  intros Hfr Hfb Hal Hend Hfreg Hwd Hwal Hwend Hwreg Herrno Hfd Hfd31 Hu. injection Hfr as <-.
  iIntros "#Hvt #Hwvt Hl Hfl Hfd Herr Hnb Hne Hvtp Hf2 Hw Hwl Hb He Hold HM HK".
  assert (Hend' := Hend). unfold file_size in Hend'.
  step. step. norm. check "Hl". load_pointer "Hl Hnb [//]" by ar. iNext. iIntros "Hl Hnb _".
  step. step. step. branch.
  step. iApply wp_call_bind; [vx | exact Hdaf | reflexivity |]. iNext.
  iApply (Hda_wide _ fb freg fl fd eb noe vb vreg with "Hvt Hwvt Hl Hfl Hfd Herr Hnb Hne Hvtp HM"); try libio_side.
  iNext. iIntros "Hvtp" (fl1 bb sz Hc) "Hl Hfl Hfd Hnb Hne Hbo Herr HM".
  iExists _. iSplit; [iPureIntro; reflexivity|]. iNext. cbn [fr_fn fr_env fr_locals fr_doomed fr_at].
  step. iDestruct "Hbo" as (breg Hbr) "(Hbl & Hxs & Hcs)".
  iApply (wp_wfile_doalloc_L6_heap fb freg (setb_flags fl1 1) f2 wd wreg w oe bb sz breg
            with "Hl Hfl Hnb Hne Hbl Hf2 Hw Hwl Hb He Hold HM"); try libio_side.
  iNext. iIntros "Hfl Hnb Hne Hbl". rewrite wide_count_owned.
  iApply ("HK" $! fl1 bb sz with "[%] Hvtp Hfl Hfd Hnb Hne [Hbl Hxs Hcs] Herr"); [exact Hc|].
  iExists breg. iFrame "Hbl Hxs Hcs". iPureIntro. exact Hbr.
  Unshelve. exact freg.
Qed.

End rules.
