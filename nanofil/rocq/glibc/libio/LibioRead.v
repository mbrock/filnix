(** Triples for user glibc's narrow stream readers and the jump-table
    entries that wrap a syscall (LibioReadCode.v): `c: __fpending`,
    `c: _IO_ferror`, `c: _IO_file_stat` and `c: _IO_file_close`.

    Each is stated over the fields of FileInv.v's layout it touches,
    the stream's life owned whole, as the checks need: a caller opens
    them from [file_inv]. A narrow stream's mode is 0 or -1
    ([mode_vtable]), so `c: __fpending` takes its narrow branch, and
    its `c: _flags2` has `c: _IO_FLAGS2_NEED_LOCK` clear ([flags_ok]),
    so `c: _IO_ferror` reads the flags without taking the lock. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Runtime Ops Semantics Run Machine
  ExternalCalls ExternalMachine Pieces StepRules Heap ContractFrame Language Logic StringLogic MemLogic.
From Glibc Require Import OsBlocks OsWorld OsFstat OsRegistry SysCode LibioReadCode FileInv LibioLogic
  SysWrappers.
Import ListNotations.
Open Scope Z_scope.

(** Integer arithmetic stays folded on an unknown under [cbn]
    (Symbolic.v's decisions): on numbers it computes. *)
Local Arguments Z.add : simpl nomatch.
Local Arguments Z.sub : simpl nomatch.
Local Arguments Z.mul : simpl nomatch.
Local Arguments Z.opp : simpl nomatch.

(** The triples over the [[runtime]] R and [LogicSig] LG0. *)
Module LibioReadOn (R : Runtime) (LG0 : LogicSig R).
Module SW := SysWrappersOn R LG0.
Import SW SW.FI.ML SW.FI.LG SW.FI.L SW.OW SW.FI SW.ST.

Section rules.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (w0 : os_world) (registry : name -> option (contract os_world)) (ge : genv).
Context (Hreg : holds_os registry) (Hext : sys_external ge).

(** The Iris instance for registry and [os_wi] w0. *)
Local Instance read_irisGS : irisGS_gen hlc (nanofil_lang registry ge) Σ :=
  nanofil_irisGS registry (os_wi w0) ge.

(** Expressions of the language. *)
Local Notation sexpr := (language.expr (nanofil_lang registry ge)).

(** A signed 32-bit load of an owned [int_cell] at offset o of b, read
    through the proven pointer the frame holds. *)
Ltac load_int H :=
  iApply (wp_raw_load_sub_bytes_dq with H);
    [reflexivity | reflexivity | reflexivity | apply load_sw_int; assumption | left; reflexivity | ar |];
  iNext; iIntros H.

(** ## `c: __fpending` *)

(** `c: __fpending(fp)` of a narrow stream (mode 0 or -1): the bytes
    between `c: _IO_write_base` and `c: _IO_write_ptr`, which share a
    capability, the buffer's or none. *)
Lemma wp_glibc___fpending fr fb freg mode wp wb reg' Φ :
  call_frame glibc___fpending [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  (mode = 0 \/ mode = 2 ^ 32 - 1) -> ptr_cap wp = ptr_cap wb ->
  0 <= ptr_addr wp < 2 ^ 64 -> 0 <= ptr_addr wb < 2 ^ 64 ->
  live fb freg -∗ int_cell fb off_mode mode -∗ pcell fb off_write_ptr wp -∗ pcell fb off_write_base wb -∗
  live_cap (ptr_cap wp) reg' -∗
  ▷ (live fb freg -∗ int_cell fb off_mode mode -∗ pcell fb off_write_ptr wp -∗ pcell fb off_write_base wb -∗
     live_cap (ptr_cap wp) reg' -∗ Φ (Ret (WInt ((ptr_addr wp - ptr_addr wb) mod 2 ^ 64)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg Hmode Hcap Hwp Hwb. injection Hfr as <-.
  iIntros "Hl [%Hm Hmode] Hwp Hwb Hc HK". unfold file_size in Hend. enter. st. norm. chk "Hl".
  load_int "Hl Hmode". st.
  destruct Hmode as [-> | ->]; closed_ints. 1: br. 2: br.
  all: st; st; norm; chk "Hl";
    (iApply (wp_raw_load_pointer with "Hl Hwp Hc");
       [reflexivity | reflexivity | reflexivity | ar | ar | exact Hwp |]);
    iNext; iIntros "Hl Hwp Hc"; st; norm; chk "Hl"; rewrite Hcap;
    (iApply (wp_raw_load_pointer with "Hl Hwb Hc");
       [reflexivity | reflexivity | reflexivity | ar | ar | exact Hwb |]);
    iNext; iIntros "Hl Hwb Hc"; st; st; st; rewrite -Hcap;
    (iApply wp_ret; [reflexivity | reflexivity |]); iNext; cbn;
    rewrite (Z.mod_small (ptr_addr wp)); try lia; rewrite (Z.mod_small (ptr_addr wb)); try lia;
    rewrite Z.mod_mod; [|lia]; iApply ("HK" with "Hl [Hmode] Hwp Hwb Hc"); (iSplit; [iPureIntro; lia | iExact "Hmode"]).
Qed.

(** ## `c: _IO_ferror` *)

(** `c: _IO_ferror(fp)` of a stream whose `c: _flags2` has
    `c: _IO_FLAGS2_NEED_LOCK` clear: the lock macros skip the lock,
    and the result is `c: _IO_ERR_SEEN` of `c: _flags`, 1 or 0. *)
Lemma wp_glibc__IO_ferror fr fb freg fl f2 Φ :
  call_frame glibc__IO_ferror [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  Z.land f2 io_need_lock = 0 ->
  live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗
  ▷ (live fb freg -∗ int_cell fb off_flags fl -∗ int_cell fb off_flags2 f2 -∗
     Φ (Ret (WInt (if Z.land fl io_err_seen =? 0 then 0 else 1)))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfb Hal Hend Hfreg Hnl. injection Hfr as <-.
  iIntros "Hl [%Hf Hfl] [%Hf2 Hfl2] HK". unfold file_size in Hend. enter. st. norm. chk "Hl".
  load_int "Hl Hfl2". st. st. st. st.
  rewrite flags2_bit7; [|exact Hf2]. unfold io_need_lock in Hnl. rewrite Hnl. br. st. chk "Hl".
  load_int "Hl Hfl". st. st. iApply wp_ret; [reflexivity | reflexivity |]. iNext.
  change (32 mod 2 ^ 32) with 32. change (0 mod 2 ^ 32) with 0. rewrite (Z.mod_small fl); [|lia].
  assert (Hb : 0 <= Z.land fl 32 < 2 ^ 32).
  { apply land_lt32; lia. }
  rewrite (Z.mod_small (Z.land fl 32)); [|exact Hb]. unfold io_err_seen.
  destruct (Z.land fl 32 =? 0); cbn [negb];
    (iApply ("HK" with "Hl [Hfl] [Hfl2]"); [iSplit; [done | iExact "Hfl"] | iSplit; [done | iExact "Hfl2"]]).
Qed.

(** ## `c: _IO_file_close` and `c: _IO_file_stat` *)

(** A call of a wrapper of SysWrappers.v from a frame, through
    [wp_call_bind]: its triple's postcondition resumes the caller. *)
Ltac resume_ret := iExists _; iSplit; [iPureIntro; reflexivity|]; iNext.

(** `c: _IO_file_close(fp)`: `c: __close_nocancel(fp->_fileno)`, 0 or
    `c: -1`, errno left as the call left it. *)
Lemma wp_glibc__IO_file_close fr fb freg fd eb Φ :
  call_frame glibc__IO_file_close [WPtr (mkPtr fb (Obj fb))] = Some fr ->
  find_fn ge (TAtom "__GI___close_nocancel") = Some (Defined glibc___close_nocancel) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) ->
  live fb freg -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live fb freg -∗ int_cell fb off_fileno fd -∗ errno_any eb -∗
     Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfn Hfb Hal Hend Hfreg He. injection Hfr as <-.
  iIntros "Hl [%Hfd Hfdb] Herr HK". unfold file_size in Hend. enter. st. norm. chk "Hl".
  load_int "Hl Hfdb".
  iApply wp_call_bind; [reflexivity | exact Hfn | reflexivity |]. iNext.
  iApply (wp_glibc___close_nocancel w0 registry ge Hreg Hext with "Herr"); [reflexivity | apply Z.mod_pos_bound; lia | exact He |].
  iNext. iIntros (k Hk) "Herr". resume_ret.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. rewrite Z.mod_mod; [|lia]. rewrite Z.mod_small; [|lia].
  iApply ("HK" with "[%] Hl [Hfdb] Herr"); [exact Hk | iSplit; [done | iExact "Hfdb"]].
Qed.

(** `c: _IO_file_stat(fp, st)`: `c: __fstat64(fp->_fileno, st)`, 0 or
    `c: -1`, the 144 bytes at st holding whatever the kernel left. *)
Lemma wp_glibc__IO_file_stat fr fb freg fd b reg o eb Φ :
  call_frame glibc__IO_file_stat [WPtr (mkPtr fb (Obj fb)); WPtr (mkPtr (b + o) (Obj b))] = Some fr ->
  find_fn ge (TAtom "__GI___fstat64") = Some (Defined glibc___fstat64) ->
  0 < fb -> fb mod 8 = 0 -> fb + file_size <= r_end freg -> r_end freg <= 2 ^ 63 ->
  ow_errno w0 = Some (mkPtr eb (Obj eb)) -> In fd (ow_fds w0) ->
  0 <= o -> b + o + stat_size <= r_end reg ->
  live fb freg -∗ int_cell fb off_fileno fd -∗ live b reg -∗ blk_any b o stat_size -∗ errno_any eb -∗
  ▷ (∀ k, ⌜k = 0 \/ k = 2 ^ 32 - 1⌝ -∗ live fb freg -∗ int_cell fb off_fileno fd -∗ live b reg -∗
     blk_any b o stat_size -∗ errno_any eb -∗ Φ (Ret (WInt k))) -∗
  WP (ERun fr : sexpr) {{ Φ }}.
Proof.
  intros Hfr Hfn Hfb Hal Hend Hfreg He Hin Ho Hst. injection Hfr as <-.
  iIntros "Hl [%Hfd Hfdb] Hbl Hb Herr HK". unfold file_size in Hend. enter. st. norm. chk "Hl".
  load_int "Hl Hfdb".
  iApply wp_call_bind; [reflexivity | exact Hfn | reflexivity |]. iNext.
  iApply (wp_glibc___fstat64 w0 registry ge Hreg Hext with "Hbl Hb Herr");
    [reflexivity | apply Z.mod_pos_bound; lia | exact He | rewrite Z.mod_small; [exact Hin | lia] | exact Ho | exact Hst |].
  iNext. iIntros (k Hk) "Hbl Hb Herr". resume_ret.
  iApply wp_ret; [reflexivity | reflexivity |]. iNext. rewrite Z.mod_mod; [|lia]. rewrite Z.mod_small; [|lia].
  iApply ("HK" with "[%] Hl [Hfdb] Hbl Hb Herr"); [exact Hk | iSplit; [done | iExact "Hfdb"]].
Qed.

End rules.
End LibioReadOn.
