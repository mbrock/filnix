(** Stream callers use these contracts for the system-call wrappers they invoke.
    Each named contract returns the caller's memory and records the possible
    result, without exposing the callee's entry frame. *)

From Glibc Require Import GlibcProgram GlibcSpec OsBlocks OsFstat.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
From iris.program_logic Require Import language weakestpre.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap ExternalCalls Runtime Logic.
Import Fix.LG0 Fix.LG0.L ListNotations ProgramAbbreviations.
Open Scope Z_scope.

Section rules.
Context `{glibc_program : !GlibcProgram (hlc := hlc) Σ}.

(** The major device number joins the low and high fields of the device identifier. *)
Definition dev_major (d : Z) : Z :=
  Z.lor (Z.land d 1048320 / 2 ^ 8) (Z.land d 18446726481523507200 / 2 ^ 32) mod 2 ^ 32.

(** The device query returns the major number without changing memory. *)
Definition major_spec : fspec Σ :=
  FSpec Z (fun d => [WInt d]) (fun d => ⌜0 <= d < 2 ^ 64⌝)%I
    (fun d v => ⌜v = Ret (WInt (dev_major d))⌝)%I.

(** Closing a descriptor preserves errno ownership and returns zero or minus one. *)
Definition close_spec : fspec Σ :=
  FSpec (Z * Z) (fun '(fd, _) => [WInt fd])
    (fun '(fd, eb) => ⌜0 <= fd < 2 ^ 32 /\ ow_errno w0 = Some (mkPtr eb (Obj eb))⌝ ∗
      errno_any eb)%I
    (fun '(_, eb) v => ∃ k, ⌜v = Ret (WInt k) /\ (k = 0 \/ k = 2 ^ 32 - 1)⌝ ∗
      errno_any eb)%I.

(** The terminal query preserves errno ownership and returns a Boolean integer. *)
Definition isatty_spec : fspec Σ :=
  FSpec (Z * Z) (fun '(fd, _) => [WInt fd])
    (fun '(fd, eb) => ⌜0 <= fd < 2 ^ 32 /\ ow_errno w0 = Some (mkPtr eb (Obj eb)) /\
      In fd (ow_fds w0)⌝ ∗ errno_any eb)%I
    (fun '(_, eb) v => ∃ k, ⌜v = Ret (WInt k) /\ (k = 0 \/ k = 1)⌝ ∗
      errno_any eb)%I.

(** A stat query returns ownership of the buffer with the bytes the kernel left. *)
Definition fstat_spec : fspec Σ :=
  FSpec (Z * Z * region * Z * Z)
    (fun '(fd, b, _, o, _) => [WInt fd; WPtr (mkPtr (b + o) (Obj b))])
    (fun '(fd, b, reg, o, eb) =>
      ⌜0 <= fd < 2 ^ 32 /\ ow_errno w0 = Some (mkPtr eb (Obj eb)) /\ In fd (ow_fds w0) /\
        0 <= o /\ b + o + stat_size <= r_end reg⌝ ∗
      live b reg ∗ blk_any b o stat_size ∗ errno_any eb)%I
    (fun '(_, b, reg, o, eb) v => ∃ k,
      ⌜v = Ret (WInt k) /\ (k = 0 \/ k = 2 ^ 32 - 1)⌝ ∗
      live b reg ∗ blk_any b o stat_size ∗ errno_any eb)%I.

End rules.
