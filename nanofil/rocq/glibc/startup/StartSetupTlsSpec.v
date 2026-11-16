(** `c: __libc_setup_tls` gives the main thread its thread object and
    makes that object the runtime's cookie, which the proofs of
    `c: main` read as [ow_self]. Its caller, `c: __libc_start_main`,
    needs only the object it ends with, so this module states that
    contract. [StartSetupTls](StartSetupTls.v) proves it.

    ## How the contract follows the world

    Setting the cookie changes the OS world in the middle of the call,
    so no single fixed world describes the whole call. The contract
    therefore reads the world through a ghost key k. The key holds the
    cookie and both handler flags, and the call hands it back with the
    new cookie. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv OsStart StartLogic StartTlsInitTpSpec.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

Section spec.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (ge : genv) (k : Z).

(** A call of `c: __libc_setup_tls()` starts with no handler registered
    and any cookie c. It ends with a fresh 2496-byte thread object tb as
    the cookie. The object's self fields name it, `c: __tls_init_tp` has
    filled in its fields, and its cleanup fields and `c: cancelhandling`
    are still zero. *)
Definition setup_tls_spec : fspec Σ :=
  FSpec (ptr * Z * region * Z * Z * region * ptr * region) (fun _ => [])
    (fun '(c, re, rereg, x, se, sereg, sp, spreg) =>
       ⌜lookup (TAtom "__nptl_initial_report_events") (ge_globals ge) = Some (mkPtr re (Obj re)) /\
        lookup (TAtom "__libc_stack_end") (ge_globals ge) = Some (mkPtr se (Obj se)) /\
        re + 1 <= r_end rereg /\ se mod 8 = 0 /\ se + 8 <= r_end sereg /\ 0 <= x < 256 /\
        0 <= ptr_addr sp < 2 ^ 64⌝ ∗
       pointsto (PName k) (DfracOwn 1) (start_ghost c false false) ∗
       live re rereg ∗ ibyte re 0 x ∗ live se sereg ∗ pcell se 0 sp ∗ live_cap (ptr_cap sp) spreg)%I
    (fun '(c, re, rereg, x, se, sereg, sp, spreg) o =>
       ⌜o = RetVoid⌝ ∗ ∃ tb t a,
       ⌜0 < tb /\ tb mod 16 = 0 /\ tb + 2496 <= 2 ^ 48 /\ 0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ ∗
       pointsto (PName k) (DfracOwn 1) (start_ghost (mkPtr tb (Obj tb)) false false) ∗
       live tb (mkRegion tb (tb + 2496) Heap Live) ∗
       pcell tb 0 (mkPtr tb (Obj tb)) ∗ pcell tb 16 (mkPtr tb (Obj tb)) ∗ tp_fields tb t a x sp ∗
       pcell tb 776 null ∗ pcell tb 784 null ∗ bytes tb 792 [0; 0; 0; 0] ∗
       live re rereg ∗ ibyte re 0 x ∗ live se sereg ∗ pcell se 0 sp ∗ live_cap (ptr_cap sp) spreg)%I.

End spec.
