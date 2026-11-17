(** After the cookie names the thread object, glibc calls
    `c: __tls_init_tp` to fill in the object's own fields. Its caller,
    `c: __libc_setup_tls`, needs only what the call writes, so this
    module states that contract together with the thread object's
    layout. [StartTlsInitTp](StartTlsInitTp.v) proves the contract. *)

From Glibc Require Import GlibcProgram GlibcSpec.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap fancy_updates.
From Stdlib Require Import String ZArith List Lia.
From Nanofil Require Import Term Syntax Values Memory Semantics Pieces Heap Runtime Logic MemLogic.
From Glibc Require Import FileInv OsStart StartLogic.
Import ListNotations ProgramAbbreviations FileInv.ML FileInv.LG FileInv.L.
Open Scope Z_scope.

(** ## The thread object

    The thread object has many fields, but a proof needs only those that
    startup writes or that `c: main` reads. The layout below picks them
    out of the zeroed object. The two assertions after it describe those
    fields before and after `c: __tls_init_tp` runs. *)

(** This layout splits the 2496-byte thread object into zero fields. It
    names the two self pointers at 0 and 16, the fields that
    `c: __tls_init_tp` writes, the cleanup pointers at 776 and 784, and
    `c: cancelhandling` at 792. *)
Definition tcb_layout : list field :=
  [FPtr; FPad 8; FPtr; FPad 696; FInt; FPad 4; FPtr; FInt; FPad 4; FPtr; FPtr; FLong; FPad 8; FPtr; FPtr;
   FInt; FPad 516; FPtr; FPad 249; FByte; FPad 2; FInt; FPad 16; FInt; FPad 124; FLong; FPad 768].

Section fields.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.

(** This assertion owns the fields that `c: __tls_init_tp` writes, while
    they are all zero. *)
Definition tp_zero (tb : Z) : iProp Σ :=
  bytes tb 720 [0; 0; 0; 0] ∗ pcell tb 728 null ∗ bytes tb 736 [0; 0; 0; 0] ∗
  pcell tb 744 null ∗ pcell tb 752 null ∗ icell tb 760 0 ∗ pcell tb 1312 null ∗
  ibyte tb 1569 0 ∗ bytes tb 1572 [0; 0; 0; 0] ∗ bytes tb 1592 [0; 0; 0; 0] ∗ icell tb 1720 0.

(** This assertion owns the same fields after `c: __tls_init_tp` has
    written them. Four values vary from run to run: the kernel thread id
    t, the runtime thread address a, the report-events byte x and the
    saved stack end sp. *)
Definition tp_fields (tb t a x : Z) (sp : ptr) : iProp Σ :=
  bytes tb 720 (le_bytes t 4) ∗ pcell tb 728 (mkPtr a CNone) ∗ bytes tb 736 (le_bytes 0 4) ∗
  pcell tb 744 (mkPtr (tb + 752) (Obj tb)) ∗ pcell tb 752 (mkPtr (tb + 752) (Obj tb)) ∗
  icell tb 760 18446744073709551584 ∗ pcell tb 1312 (mkPtr (tb + 800) (Obj tb)) ∗
  ibyte tb 1569 x ∗ bytes tb 1572 (le_bytes 2 4) ∗ bytes tb 1592 (le_bytes 2 4) ∗ icell tb 1720 (ptr_addr sp).

(** Startup allocates the thread object zeroed, so every field it later
    writes starts at zero. A fresh 2496-byte object splits into its
    lifetime and those zero fields. *)
Lemma tcb_fresh tb :
  obj tb (heap_req 16 2496) ⊢
  live tb (mkRegion tb (tb + 2496) Heap Live) ∗ pcell tb 0 null ∗ pcell tb 16 null ∗ tp_zero tb ∗
  pcell tb 776 null ∗ pcell tb 784 null ∗ bytes tb 792 [0; 0; 0; 0].
Proof using Type.
  rewrite obj_zero_block; [|vm_compute; congruence].
  change (req_extent (heap_req 16 2496)) with 2496. change (req_kind (heap_req 16 2496)) with Heap.
  change (Z.to_nat 2496) with (layout_len tcb_layout).
  iIntros "[$ H]". iDestruct (zero_layout with "H") as "H". cbn [layout_own field_own field_len tcb_layout].
  iEval (simpl) in "H".
  iDestruct "H" as "(H0 & _ & H16 & _ & H720 & _ & H728 & H736 & _ & H744 & H752 & H760 & _ & H776 & H784 &
    H792 & _ & H1312 & _ & H1569 & _ & H1572 & _ & H1592 & _ & H1720 & _)".
  iSplitL "H0"; [iExact "H0"|]. iSplitL "H16"; [iExact "H16"|].
  iSplitR "H776 H784 H792"; [|iSplitL "H776"; [iExact "H776"|]; iSplitL "H784"; [iExact "H784" | iExact "H792"]].
  rewrite /tp_zero. iSplitL "H720"; [iExact "H720"|]. iSplitL "H728"; [iExact "H728"|].
  iSplitL "H736"; [iExact "H736"|]. iSplitL "H744"; [iExact "H744"|]. iSplitL "H752"; [iExact "H752"|].
  iSplitL "H760"; [iExact "H760"|]. iSplitL "H1312"; [iExact "H1312"|]. iSplitL "H1569"; [iExact "H1569"|].
  iSplitL "H1572"; [iExact "H1572"|]. iSplitL "H1592"; [iExact "H1592" | iExact "H1720"].
Qed.

End fields.

(** ## The contract

    The function reads the cookie, so its contract depends on which
    object the cookie names. The definition below therefore takes that
    object tb as a parameter. Each proof that uses it must show that the
    world's cookie is tb. *)

Section spec.
Context `{!invGS_gen hlc Σ, !gen_heapGS piece pval Σ}.
Context (ge : genv) (tb : Z).

(** A call of `c: __tls_init_tp()` fills in the zero fields of the
    thread object tb for some nonzero thread id t and thread handle a.
    It only reads the report-events byte x and the saved stack end sp,
    and it gives both back. *)
Definition tls_init_tp_spec : fspec Σ :=
  FSpec (region * Z * region * Z * Z * region * ptr * region) (fun _ => [])
    (fun '(treg, re, rereg, x, se, sereg, sp, spreg) =>
       ⌜lookup (TAtom "__nptl_initial_report_events") (ge_globals ge) = Some (mkPtr re (Obj re)) /\
        lookup (TAtom "__libc_stack_end") (ge_globals ge) = Some (mkPtr se (Obj se)) /\
        re + 1 <= r_end rereg /\ se mod 8 = 0 /\ se + 8 <= r_end sereg /\ 0 <= x < 256 /\
        0 <= ptr_addr sp < 2 ^ 64 /\ 0 < tb /\ tb mod 16 = 0 /\ tb + 2496 <= r_end treg <= 2 ^ 63⌝ ∗
       live tb treg ∗ tp_zero tb ∗ live re rereg ∗ ibyte re 0 x ∗ live se sereg ∗ pcell se 0 sp ∗
       live_cap (ptr_cap sp) spreg)%I
    (fun '(treg, re, rereg, x, se, sereg, sp, spreg) o =>
       ⌜o = RetVoid⌝ ∗ ∃ t a, ⌜0 < t < 2 ^ 32 /\ 0 < a < 2 ^ 64⌝ ∗
       live tb treg ∗ tp_fields tb t a x sp ∗ live re rereg ∗ ibyte re 0 x ∗ live se sereg ∗
       pcell se 0 sp ∗ live_cap (ptr_cap sp) spreg)%I.

End spec.
