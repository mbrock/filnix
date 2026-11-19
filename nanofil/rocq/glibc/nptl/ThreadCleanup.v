(** Glibc records the active cleanup handler in the thread descriptor.
    The cleanup and stack-allocation proofs share ownership of its fields. *)

From iris.base_logic.lib Require Import gen_heap.
From Stdlib Require Import String ZArith.
From Nanofil Require Import Values Memory Pieces Heap.
From Glibc Require Import Fix OsMemLogic SysLayout LayoutTables GlibcTactics.
Import Fix.LG0 Fix.ML0.
Open Scope Z_scope.

Definition off_cleanup : Z := ltac:(layout_constant (SysLayout.field_offset "struct pthread" "cleanup")).
#[export] Hint Unfold off_cleanup : offs.
Definition off_cleanup_jmp : Z := ltac:(layout_constant (SysLayout.field_offset "struct pthread" "cleanup_jmp_buf")).
#[export] Hint Unfold off_cleanup_jmp : offs.
Definition off_cancelhandling : Z := ltac:(layout_constant (SysLayout.field_offset "struct pthread" "cancelhandling")).
#[export] Hint Unfold off_cancelhandling : offs.

Section cleanup.
Context `{!gen_heapGS piece pval Σ}.

(** [tcb_cleanup_inv] self: the calling thread's cookie self, not
    null, is the object tb's own pointer; the thread owns tb's life and
    the fields the cleanup calls touch: `c: cleanup` null, as it is
    outside a push and pop, `c: cleanup_jmp_buf`, and
    `c: cancelhandling` 0, so `c: (cancelhandling & CANCELTYPE_BITMASK)
    == 0` and neither a CAS nor `c: __pthread_unwind` is reached. *)
Definition tcb_cleanup_inv (self : ptr) : iProp Σ :=
  ∃ tb treg jb, ⌜self = mkPtr tb (Obj tb) /\ 0 < tb /\ tb mod 8 = 0 /\
                 tb + off_cancelhandling + 4 <= r_end treg /\ r_end treg <= 2 ^ 63⌝ ∗
    live tb treg ∗ pcell tb off_cleanup null ∗ pcell tb off_cleanup_jmp jb ∗
    int_cell tb off_cancelhandling 0.

(** [tcb_pushed] self buf: the same, inside a push of the cleanup
    buffer buf, which `c: cleanup` then points at. *)
Definition tcb_pushed (self buf : ptr) : iProp Σ :=
  ∃ tb treg jb, ⌜self = mkPtr tb (Obj tb) /\ 0 < tb /\ tb mod 8 = 0 /\
                 tb + off_cancelhandling + 4 <= r_end treg /\ r_end treg <= 2 ^ 63⌝ ∗
    live tb treg ∗ pcell tb off_cleanup buf ∗ pcell tb off_cleanup_jmp jb ∗
    int_cell tb off_cancelhandling 0.

End cleanup.
