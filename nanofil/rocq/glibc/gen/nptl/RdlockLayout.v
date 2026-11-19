(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
From Glibc Require CapturedLayouts_1e799a8f46203a2b CapturedLayouts_7a0c7292ed5a352b.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module RdlockLayout.

Local Definition layouts : list record_layout :=
  [CapturedLayouts_7a0c7292ed5a352b.layout_structZ20__pthread_rwlock_arch_t;
   CapturedLayouts_1e799a8f46203a2b.layout_structZ20timespec;
   CapturedLayouts_7a0c7292ed5a352b.layout_typedefZ20__libc_rwlock_t;
   CapturedLayouts_7a0c7292ed5a352b.layout_typedefZ20pthread_rwlock_t].

(** Each named record has its complete size and record alignment in bytes. *)
Definition records := layout_records layouts.

(** These used tags have only forward declarations in the captured units. *)
Definition unavailable : list string := [].

(** Each field has a tag, name, byte offset, type size and type alignment. *)
Definition fields := layout_fields layouts.

(** The lookup returns [None] if the fixture has no matching field. *)
Definition field_offset := layout_field_offset fields.

End RdlockLayout.
