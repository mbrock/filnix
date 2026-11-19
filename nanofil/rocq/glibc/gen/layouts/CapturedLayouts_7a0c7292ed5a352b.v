(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_structZ20__pthread_rwlock_arch_t : record_layout :=
  (mkRecordLayout "struct __pthread_rwlock_arch_t" 56 8 [("__readers", 0, 4, 4); ("__writers", 4, 4, 4); ("__wrphase_futex", 8, 4, 4); ("__writers_futex", 12, 4, 4); ("__pad3", 16, 4, 4); ("__pad4", 20, 4, 4); ("__cur_writer", 24, 4, 4); ("__shared", 28, 4, 4); ("__pad1", 32, 8, 8); ("__pad2", 40, 8, 8); ("__flags", 48, 4, 4)]).

Definition layout_typedefZ20__libc_rwlock_t : record_layout :=
  (mkRecordLayout "typedef __libc_rwlock_t" 56 8 [("__data", 0, 56, 8); ("__size", 0, 56, 1); ("__align", 0, 8, 8)]).

Definition layout_typedefZ20pthread_rwlock_t : record_layout :=
  (mkRecordLayout "typedef pthread_rwlock_t" 56 8 [("__data", 0, 56, 8); ("__size", 0, 56, 1); ("__align", 0, 8, 8)]).
