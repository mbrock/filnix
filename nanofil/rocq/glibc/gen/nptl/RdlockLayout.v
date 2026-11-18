(** These tables record the C layouts used by this fixture's functions.
    The compiler supplies field offsets, sizes and type alignments from its completed layouts.
    Offset checks compare hand-written constants against these tables without changing existing proofs.
    Layouts remain advisory data, not premises of soundness theorems.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String ZArith List.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module RdlockLayout.

(** Each named record has its complete size and record alignment in bytes. *)
Definition records : list (string * (Z * Z)) :=
  [("struct __pthread_rwlock_arch_t", (56, 8)); ("struct timespec", (16, 8)); ("typedef __libc_rwlock_t", (56, 8)); ("typedef pthread_rwlock_t", (56, 8))].

(** These used tags have only forward declarations in the captured units. *)
Definition unavailable : list string := [].

(** Each field has a tag, name, byte offset, type size and type alignment.
    Flexible arrays have zero size; bit-fields retain their declared type's size and alignment. *)
Definition fields : list (string * string * Z * Z * Z) :=
  [("struct __pthread_rwlock_arch_t", "__readers", 0, 4, 4); ("struct __pthread_rwlock_arch_t", "__writers", 4, 4, 4); ("struct __pthread_rwlock_arch_t", "__wrphase_futex", 8, 4, 4); ("struct __pthread_rwlock_arch_t", "__writers_futex", 12, 4, 4); ("struct __pthread_rwlock_arch_t", "__pad3", 16, 4, 4); ("struct __pthread_rwlock_arch_t", "__pad4", 20, 4, 4); ("struct __pthread_rwlock_arch_t", "__cur_writer", 24, 4, 4); ("struct __pthread_rwlock_arch_t", "__shared", 28, 4, 4); ("struct __pthread_rwlock_arch_t", "__pad1", 32, 8, 8); ("struct __pthread_rwlock_arch_t", "__pad2", 40, 8, 8); ("struct __pthread_rwlock_arch_t", "__flags", 48, 4, 4); ("struct timespec", "tv_sec", 0, 8, 8); ("struct timespec", "tv_nsec", 8, 8, 8); ("typedef __libc_rwlock_t", "__data", 0, 56, 8); ("typedef __libc_rwlock_t", "__size", 0, 56, 1); ("typedef __libc_rwlock_t", "__align", 0, 8, 8); ("typedef pthread_rwlock_t", "__data", 0, 56, 8); ("typedef pthread_rwlock_t", "__size", 0, 56, 1); ("typedef pthread_rwlock_t", "__align", 0, 8, 8)].

(** Missing fields return [None], so an offset check cannot accept an invented entry. *)
Definition field_offset (tag field : string) : option Z :=
  option_map (fun entry => let '(_, _, offset, _, _) := entry in offset)
    (find (fun entry => let '(t, f, _, _, _) := entry in
      andb (String.eqb t tag) (String.eqb f field)) fields).

End RdlockLayout.
