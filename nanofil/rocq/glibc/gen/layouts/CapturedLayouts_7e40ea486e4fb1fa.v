(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_structZ20stat64 : record_layout :=
  (mkRecordLayout "struct stat64" 144 8 [("st_dev", 0, 8, 8); ("st_ino", 8, 8, 8); ("st_nlink", 16, 8, 8); ("st_mode", 24, 4, 4); ("st_uid", 28, 4, 4); ("st_gid", 32, 4, 4); ("__pad0", 36, 4, 4); ("st_rdev", 40, 8, 8); ("st_size", 48, 8, 8); ("st_blksize", 56, 8, 8); ("st_blocks", 64, 8, 8); ("st_atim", 72, 16, 8); ("st_mtim", 88, 16, 8); ("st_ctim", 104, 16, 8); ("__glibc_reserved", 120, 24, 8)]).
