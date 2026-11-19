(** Multiple fixtures use these captured C layouts.
    Each fixture refers to the records that its functions use.
    The code generator reproduces this file from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List.
From Glibc Require Import LayoutTables.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Definition layout_glibc_genopsZ3aanonymousZ20structZ23170 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous struct#170" 32 8 [("exception_class", 0, 8, 8); ("exception_cleanup", 8, 8, 8); ("private_1", 16, 8, 8); ("private_2", 24, 8, 8)]).

Definition layout_glibc_genopsZ3aanonymousZ20structZ23212 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous struct#212" 8 4 [("addr", 0, 4, 4); ("mask", 4, 4, 4)]).

Definition layout_glibc_genopsZ3aanonymousZ20structZ23214 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous struct#214" 56 8 [("nscount", 0, 2, 2); ("nsmap", 2, 6, 2); ("nssocks", 8, 12, 4); ("nscount6", 20, 2, 2); ("nsinit", 22, 2, 2); ("nsaddrs", 24, 24, 8); ("__glibc_extension_index", 48, 8, 8)]).

Definition layout_glibc_genopsZ3aanonymousZ20structZ23217 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous struct#217" 72 8 [("jmp_buf", 0, 64, 8); ("mask_was_saved", 64, 4, 4)]).

Definition layout_glibc_genopsZ3aanonymousZ20structZ23219 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous struct#219" 24 8 [("prev", 0, 8, 8); ("cleanup", 8, 8, 8); ("canceltype", 16, 4, 4)]).

Definition layout_glibc_genopsZ3aanonymousZ20unionZ23169 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous union#169" 32 16 [("unwind_exception_align", 0, 16, 8); ("exception_class", 0, 8, 8); ("exception_cleanup", 8, 8, 8); ("private_1", 16, 8, 8); ("private_2", 24, 8, 8)]).

Definition layout_glibc_genopsZ3aanonymousZ20unionZ23200 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous union#200" 16 4 [("__u6_addr8", 0, 16, 1); ("__u6_addr16", 0, 16, 2); ("__u6_addr32", 0, 16, 4)]).

Definition layout_glibc_genopsZ3aanonymousZ20unionZ23213 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous union#213" 56 8 [("pad", 0, 52, 1); ("_ext", 0, 56, 8)]).

Definition layout_glibc_genopsZ3aanonymousZ20unionZ23218 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous union#218" 32 8 [("pad", 0, 32, 8); ("data", 0, 24, 8)]).

Definition layout_glibc_genopsZ3aanonymousZ20unionZ23224 : record_layout :=
  (mkRecordLayout "glibc_genops:anonymous union#224" 704 32 [("header", 0, 704, 32); ("__padding", 0, 192, 8)]).
