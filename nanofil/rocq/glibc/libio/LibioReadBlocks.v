(** An executor needs to know which values and memory regions a block may use.
    These tables list live temporaries and explicit memory accesses to guide that choice.
    Wrong hints can stop execution, but they cannot justify a memory access.
    No soundness theorem may assume that these tables are correct.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


From Glibc Require Import LibioReadSrc.
Module LibioReadBlocks.

Module fn___fpending.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L3"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L2"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (5%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (32))); (6%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (9%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (24)))]); ((TAtom "L3"), [(2%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (40))); (5%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (32)))])].

End fn___fpending.

Module fn__IO_ferror.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L6"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L84"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L85"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L124"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L125"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L147"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L168"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163")]); ((TAtom "L169"), [(TAtom "v113"); (TAtom "v163"); (TAtom "v170")]); ((TAtom "L180"), [(TAtom "v113"); (TAtom "v163")]); ((TAtom "L148"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L116"), [(TAtom "v113")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L6"), []); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v49")]); ((TAtom "L41"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L35"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L60"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L84"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75"); (TAtom "v82")]); ((TAtom "L85"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33"); (TAtom "v75")]); ((TAtom "L89"), [(TAtom "chk0"); (TAtom "chk10"); (TAtom "chk2"); (TAtom "v0"); (TAtom "v33")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L61"), [(TAtom "chk0"); (TAtom "chk2"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L130"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113"); (TAtom "v137")]); ((TAtom "L131"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L124"), [(TAtom "v113")]); ((TAtom "L125"), [(TAtom "chk28"); (TAtom "v0"); (TAtom "v113")]); ((TAtom "L147"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163"); (TAtom "v167")]); ((TAtom "L168"), [(TAtom "chk33"); (TAtom "v113"); (TAtom "v163"); (TAtom "v170"); (TAtom "v171")]); ((TAtom "L169"), [(TAtom "v113"); (TAtom "v163")]); ((TAtom "L180"), [(TAtom "v113")]); ((TAtom "L148"), [(TAtom "v113")]); ((TAtom "L116"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v10")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)))]); ((TAtom "L6"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L29"), [(3%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 1), true, false, (Some (TAtom "v37")), (Some (0)))]); ((TAtom "L40"), [(2%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), true, false, (Some (TAtom "v44")), (Some (8)))]); ((TAtom "L41"), []); ((TAtom "L34"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v54")]), (0), (Some 4), false, true, (Some (TAtom "v54")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), false, true, (Some (TAtom "v57")), (Some (8)))]); ((TAtom "L35"), [(2%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 8), true, false, (Some (TAtom "v65")), (Some (8)))]); ((TAtom "L60"), [(1%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (3%N, (TApp "tmp" [(TAtom "v75")]), (0), (Some 4), true, true, (Some (TAtom "v75")), (Some (0)))]); ((TAtom "L84"), []); ((TAtom "L85"), []); ((TAtom "L89"), []); ((TAtom "L78"), [(2%N, (TApp "tmp" [(TAtom "v100")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v102")]), (0), (Some 8), false, true, (Some (TAtom "v101")), (Some (8)))]); ((TAtom "L61"), [(1%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 4), true, false, (Some (TAtom "v106")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v107")]), (0), (Some 4), false, true, (Some (TAtom "v106")), (Some (4)))]); ((TAtom "L24"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L121"), [(2%N, (TApp "tmp" [(TAtom "v127")]), (0), (Some 1), true, false, (Some (TAtom "v127")), (Some (0)))]); ((TAtom "L130"), [(2%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v135")]), (0), (Some 4), true, false, (Some (TAtom "v134")), (Some (4)))]); ((TAtom "L131"), []); ((TAtom "L124"), [(2%N, (TApp "tmp" [(TAtom "v141")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v143")]), (0), (Some 8), false, true, (Some (TAtom "v142")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v141")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (9%N, (TApp "tmp" [(TAtom "v146")]), (0), (Some 4), false, true, (Some (TAtom "v146")), (Some (0)))]); ((TAtom "L125"), [(2%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v153")]), (0), (Some 4), true, false, (Some (TAtom "v152")), (Some (4)))]); ((TAtom "L147"), [(1%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v159")]), (0), (Some 8), false, true, (Some (TAtom "v158")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "v157")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v163")]), (0), (Some 4), true, false, (Some (TAtom "v163")), (Some (0)))]); ((TAtom "L168"), [(1%N, (TApp "tmp" [(TAtom "v163")]), (0), (Some 4), true, true, (Some (TAtom "v163")), (Some (0)))]); ((TAtom "L169"), []); ((TAtom "L180"), []); ((TAtom "L148"), [(1%N, (TApp "tmp" [(TAtom "v151")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), true, false, (Some (TAtom "v193")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v194")]), (0), (Some 4), false, true, (Some (TAtom "v193")), (Some (4)))]); ((TAtom "L116"), [])].

End fn__IO_ferror.

Module fn___GI__IO_file_doallocate.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v39"); (TAtom "v4")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L66"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L7"), [(TAtom "v0")]); ((TAtom "L76"), []); ((TAtom "L78"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v75")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L12"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v16"); (TAtom "v4")]); ((TAtom "iw_1.join"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v23"); (TAtom "v4")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L5"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L26"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v39"); (TAtom "v4")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v45")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L48"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4"); (TAtom "v54")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L33"), [(TAtom "chk4"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L28"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L65"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4"); (TAtom "v69")]); ((TAtom "L66"), [(TAtom "chk9"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L59"), [(TAtom "v0"); (TAtom "v73")]); ((TAtom "L7"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v75")]); ((TAtom "L76"), []); ((TAtom "L78"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v9")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))]); ((TAtom "L12"), [(2%N, (TApp "tmp" [(TAtom "v15")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (144)))]); ((TAtom "L13"), []); ((TAtom "L5"), [(2%N, (TApp "tmp" [(TAtom "v29")]), (0), (Some 4), true, false, (Some (TAtom "v4")), (Some (24)))]); ((TAtom "L26"), [(2%N, (TApp "tmp" [(TAtom "v37")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (40)))]); ((TAtom "L42"), []); ((TAtom "L43"), []); ((TAtom "L48"), [(2%N, (TApp "tmp" [(TAtom "v51")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))]); ((TAtom "L49"), []); ((TAtom "L33"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L28"), [(2%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)))]); ((TAtom "L65"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)))]); ((TAtom "L66"), []); ((TAtom "L59"), [(1%N, (TApp "tmp" [(TAtom "v62")]), (0), (Some 8), true, false, (Some (TAtom "v4")), (Some (56)))]); ((TAtom "L7"), []); ((TAtom "L76"), []); ((TAtom "L78"), [])].

End fn___GI__IO_file_doallocate.

Module fn___GI__IO_file_stat.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v5")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))])].

End fn___GI__IO_file_stat.

Module fn___GI__IO_file_close.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))])].

End fn___GI__IO_file_close.

Module fn__IO_new_file_write.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L8"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L9"), [(TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L38"), [(TAtom "chk0"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L40"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "L10"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L61"), [(TAtom "chk7"); (TAtom "v0"); (TAtom "v60")]); ((TAtom "L63"), [(TAtom "v60")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L8"), [(TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L9"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L14"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v30"); (TAtom "v4")]); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v36"); (TAtom "v4")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v37"); (TAtom "v4")]); ((TAtom "L38"), [(TAtom "pr.2"); (TAtom "v0"); (TAtom "v4")]); ((TAtom "L40"), [(TAtom "v0"); (TAtom "v4"); (TAtom "v54"); (TAtom "v57")]); ((TAtom "L10"), [(TAtom "chk7"); (TAtom "v0"); (TAtom "v60")]); ((TAtom "L61"), [(TAtom "v60")]); ((TAtom "L63"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L8"), []); ((TAtom "L9"), [(2%N, (TApp "tmp" [(TAtom "v18")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116)))]); ((TAtom "L14"), [(2%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))]); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (112)))]); ((TAtom "L16"), []); ((TAtom "L38"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L40"), [(2%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (200))); (5%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (200)))]); ((TAtom "L10"), [(3%N, (TApp "tmp" [(TAtom "v65")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (144)))]); ((TAtom "L61"), [(1%N, (TApp "tmp" [(TAtom "v65")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (144))); (4%N, (TApp "tmp" [(TAtom "v69")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (144)))]); ((TAtom "L63"), [])].

End fn__IO_new_file_write.

Module fn___GI__IO_setb.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L34"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L35"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v21"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L17"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L10"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L33"), []); ((TAtom "L34"), []); ((TAtom "L35"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L16"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L17"), []); ((TAtom "L8"), [(1%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L10"), [(2%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (56))); (5%N, (TApp "tmp" [(TAtom "v31")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (64)))]); ((TAtom "L33"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L34"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0))); (4%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L35"), [])].

End fn___GI__IO_setb.

Module fn___GI__IO_doallocbuf.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.join"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "L26"), []); ((TAtom "L13"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "L4"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v23")]); ((TAtom "L19"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L11"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.L10"), [(TAtom "v0"); (TAtom "v31")]); ((TAtom "iw_1.join"), [(TAtom "v0")]); ((TAtom "L26"), []); ((TAtom "L13"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "v6")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (56)))]); ((TAtom "L2"), []); ((TAtom "L4"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L18"), [(2%N, (TApp "tmp" [(TAtom "v21")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L19"), []); ((TAtom "L11"), [(2%N, (TApp "tmp" [(TAtom "v30")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v33")]), (0), (Some 8), true, false, (Some (TAtom "v31")), (Some (104)))]); ((TAtom "L26"), []); ((TAtom "L13"), [])].

End fn___GI__IO_doallocbuf.

Module fn___gnu_dev_major.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___gnu_dev_major.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("__fpending", app (map fst fn___fpending.live_in) (app (map fst fn___fpending.live_out) (map fst fn___fpending.footprint))); ("_IO_ferror", app (map fst fn__IO_ferror.live_in) (app (map fst fn__IO_ferror.live_out) (map fst fn__IO_ferror.footprint))); ("__GI__IO_file_doallocate", app (map fst fn___GI__IO_file_doallocate.live_in) (app (map fst fn___GI__IO_file_doallocate.live_out) (map fst fn___GI__IO_file_doallocate.footprint))); ("__GI__IO_file_stat", app (map fst fn___GI__IO_file_stat.live_in) (app (map fst fn___GI__IO_file_stat.live_out) (map fst fn___GI__IO_file_stat.footprint))); ("__GI__IO_file_close", app (map fst fn___GI__IO_file_close.live_in) (app (map fst fn___GI__IO_file_close.live_out) (map fst fn___GI__IO_file_close.footprint))); ("_IO_new_file_write", app (map fst fn__IO_new_file_write.live_in) (app (map fst fn__IO_new_file_write.live_out) (map fst fn__IO_new_file_write.footprint))); ("__GI__IO_setb", app (map fst fn___GI__IO_setb.live_in) (app (map fst fn___GI__IO_setb.live_out) (map fst fn___GI__IO_setb.footprint))); ("__GI__IO_doallocbuf", app (map fst fn___GI__IO_doallocbuf.live_in) (app (map fst fn___GI__IO_doallocbuf.live_out) (map fst fn___GI__IO_doallocbuf.footprint))); ("__gnu_dev_major", app (map fst fn___gnu_dev_major.live_in) (app (map fst fn___gnu_dev_major.live_out) (map fst fn___gnu_dev_major.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) LibioReadSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End LibioReadBlocks.
