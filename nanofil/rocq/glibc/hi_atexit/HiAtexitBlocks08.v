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


Module HiAtexitBlocks08.

Module fn__IO_default_showmanyc.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn__IO_default_showmanyc.

Module fn__IO_default_imbue.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn__IO_default_imbue.

Module fn__IO_new_fclose.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L73"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L99"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L100"), [(TAtom "chk0"); (TAtom "chk17"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L101"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_1.L5"), [(TAtom "chk0"); (TAtom "chk22"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L19"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L28"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L29"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L22"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L23"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L45"), [(TAtom "chk0"); (TAtom "chk31"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L66"), [(TAtom "chk0"); (TAtom "chk36"); (TAtom "iw_1.v61"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L67"), [(TAtom "chk0"); (TAtom "iw_1.v61"); (TAtom "iw_1.v68"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L78"), [(TAtom "chk0"); (TAtom "iw_1.v61"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L46"), [(TAtom "chk0"); (TAtom "chk31"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "L136"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L143"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L169"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L170"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L174"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160")]); ((TAtom "L163"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158")]); ((TAtom "L195"), [(TAtom "chk51"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v190")]); ((TAtom "L196"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v190"); (TAtom "v197")]); ((TAtom "L207"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v190")]); ((TAtom "L137"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L218"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L10"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L11"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L19"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L20"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L4"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.join"), [(TAtom "pr.1")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L18"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L29"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22"); (TAtom "v38")]); ((TAtom "L30"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L23"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L24"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L49"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L73"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64"); (TAtom "v71")]); ((TAtom "L74"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22"); (TAtom "v64")]); ((TAtom "L78"), [(TAtom "chk0"); (TAtom "chk8"); (TAtom "v0"); (TAtom "v22")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L50"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), [(TAtom "chk0"); (TAtom "chk17"); (TAtom "v0")]); ((TAtom "L99"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v107")]); ((TAtom "L100"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L121"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L101"), [(TAtom "chk0"); (TAtom "chk22"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L5"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L19"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L28"), [(TAtom "chk0"); (TAtom "iw_1.v35"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L29"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L22"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L23"), [(TAtom "chk0"); (TAtom "chk31"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L45"), [(TAtom "chk0"); (TAtom "chk36"); (TAtom "iw_1.v61"); (TAtom "iw_1.v65"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L66"), [(TAtom "chk0"); (TAtom "chk36"); (TAtom "iw_1.v61"); (TAtom "iw_1.v68"); (TAtom "iw_1.v69"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L67"), [(TAtom "chk0"); (TAtom "iw_1.v61"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L78"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_1.L46"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L8"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "iw_2.L10"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v131")]); ((TAtom "iw_2.join"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L136"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L143"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L145"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L169"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160"); (TAtom "v167")]); ((TAtom "L170"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158"); (TAtom "v160")]); ((TAtom "L174"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v158")]); ((TAtom "L163"), [(TAtom "chk51"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v190"); (TAtom "v194")]); ((TAtom "L195"), [(TAtom "chk51"); (TAtom "pr.1"); (TAtom "v0"); (TAtom "v190"); (TAtom "v197"); (TAtom "v198")]); ((TAtom "L196"), [(TAtom "pr.1"); (TAtom "v0"); (TAtom "v190")]); ((TAtom "L207"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L137"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "L218"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.start"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L10"), [(TAtom "iw_3.v16"); (TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L11"), [(TAtom "iw_3.v7"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L19"), [(TAtom "iw_3.v25"); (TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L20"), [(TAtom "pr.1"); (TAtom "v0")]); ((TAtom "iw_3.L4"), [(TAtom "pr.1")]); ((TAtom "iw_3.join"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L18"), [(3%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 1), true, false, (Some (TAtom "v26")), (Some (0)))]); ((TAtom "L29"), [(2%N, (TApp "tmp" [(TAtom "v32")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v34")]), (0), (Some 8), true, false, (Some (TAtom "v33")), (Some (8)))]); ((TAtom "L30"), []); ((TAtom "L23"), [(2%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v43")]), (0), (Some 4), false, true, (Some (TAtom "v43")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v42")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v47")]), (0), (Some 8), false, true, (Some (TAtom "v46")), (Some (8)))]); ((TAtom "L24"), [(2%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v54")), (Some (8)))]); ((TAtom "L49"), [(1%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (3%N, (TApp "tmp" [(TAtom "v64")]), (0), (Some 4), true, true, (Some (TAtom "v64")), (Some (0)))]); ((TAtom "L73"), []); ((TAtom "L74"), []); ((TAtom "L78"), []); ((TAtom "L67"), [(2%N, (TApp "tmp" [(TAtom "v89")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v91")]), (0), (Some 8), false, true, (Some (TAtom "v90")), (Some (8)))]); ((TAtom "L50"), [(1%N, (TApp "tmp" [(TAtom "v53")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v96")]), (0), (Some 4), true, false, (Some (TAtom "v95")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v96")]), (0), (Some 4), false, true, (Some (TAtom "v95")), (Some (4)))]); ((TAtom "L13"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L99"), [(3%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116))); (7%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (116))); (12%N, (TApp "tmp" [(TAtom "v109")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (116)))]); ((TAtom "L100"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "L121"), []); ((TAtom "L101"), [(1%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "iw_1.L5"), [(0%N, (TApp "tmp" [(TAtom "v0")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (0)))]); ((TAtom "iw_1.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v25")]), (0), (Some 1), true, false, (Some (TAtom "iw_1.v25")), (Some (0)))]); ((TAtom "iw_1.L28"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v31")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v33")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v32")), (Some (4)))]); ((TAtom "iw_1.L29"), []); ((TAtom "iw_1.L22"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v39")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v41")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v40")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "iw_1.v39")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (9%N, (TApp "tmp" [(TAtom "iw_1.v44")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v44")), (Some (0)))]); ((TAtom "iw_1.L23"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_1.v51")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v50")), (Some (4)))]); ((TAtom "iw_1.L45"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_1.v57")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v56")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "iw_1.v55")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "iw_1.v61")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v61")), (Some (0)))]); ((TAtom "iw_1.L66"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v61")]), (0), (Some 4), true, true, (Some (TAtom "iw_1.v61")), (Some (0)))]); ((TAtom "iw_1.L67"), []); ((TAtom "iw_1.L78"), []); ((TAtom "iw_1.L46"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v49")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_1.v92")]), (0), (Some 4), true, false, (Some (TAtom "iw_1.v91")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "iw_1.v92")]), (0), (Some 4), false, true, (Some (TAtom "iw_1.v91")), (Some (4)))]); ((TAtom "L8"), [(3%N, (TApp "tmp" [(TAtom "v130")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (216)))]); ((TAtom "iw_2.L10"), []); ((TAtom "iw_2.join"), [(2%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 8), true, false, (Some (TAtom "v131")), (Some (16))); (7%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (192)))]); ((TAtom "L136"), [(2%N, (TApp "tmp" [(TAtom "v147")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (160))); (5%N, (TApp "tmp" [(TAtom "v149")]), (0), (Some 8), true, false, (Some (TAtom "v148")), (Some (72)))]); ((TAtom "L143"), []); ((TAtom "L145"), [(2%N, (TApp "tmp" [(TAtom "v157")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (152))); (5%N, (TApp "tmp" [(TAtom "v160")]), (0), (Some 4), true, true, (Some (TAtom "v160")), (Some (0)))]); ((TAtom "L169"), []); ((TAtom "L170"), []); ((TAtom "L174"), []); ((TAtom "L163"), [(1%N, (TApp "tmp" [(TAtom "v158")]), (0), (Some 8), true, false, (Some (TAtom "v158")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v187")]), (0), (Some 8), true, false, (Some (TAtom "v158")), (Some (56))); (9%N, (TApp "tmp" [(TAtom "v190")]), (0), (Some 4), true, false, (Some (TAtom "v190")), (Some (0)))]); ((TAtom "L195"), [(1%N, (TApp "tmp" [(TAtom "v190")]), (0), (Some 4), true, true, (Some (TAtom "v190")), (Some (0)))]); ((TAtom "L196"), []); ((TAtom "L207"), []); ((TAtom "L137"), [(2%N, (TApp "tmp" [(TAtom "v222")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (80)))]); ((TAtom "L218"), []); ((TAtom "iw_3.start"), []); ((TAtom "iw_3.L10"), []); ((TAtom "iw_3.L11"), []); ((TAtom "iw_3.L19"), []); ((TAtom "iw_3.L20"), []); ((TAtom "iw_3.L4"), []); ((TAtom "iw_3.join"), [])].

End fn__IO_new_fclose.

Module fn___GI__IO_puts.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L31"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L32"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L51"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L75"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66"); (TAtom "v73")]); ((TAtom "L76"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66"); (TAtom "v73")]); ((TAtom "L80"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66")]); ((TAtom "L69"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L52"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L109"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L119"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L121"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L162"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "iw_1.L10"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v167"); (TAtom "v6")]); ((TAtom "iw_1.join"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v167"); (TAtom "v6")]); ((TAtom "L163"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L180"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L182"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L183"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L184"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L181"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L101"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L212"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v215")]); ((TAtom "L103"), [(TAtom "chk1"); (TAtom "v12")]); ((TAtom "iw_2.L5"), [(TAtom "chk1"); (TAtom "chk38"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L19"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L28"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L29"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L22"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L23"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L45"), [(TAtom "chk47"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L66"), [(TAtom "chk52"); (TAtom "iw_2.v61"); (TAtom "pr.1")]); ((TAtom "iw_2.L67"), [(TAtom "iw_2.v61"); (TAtom "iw_2.v68"); (TAtom "pr.1")]); ((TAtom "iw_2.L78"), [(TAtom "iw_2.v61"); (TAtom "pr.1")]); ((TAtom "iw_2.L46"), [(TAtom "chk47"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "L9"), [(TAtom "pr.1")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L20"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L31"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v40"); (TAtom "v6")]); ((TAtom "L32"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L25"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L26"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L51"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66"); (TAtom "v73")]); ((TAtom "L75"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66"); (TAtom "v73")]); ((TAtom "L76"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6"); (TAtom "v66")]); ((TAtom "L80"), [(TAtom "chk1"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v12"); (TAtom "v24"); (TAtom "v6")]); ((TAtom "L69"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L52"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L109"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L119"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L121"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L162"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v167"); (TAtom "v6")]); ((TAtom "iw_1.L10"), [(TAtom "chk1"); (TAtom "v0"); (TAtom "v12"); (TAtom "v167"); (TAtom "v6")]); ((TAtom "iw_1.join"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v177"); (TAtom "v6")]); ((TAtom "L163"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L180"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L182"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v200"); (TAtom "v6")]); ((TAtom "L183"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L184"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v208"); (TAtom "v6")]); ((TAtom "L181"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v6")]); ((TAtom "L101"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v215")]); ((TAtom "L212"), [(TAtom "chk1"); (TAtom "v12"); (TAtom "v215")]); ((TAtom "L103"), [(TAtom "chk1"); (TAtom "chk38"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L5"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L19"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L28"), [(TAtom "chk1"); (TAtom "iw_2.v35"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L29"), [(TAtom "chk1"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L22"), [(TAtom "pr.1")]); ((TAtom "iw_2.L23"), [(TAtom "chk47"); (TAtom "pr.1"); (TAtom "v12")]); ((TAtom "iw_2.L45"), [(TAtom "chk52"); (TAtom "iw_2.v61"); (TAtom "iw_2.v65"); (TAtom "pr.1")]); ((TAtom "iw_2.L66"), [(TAtom "chk52"); (TAtom "iw_2.v61"); (TAtom "iw_2.v68"); (TAtom "iw_2.v69"); (TAtom "pr.1")]); ((TAtom "iw_2.L67"), [(TAtom "iw_2.v61"); (TAtom "pr.1")]); ((TAtom "iw_2.L78"), [(TAtom "pr.1")]); ((TAtom "iw_2.L46"), [(TAtom "pr.1")]); ((TAtom "L9"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v11")]), (0), (Some 8), true, false, (Some (TAtom "v11")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 4), true, false, (Some (TAtom "v12")), (Some (0)))]); ((TAtom "L20"), [(3%N, (TApp "tmp" [(TAtom "v28")]), (0), (Some 1), true, false, (Some (TAtom "v28")), (Some (0)))]); ((TAtom "L31"), [(2%N, (TApp "tmp" [(TAtom "v34")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v36")]), (0), (Some 8), true, false, (Some (TAtom "v35")), (Some (8)))]); ((TAtom "L32"), []); ((TAtom "L25"), [(2%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 4), false, true, (Some (TAtom "v45")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v44")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 8), false, true, (Some (TAtom "v48")), (Some (8)))]); ((TAtom "L26"), [(2%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v57")]), (0), (Some 8), true, false, (Some (TAtom "v56")), (Some (8)))]); ((TAtom "L51"), [(1%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (3%N, (TApp "tmp" [(TAtom "v66")]), (0), (Some 4), true, true, (Some (TAtom "v66")), (Some (0)))]); ((TAtom "L75"), []); ((TAtom "L76"), []); ((TAtom "L80"), []); ((TAtom "L69"), [(2%N, (TApp "tmp" [(TAtom "v91")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "v93")]), (0), (Some 8), false, true, (Some (TAtom "v92")), (Some (8)))]); ((TAtom "L52"), [(1%N, (TApp "tmp" [(TAtom "v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), true, false, (Some (TAtom "v97")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 4), false, true, (Some (TAtom "v97")), (Some (4)))]); ((TAtom "L109"), [(2%N, (TApp "tmp" [(TAtom "v122")]), (0), (Some 8), true, false, (Some (TAtom "v122")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v124")]), (0), (Some 4), true, false, (Some (TAtom "v123")), (Some (192)))]); ((TAtom "L119"), [(2%N, (TApp "tmp" [(TAtom "v127")]), (0), (Some 8), true, false, (Some (TAtom "v127")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v129")]), (0), (Some 4), false, true, (Some (TAtom "v128")), (Some (192)))]); ((TAtom "L121"), [(2%N, (TApp "tmp" [(TAtom "v131")]), (0), (Some 8), true, false, (Some (TAtom "v131")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v133")]), (0), (Some 4), true, false, (Some (TAtom "v132")), (Some (192)))]); ((TAtom "L162"), [(2%N, (TApp "tmp" [(TAtom "v164")]), (0), (Some 8), true, false, (Some (TAtom "v164")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v166")]), (0), (Some 8), true, false, (Some (TAtom "v165")), (Some (216)))]); ((TAtom "iw_1.L10"), []); ((TAtom "iw_1.join"), [(2%N, (TApp "tmp" [(TAtom "v169")]), (0), (Some 8), true, false, (Some (TAtom "v167")), (Some (56))); (5%N, (TApp "tmp" [(TAtom "v171")]), (0), (Some 8), true, false, (Some (TAtom "v171")), (Some (0)))]); ((TAtom "L163"), []); ((TAtom "L180"), [(2%N, (TApp "tmp" [(TAtom "v185")]), (0), (Some 8), true, false, (Some (TAtom "v185")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v187")]), (0), (Some 8), true, false, (Some (TAtom "v186")), (Some (40))); (8%N, (TApp "tmp" [(TAtom "v189")]), (0), (Some 8), true, false, (Some (TAtom "v189")), (Some (0))); (11%N, (TApp "tmp" [(TAtom "v191")]), (0), (Some 8), true, false, (Some (TAtom "v190")), (Some (48)))]); ((TAtom "L182"), [(2%N, (TApp "tmp" [(TAtom "v198")]), (0), (Some 8), true, false, (Some (TAtom "v198")), (Some (0)))]); ((TAtom "L183"), [(2%N, (TApp "tmp" [(TAtom "v201")]), (0), (Some 8), true, false, (Some (TAtom "v201")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v203")]), (0), (Some 8), true, false, (Some (TAtom "v202")), (Some (40))); (8%N, (TApp "tmp" [(TAtom "v203")]), (0), (Some 8), false, true, (Some (TAtom "v202")), (Some (40))); (10%N, (TApp "tmp" [(TAtom "v204")]), (0), (Some 1), false, true, (Some (TAtom "v204")), (Some (0)))]); ((TAtom "L184"), []); ((TAtom "L181"), []); ((TAtom "L101"), []); ((TAtom "L212"), []); ((TAtom "L103"), [(1%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 4), true, false, (Some (TAtom "v12")), (Some (0)))]); ((TAtom "iw_2.L5"), [(0%N, (TApp "tmp" [(TAtom "v12")]), (0), (Some 4), true, false, (Some (TAtom "v12")), (Some (0)))]); ((TAtom "iw_2.L19"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v25")]), (0), (Some 1), true, false, (Some (TAtom "iw_2.v25")), (Some (0)))]); ((TAtom "iw_2.L28"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v31")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_2.v33")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v32")), (Some (4)))]); ((TAtom "iw_2.L29"), []); ((TAtom "iw_2.L22"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v39")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_2.v41")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v40")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "iw_2.v39")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (9%N, (TApp "tmp" [(TAtom "iw_2.v44")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v44")), (Some (0)))]); ((TAtom "iw_2.L23"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (5%N, (TApp "tmp" [(TAtom "iw_2.v51")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v50")), (Some (4)))]); ((TAtom "iw_2.L45"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_2.v57")]), (0), (Some 8), false, true, (Some (TAtom "iw_2.v56")), (Some (8))); (6%N, (TApp "tmp" [(TAtom "iw_2.v55")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (8%N, (TApp "tmp" [(TAtom "iw_2.v61")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v61")), (Some (0)))]); ((TAtom "iw_2.L66"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v61")]), (0), (Some 4), true, true, (Some (TAtom "iw_2.v61")), (Some (0)))]); ((TAtom "iw_2.L67"), []); ((TAtom "iw_2.L78"), []); ((TAtom "iw_2.L46"), [(1%N, (TApp "tmp" [(TAtom "iw_2.v49")]), (0), (Some 8), true, false, (Some (TAtom "v12")), (Some (136))); (4%N, (TApp "tmp" [(TAtom "iw_2.v92")]), (0), (Some 4), true, false, (Some (TAtom "iw_2.v91")), (Some (4))); (7%N, (TApp "tmp" [(TAtom "iw_2.v92")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v91")), (Some (4)))]); ((TAtom "L9"), [])].

End fn___GI__IO_puts.

Module fn_glibc_stdfiles__IO_stdfiles_init.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L2"), []); ((TAtom "L3"), [(TAtom "chk0"); (TAtom "pr.1")]); ((TAtom "L5"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v1")]); ((TAtom "L2"), [(TAtom "chk0"); (TAtom "pr.1")]); ((TAtom "L3"), [(TAtom "v17")]); ((TAtom "L5"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), []); ((TAtom "L2"), [(1%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)))]); ((TAtom "L3"), [(0%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0))); (3%N, (TApp "tmp" [(TAtom "v13")]), (0), (Some 8), false, true, (Some (TAtom "v12")), (Some (184))); (5%N, (TApp "tmp" [(TAtom "pr.1")]), (0), (Some 8), true, false, (Some (TAtom "pr.1")), (Some (0)))]); ((TAtom "L5"), [])].

End fn_glibc_stdfiles__IO_stdfiles_init.

Module fn__IO_vtable_check.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn__IO_vtable_check.

Module fn_glibc_vtables_check_stdfiles_vtables.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L11"), []); ((TAtom "L12"), []); ((TAtom "L23"), []); ((TAtom "L24"), []); ((TAtom "L0"), []); ((TAtom "L2"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), []); ((TAtom "L11"), [(TAtom "v20")]); ((TAtom "L12"), []); ((TAtom "L23"), [(TAtom "v32")]); ((TAtom "L24"), []); ((TAtom "L0"), []); ((TAtom "L2"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(3%N, (TApp "tmp" [(TAtom "v4")]), (0), (Some 8), true, false, (Some (TAtom "v3")), (Some (216)))]); ((TAtom "L11"), [(3%N, (TApp "tmp" [(TAtom "v14")]), (0), (Some 8), true, false, (Some (TAtom "v13")), (Some (216)))]); ((TAtom "L12"), []); ((TAtom "L23"), [(3%N, (TApp "tmp" [(TAtom "v26")]), (0), (Some 8), true, false, (Some (TAtom "v25")), (Some (216)))]); ((TAtom "L24"), []); ((TAtom "L0"), [(3%N, (TApp "tmp" [(TAtom "iw_1.v6")]), (0), (Some 8), false, true, (Some (TAtom "iw_1.v6")), (Some (0)))]); ((TAtom "L2"), [])].

End fn_glibc_vtables_check_stdfiles_vtables.

Module fn___isatty_nostatus.

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

End fn___isatty_nostatus.

Module fn___GI___libc_write.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___GI___libc_write.

Module fn___GI___write_nocancel.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___GI___write_nocancel.

Module fn___lseek64.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___lseek64.

Module fn___GI___fstat64.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___GI___fstat64.

Module fn___GI___close_nocancel.

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

End fn___GI___close_nocancel.

Module fn___GI__exit.

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

End fn___GI__exit.

Module fn___run_exit_handlers.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L13"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L33"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v31"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v31"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L38"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L27"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L15"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L55"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L57"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L69"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60"); (TAtom "v67")]); ((TAtom "L70"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60"); (TAtom "v67")]); ((TAtom "L74"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60")]); ((TAtom "L88"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L91"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L101"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L102"), [(TAtom "chk6"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L130"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L145"), [(TAtom "chk16"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L146"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v147"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L157"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L152"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L181"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v179"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L182"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v179"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L186"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L196"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L207"), [(TAtom "chk21"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L208"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v209"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L219"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L214"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L241"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v239"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L242"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v239"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L246"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L256"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L272"), [(TAtom "chk28"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L273"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v274"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L284"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L279"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L308"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v306"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L309"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v306"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L313"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L325"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L328"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L330"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L326"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L332"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L334"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L123"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L103"), [(TAtom "chk6"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L350"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90")]); ((TAtom "L365"), [(TAtom "chk8"); (TAtom "v0"); (TAtom "v360"); (TAtom "v4")]); ((TAtom "L366"), [(TAtom "v0"); (TAtom "v360"); (TAtom "v367"); (TAtom "v4")]); ((TAtom "L377"), [(TAtom "v0"); (TAtom "v360"); (TAtom "v4")]); ((TAtom "L372"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L388"), [(TAtom "v0")]); ((TAtom "L390"), [(TAtom "v0")])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L13"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v31"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L33"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v31"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L34"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v24"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L38"), [(TAtom "v0"); (TAtom "v12"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L27"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v6")]); ((TAtom "L15"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L55"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L57"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60"); (TAtom "v67")]); ((TAtom "L69"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60"); (TAtom "v67")]); ((TAtom "L70"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v60")]); ((TAtom "L74"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L88"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L91"), [(TAtom "chk8"); (TAtom "v0"); (TAtom "v360"); (TAtom "v364"); (TAtom "v4")]); ((TAtom "L101"), [(TAtom "chk6"); (TAtom "chk9"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L102"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L130"), [(TAtom "chk16"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v144"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L145"), [(TAtom "chk16"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v147"); (TAtom "v148"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L146"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v140"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L157"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v133"); (TAtom "v137"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L152"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v179"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L181"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v179"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L182"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v172"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L186"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L196"), [(TAtom "chk21"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v206"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L207"), [(TAtom "chk21"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v209"); (TAtom "v210"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L208"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v202"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L219"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v199"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L214"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v239"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L241"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v239"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L242"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v232"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L246"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L256"), [(TAtom "chk28"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v271"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L272"), [(TAtom "chk28"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v274"); (TAtom "v275"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L273"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v267"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L284"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v260"); (TAtom "v264"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L279"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v306"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L308"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v306"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L309"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v299"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L313"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L325"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L328"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L330"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L326"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L332"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v121"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L334"), [(TAtom "chk13"); (TAtom "chk6"); (TAtom "v0"); (TAtom "v116"); (TAtom "v119"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L123"), [(TAtom "chk6"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90"); (TAtom "v96")]); ((TAtom "L103"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4"); (TAtom "v90")]); ((TAtom "L350"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L365"), [(TAtom "chk8"); (TAtom "v0"); (TAtom "v360"); (TAtom "v367"); (TAtom "v368"); (TAtom "v4")]); ((TAtom "L366"), [(TAtom "v0"); (TAtom "v360"); (TAtom "v4")]); ((TAtom "L377"), [(TAtom "v0"); (TAtom "v4")]); ((TAtom "L372"), [(TAtom "v0")]); ((TAtom "L388"), [(TAtom "v0")]); ((TAtom "L390"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(4%N, (TApp "tmp" [(TAtom "v17")]), (0), (Some 8), true, false, (Some (TAtom "v16")), (Some (8)))]); ((TAtom "L13"), [(2%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 4), true, true, (Some (TAtom "v24")), (Some (0)))]); ((TAtom "L33"), []); ((TAtom "L34"), []); ((TAtom "L38"), []); ((TAtom "L27"), [(3%N, (TApp "tmp" [(TAtom "v49")]), (0), (Some 8), false, true, (Some (TAtom "v48")), (Some (8)))]); ((TAtom "L15"), [(3%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 4), true, false, (Some (TAtom "v51")), (Some (4))); (6%N, (TApp "tmp" [(TAtom "v52")]), (0), (Some 4), false, true, (Some (TAtom "v51")), (Some (4)))]); ((TAtom "L55"), []); ((TAtom "L57"), [(2%N, (TApp "tmp" [(TAtom "v60")]), (0), (Some 4), true, true, (Some (TAtom "v60")), (Some (0)))]); ((TAtom "L69"), []); ((TAtom "L70"), []); ((TAtom "L74"), []); ((TAtom "L88"), [(1%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)))]); ((TAtom "L91"), [(2%N, (TApp "tmp" [(TAtom "v98")]), (0), (Some 1), false, true, (Some (TAtom "v98")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v360")]), (0), (Some 4), true, false, (Some (TAtom "v360")), (Some (0)))]); ((TAtom "L101"), [(2%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (8)))]); ((TAtom "L102"), [(2%N, (TApp "tmp" [(TAtom "v105")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v112")]), (0), (Some 8), false, true, (Some (TAtom "v90")), (Some (8))); (10%N, (TApp "tmp" [(TAtom "v118")]), (0), (Some 8), true, false, (Some (TAtom "v118")), (Some (0))); (12%N, (TApp "tmp" [(TAtom "v116")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None)]); ((TAtom "L130"), [(2%N, (TApp "tmp" [(TAtom "v132")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (5%N, (TApp "tmp" [(TAtom "v136")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (8%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 4), true, false, (Some (TAtom "v140")), (Some (0)))]); ((TAtom "L145"), [(1%N, (TApp "tmp" [(TAtom "v140")]), (0), (Some 4), true, true, (Some (TAtom "v140")), (Some (0)))]); ((TAtom "L146"), []); ((TAtom "L157"), []); ((TAtom "L152"), [(4%N, (TApp "tmp" [(TAtom "v172")]), (0), (Some 4), true, true, (Some (TAtom "v172")), (Some (0)))]); ((TAtom "L181"), []); ((TAtom "L182"), []); ((TAtom "L186"), []); ((TAtom "L196"), [(2%N, (TApp "tmp" [(TAtom "v198")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (5%N, (TApp "tmp" [(TAtom "v202")]), (0), (Some 4), true, false, (Some (TAtom "v202")), (Some (0)))]); ((TAtom "L207"), [(1%N, (TApp "tmp" [(TAtom "v202")]), (0), (Some 4), true, true, (Some (TAtom "v202")), (Some (0)))]); ((TAtom "L208"), []); ((TAtom "L219"), []); ((TAtom "L214"), [(4%N, (TApp "tmp" [(TAtom "v232")]), (0), (Some 4), true, true, (Some (TAtom "v232")), (Some (0)))]); ((TAtom "L241"), []); ((TAtom "L242"), []); ((TAtom "L246"), []); ((TAtom "L256"), [(1%N, (TApp "tmp" [(TAtom "v116")]), (0), (Some 8), false, true, (Some (TAtom "v90")), None); (4%N, (TApp "tmp" [(TAtom "v259")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (7%N, (TApp "tmp" [(TAtom "v263")]), (0), (Some 8), true, false, (Some (TAtom "v90")), None); (10%N, (TApp "tmp" [(TAtom "v267")]), (0), (Some 4), true, false, (Some (TAtom "v267")), (Some (0)))]); ((TAtom "L272"), [(1%N, (TApp "tmp" [(TAtom "v267")]), (0), (Some 4), true, true, (Some (TAtom "v267")), (Some (0)))]); ((TAtom "L273"), []); ((TAtom "L284"), []); ((TAtom "L279"), [(4%N, (TApp "tmp" [(TAtom "v299")]), (0), (Some 4), true, true, (Some (TAtom "v299")), (Some (0)))]); ((TAtom "L308"), []); ((TAtom "L309"), []); ((TAtom "L313"), []); ((TAtom "L325"), []); ((TAtom "L328"), []); ((TAtom "L330"), []); ((TAtom "L326"), []); ((TAtom "L332"), []); ((TAtom "L334"), []); ((TAtom "L123"), [(2%N, (TApp "tmp" [(TAtom "v341")]), (0), (Some 8), true, false, (Some (TAtom "v341")), (Some (0)))]); ((TAtom "L103"), [(1%N, (TApp "tmp" [(TAtom "v90")]), (0), (Some 8), true, false, (Some (TAtom "v90")), (Some (0))); (3%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), false, true, (Some (TAtom "v2")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "v2")]), (0), (Some 8), true, false, (Some (TAtom "v2")), (Some (0)))]); ((TAtom "L350"), []); ((TAtom "L365"), [(1%N, (TApp "tmp" [(TAtom "v360")]), (0), (Some 4), true, true, (Some (TAtom "v360")), (Some (0)))]); ((TAtom "L366"), []); ((TAtom "L377"), []); ((TAtom "L372"), []); ((TAtom "L388"), []); ((TAtom "L390"), [])].

End fn___run_exit_handlers.

Module fn___GI_exit.

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

End fn___GI_exit.

Module fn___GI___call_tls_dtors.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [])].

End fn___GI___call_tls_dtors.

End HiAtexitBlocks08.
