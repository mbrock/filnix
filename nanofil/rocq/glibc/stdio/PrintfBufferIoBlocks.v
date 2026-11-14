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


From Glibc Require Import PrintfBufferIoSrc.
Module PrintfBufferIoBlocks.

Module fn___printf_buffer_write.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L20"), []); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v65")]); ((TAtom "L68"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L17"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v2"); (TAtom "v4")]); ((TAtom "L6"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L16"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L32"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v37")]); ((TAtom "L33"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L20"), []); ((TAtom "L22"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L42"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk2"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0")]); ((TAtom "L43"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v65")]); ((TAtom "L67"), [(TAtom "chk0"); (TAtom "chk1"); (TAtom "chk6"); (TAtom "pr.1"); (TAtom "pr.2"); (TAtom "v0"); (TAtom "v65")]); ((TAtom "L68"), [(TAtom "chk0"); (TAtom "v0"); (TAtom "v86"); (TAtom "v89")]); ((TAtom "L17"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L6"), []); ((TAtom "L15"), []); ((TAtom "L16"), [(2%N, (TApp "tmp" [(TAtom "v24")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v27")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L32"), []); ((TAtom "L33"), []); ((TAtom "L20"), []); ((TAtom "L22"), [(2%N, (TApp "tmp" [(TAtom "v45")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (5%N, (TApp "tmp" [(TAtom "v48")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L42"), []); ((TAtom "L43"), [(2%N, (TApp "tmp" [(TAtom "v58")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (16))); (5%N, (TApp "tmp" [(TAtom "v61")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L67"), []); ((TAtom "L68"), [(1%N, (TApp "tmp" [(TAtom "v61")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v74")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (7%N, (TApp "tmp" [(TAtom "v74")]), (0), (Some 8), false, true, (Some (TAtom "v0")), (Some (8)))]); ((TAtom "L17"), [])].

End fn___printf_buffer_write.

Module fn___printf_buffer_flush.

Definition live_in : list (name * list name) :=
  [((TAtom "start"), [(TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "iw_2.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L9"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L11"), []); ((TAtom "iw_2.L12"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L16"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L21"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L23"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L25"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L27"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L31"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L34"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L37"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L39"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L35"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L43"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L45"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L32"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L49"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L52"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L54"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L50"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L58"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L60"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L6"), []); ((TAtom "iw_3.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), []); ((TAtom "L15"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L22"), []); ((TAtom "L23"), [])].

Definition live_out : list (name * list name) :=
  [((TAtom "start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L2"), []); ((TAtom "iw_2.start"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L9"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L11"), []); ((TAtom "iw_2.L12"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L14"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L16"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L18"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L21"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L23"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L25"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L27"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L31"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L34"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L37"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L39"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L35"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L43"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L45"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L32"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L49"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L52"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L54"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L50"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L58"), [(TAtom "chk0"); (TAtom "iw_2.v4"); (TAtom "v0")]); ((TAtom "iw_2.L60"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "iw_2.L6"), []); ((TAtom "iw_3.start"), [(TAtom "chk0"); (TAtom "v0")]); ((TAtom "L13"), []); ((TAtom "L15"), []); ((TAtom "L22"), []); ((TAtom "L23"), [])].

(** Each access records its instruction index, address, byte offset, optional width,
    read and write flags, optional root temporary and optional offset from that root.
    A local address names an invocation-local object, not a pointer temporary.
    Variable-sized runtime accesses have no fixed width. *)
Definition footprint : list (name * list (N * term * Z * option Z * bool * bool * option name * option Z)) :=
  [((TAtom "start"), [(2%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L2"), []); ((TAtom "iw_2.start"), [(1%N, (TApp "tmp" [(TAtom "iw_1.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "iw_2.L9"), []); ((TAtom "iw_2.L11"), []); ((TAtom "iw_2.L12"), []); ((TAtom "iw_2.L14"), []); ((TAtom "iw_2.L16"), []); ((TAtom "iw_2.L18"), [(2%N, (TApp "tmp" [(TAtom "iw_2.v19")]), (0), (Some 4), false, true, (Some (TAtom "iw_2.v19")), (Some (0))); (5%N, (TApp "tmp" [(TAtom "iw_2.iw_1.v3")]), (0), (Some 4), false, true, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "iw_2.L21"), []); ((TAtom "iw_2.L23"), []); ((TAtom "iw_2.L25"), []); ((TAtom "iw_2.L27"), []); ((TAtom "iw_2.L31"), []); ((TAtom "iw_2.L34"), []); ((TAtom "iw_2.L37"), []); ((TAtom "iw_2.L39"), []); ((TAtom "iw_2.L35"), []); ((TAtom "iw_2.L43"), []); ((TAtom "iw_2.L45"), []); ((TAtom "iw_2.L32"), []); ((TAtom "iw_2.L49"), []); ((TAtom "iw_2.L52"), []); ((TAtom "iw_2.L54"), []); ((TAtom "iw_2.L50"), []); ((TAtom "iw_2.L58"), []); ((TAtom "iw_2.L60"), []); ((TAtom "iw_2.L6"), []); ((TAtom "iw_3.start"), [(2%N, (TApp "tmp" [(TAtom "iw_3.v3")]), (0), (Some 4), true, false, (Some (TAtom "v0")), (Some (32)))]); ((TAtom "L13"), []); ((TAtom "L15"), [(2%N, (TApp "tmp" [(TAtom "v25")]), (0), (Some 8), true, false, (Some (TAtom "v0")), (Some (8))); (4%N, (TApp "tmp" [(TAtom "v25")]), (8), (Some 8), true, false, (Some (TAtom "v0")), (Some (16)))]); ((TAtom "L22"), []); ((TAtom "L23"), [])].

End fn___printf_buffer_flush.

(** Projection keeps temporary sets and access records out of the membership computation. *)
Definition block_labels : list (string * list name) := Eval lazy in
  [("__printf_buffer_write", app (map fst fn___printf_buffer_write.live_in) (app (map fst fn___printf_buffer_write.live_out) (map fst fn___printf_buffer_write.footprint))); ("__printf_buffer_flush", app (map fst fn___printf_buffer_flush.live_in) (app (map fst fn___printf_buffer_flush.live_out) (map fst fn___printf_buffer_flush.footprint)))].

(** The source sidecar projects these labels from the decoded module, not from the hint tables. *)
Lemma labels_valid :
  forallb (fun row =>
    match find (fun entry => String.eqb (fst entry) (fst row)) PrintfBufferIoSrc.source_blocks with
    | Some (_, Some labels) => forallb (fun l => existsb (name_eqb l) labels) (snd row)
    | _ => false
    end) block_labels = true.
Proof. vm_compute. reflexivity. Qed.

End PrintfBufferIoBlocks.
