(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import LibioCloseItCode.
Module LibioCloseItSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "fileops.c".

Module fn__IO_file_close_maybe_unlink.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 129%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 133%N)); ((TAtom "L5"), (file_1, 134%N)); ((TAtom "L7"), (file_1, 136%N)); ((TAtom "L23"), (file_1, 136%N)); ((TAtom "L24"), (file_1, 136%N)); ((TAtom "L16"), (file_1, 138%N)); ((TAtom "L31"), (file_1, 138%N)); ((TAtom "L32"), (file_1, 138%N)); ((TAtom "L17"), (file_1, 139%N)); ((TAtom "L81"), (file_1, 139%N)); ((TAtom "L86"), (file_1, 139%N)); ((TAtom "L92"), (file_1, 139%N)); ((TAtom "L87"), (file_1, 139%N)); ((TAtom "L110"), (file_1, 139%N)); ((TAtom "L118"), (file_1, 139%N)); ((TAtom "L82"), (file_1, 139%N)); ((TAtom "L74"), (file_1, 159%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_1, 159%N)); ((TAtom "L147"), (file_1, 162%N)); ((TAtom "L155"), (file_1, 162%N)); ((TAtom "L148"), (file_1, 167%N)); ((TAtom "L161"), (file_1, 168%N)); ((TAtom "L163"), (file_1, 159%N)); ((TAtom "iw_2.L10"), (file_0, 1049%N)); ((TAtom "iw_2.join"), (file_1, 169%N)); ((TAtom "L191"), (file_1, 169%N)); ((TAtom "L192"), (file_1, 169%N)); ((TAtom "L179"), (file_1, 169%N)); ((TAtom "L18"), (file_1, 132%N)); ((TAtom "L202"), (file_1, 177%N)); ((TAtom "iw_3.L10"), (file_0, 1049%N)); ((TAtom "iw_3.join"), (file_1, 177%N)); ((TAtom "L204"), (file_1, 177%N)); ((TAtom "L221"), (file_1, 183%N)); ((TAtom "L228"), (file_1, 184%N)); ((TAtom "L230"), (file_1, 185%N)); ((TAtom "L223"), (file_1, 189%N)); ((TAtom "L277"), (file_1, 194%N)); ((TAtom "L279"), (file_1, 197%N)); ((TAtom "L299"), (file_1, 201%N)); ((TAtom "L300"), (file_1, 201%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "vtable"); ((TAtom "iw_3.v13"), "offset"); ((TAtom "iw_3.v18"), "vtable"); ((TAtom "iw_3.v3"), "vtable"); ((TAtom "iw_3.v4"), "ptr"); ((TAtom "iw_3.v6"), "ptr"); ((TAtom "iw_3.v9"), "offset"); ((TAtom "pr.1"), "flush_status"); ((TAtom "pr.2"), "flush_status"); ((TAtom "pr.3"), "flush_status"); ((TAtom "pr.4"), "flush_status"); ((TAtom "pr.5"), "o"); ((TAtom "v0"), "fp"); ((TAtom "v112"), "fp"); ((TAtom "v120"), "fp"); ((TAtom "v124"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v145"), "fp"); ((TAtom "v146"), "o"); ((TAtom "v150"), "o"); ((TAtom "v158"), "__libc_errno"); ((TAtom "v160"), "flush_status"); ((TAtom "v164"), "fp"); ((TAtom "v167"), "o"); ((TAtom "v168"), "fp"); ((TAtom "v171"), "fp"); ((TAtom "v177"), "o"); ((TAtom "v181"), "fp"); ((TAtom "v187"), "fp"); ((TAtom "v188"), "o"); ((TAtom "v19"), "fp"); ((TAtom "v194"), "__libc_errno"); ((TAtom "v199"), "flush_status"); ((TAtom "v2"), "unlink"); ((TAtom "v200"), "fp"); ((TAtom "v205"), "fp"); ((TAtom "v212"), "fp"); ((TAtom "v218"), "fp"); ((TAtom "v220"), "close_status"); ((TAtom "v224"), "fp"); ((TAtom "v231"), "fp"); ((TAtom "v239"), "fp"); ((TAtom "v240"), "fp"); ((TAtom "v241"), "fp"); ((TAtom "v245"), "fp"); ((TAtom "v248"), "fp"); ((TAtom "v25"), "fp"); ((TAtom "v252"), "fp"); ((TAtom "v256"), "fp"); ((TAtom "v260"), "fp"); ((TAtom "v264"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v267"), "fp"); ((TAtom "v269"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v273"), "fp"); ((TAtom "v275"), "fp"); ((TAtom "v280"), "unlink"); ((TAtom "v281"), "fp"); ((TAtom "v282"), "fp"); ((TAtom "v287"), "fp"); ((TAtom "v291"), "fp"); ((TAtom "v294"), "fp"); ((TAtom "v301"), "close_status"); ((TAtom "v302"), "close_status"); ((TAtom "v303"), "flush_status"); ((TAtom "v34"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v42"), "fp"); ((TAtom "v45"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v73"), "flush_status"); ((TAtom "v77"), "fp"); ((TAtom "v8"), "fp"); ((TAtom "v83"), "fp"); ((TAtom "v88"), "fp"); ((TAtom "v94"), "fp"); ((TAtom "v97"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_file_close_maybe_unlink.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libiocloseit_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["_IO_file_close_maybe_unlink"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("_IO_file_close_maybe_unlink", app (map fst fn__IO_file_close_maybe_unlink.block_src) fn__IO_file_close_maybe_unlink.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End LibioCloseItSrc.
