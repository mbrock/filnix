(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioCloseItCode.
Import ListNotations.
Open Scope string_scope.

Module LibioCloseItSrc.

Module fn__IO_file_close_maybe_unlink.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 129%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 133%nat)); ((TAtom "L5"), ("fileops.c", 134%nat)); ((TAtom "L7"), ("fileops.c", 136%nat)); ((TAtom "L23"), ("fileops.c", 136%nat)); ((TAtom "L24"), ("fileops.c", 136%nat)); ((TAtom "L16"), ("fileops.c", 138%nat)); ((TAtom "L31"), ("fileops.c", 138%nat)); ((TAtom "L32"), ("fileops.c", 138%nat)); ((TAtom "L17"), ("fileops.c", 139%nat)); ((TAtom "L81"), ("fileops.c", 139%nat)); ((TAtom "L86"), ("fileops.c", 139%nat)); ((TAtom "L92"), ("fileops.c", 139%nat)); ((TAtom "L87"), ("fileops.c", 139%nat)); ((TAtom "L110"), ("fileops.c", 139%nat)); ((TAtom "L118"), ("fileops.c", 139%nat)); ((TAtom "L82"), ("fileops.c", 139%nat)); ((TAtom "L74"), ("fileops.c", 159%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 159%nat)); ((TAtom "L147"), ("fileops.c", 162%nat)); ((TAtom "L155"), ("fileops.c", 162%nat)); ((TAtom "L148"), ("fileops.c", 167%nat)); ((TAtom "L161"), ("fileops.c", 168%nat)); ((TAtom "L163"), ("fileops.c", 159%nat)); ((TAtom "iw_2.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_2.join"), ("fileops.c", 169%nat)); ((TAtom "L191"), ("fileops.c", 169%nat)); ((TAtom "L192"), ("fileops.c", 169%nat)); ((TAtom "L179"), ("fileops.c", 169%nat)); ((TAtom "L18"), ("fileops.c", 132%nat)); ((TAtom "L202"), ("fileops.c", 177%nat)); ((TAtom "iw_3.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_3.join"), ("fileops.c", 177%nat)); ((TAtom "L204"), ("fileops.c", 177%nat)); ((TAtom "L221"), ("fileops.c", 183%nat)); ((TAtom "L228"), ("fileops.c", 184%nat)); ((TAtom "L230"), ("fileops.c", 185%nat)); ((TAtom "L223"), ("fileops.c", 189%nat)); ((TAtom "L277"), ("fileops.c", 194%nat)); ((TAtom "L279"), ("fileops.c", 197%nat)); ((TAtom "L299"), ("fileops.c", 201%nat)); ((TAtom "L300"), ("fileops.c", 201%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "iw_2.v0"), "vtable"); ((TAtom "iw_2.v13"), "offset"); ((TAtom "iw_2.v18"), "vtable"); ((TAtom "iw_2.v3"), "vtable"); ((TAtom "iw_2.v4"), "ptr"); ((TAtom "iw_2.v6"), "ptr"); ((TAtom "iw_2.v9"), "offset"); ((TAtom "iw_3.v0"), "vtable"); ((TAtom "iw_3.v13"), "offset"); ((TAtom "iw_3.v18"), "vtable"); ((TAtom "iw_3.v3"), "vtable"); ((TAtom "iw_3.v4"), "ptr"); ((TAtom "iw_3.v6"), "ptr"); ((TAtom "iw_3.v9"), "offset"); ((TAtom "pr.1"), "flush_status"); ((TAtom "pr.2"), "flush_status"); ((TAtom "pr.3"), "flush_status"); ((TAtom "pr.4"), "flush_status"); ((TAtom "pr.5"), "o"); ((TAtom "v0"), "fp"); ((TAtom "v112"), "fp"); ((TAtom "v120"), "fp"); ((TAtom "v124"), "fp"); ((TAtom "v139"), "fp"); ((TAtom "v145"), "fp"); ((TAtom "v146"), "o"); ((TAtom "v150"), "o"); ((TAtom "v158"), "__libc_errno"); ((TAtom "v160"), "flush_status"); ((TAtom "v164"), "fp"); ((TAtom "v167"), "o"); ((TAtom "v168"), "fp"); ((TAtom "v171"), "fp"); ((TAtom "v177"), "o"); ((TAtom "v181"), "fp"); ((TAtom "v187"), "fp"); ((TAtom "v188"), "o"); ((TAtom "v19"), "fp"); ((TAtom "v194"), "__libc_errno"); ((TAtom "v199"), "flush_status"); ((TAtom "v2"), "unlink"); ((TAtom "v200"), "fp"); ((TAtom "v205"), "fp"); ((TAtom "v212"), "fp"); ((TAtom "v218"), "fp"); ((TAtom "v220"), "close_status"); ((TAtom "v224"), "fp"); ((TAtom "v231"), "fp"); ((TAtom "v239"), "fp"); ((TAtom "v240"), "fp"); ((TAtom "v241"), "fp"); ((TAtom "v245"), "fp"); ((TAtom "v248"), "fp"); ((TAtom "v25"), "fp"); ((TAtom "v252"), "fp"); ((TAtom "v256"), "fp"); ((TAtom "v260"), "fp"); ((TAtom "v264"), "fp"); ((TAtom "v265"), "fp"); ((TAtom "v267"), "fp"); ((TAtom "v269"), "fp"); ((TAtom "v271"), "fp"); ((TAtom "v273"), "fp"); ((TAtom "v275"), "fp"); ((TAtom "v280"), "unlink"); ((TAtom "v281"), "fp"); ((TAtom "v282"), "fp"); ((TAtom "v287"), "fp"); ((TAtom "v291"), "fp"); ((TAtom "v294"), "fp"); ((TAtom "v301"), "close_status"); ((TAtom "v302"), "close_status"); ((TAtom "v303"), "flush_status"); ((TAtom "v34"), "fp"); ((TAtom "v38"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v42"), "fp"); ((TAtom "v45"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v63"), "fp"); ((TAtom "v73"), "flush_status"); ((TAtom "v77"), "fp"); ((TAtom "v8"), "fp"); ((TAtom "v83"), "fp"); ((TAtom "v88"), "fp"); ((TAtom "v94"), "fp"); ((TAtom "v97"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_file_close_maybe_unlink") (code_module libiocloseit_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_file_close_maybe_unlink.

End LibioCloseItSrc.
