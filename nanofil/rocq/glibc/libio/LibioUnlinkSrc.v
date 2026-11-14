(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


From Glibc Require Import LibioUnlinkCode.
Module LibioUnlinkSrc.

Definition file_0 : string := "./libioP.h".

Definition file_1 : string := "fileops.c".

Definition file_2 : string := "genops.c".

Module fn__IO_new_file_finish.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_1, 211%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_1, 214%N)); ((TAtom "L4"), (file_1, 216%N)); ((TAtom "L12"), (file_1, 216%N)); ((TAtom "L13"), (file_1, 216%N)); ((TAtom "L14"), (file_1, 217%N)); ((TAtom "L55"), (file_1, 218%N)); ((TAtom "iw_1.L10"), (file_0, 1049%N)); ((TAtom "iw_1.join"), (file_1, 218%N)); ((TAtom "L6"), (file_1, 220%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "dummy"); ((TAtom "v20"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v44"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v62"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v70"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

End fn__IO_new_file_finish.

Module fn___GI__IO_un_link.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 65%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 72%N)); ((TAtom "L2"), (file_2, 72%N)); ((TAtom "L31"), (file_2, 73%N)); ((TAtom "L32"), (file_2, 73%N)); ((TAtom "L25"), (file_2, 73%N)); ((TAtom "L26"), (file_2, 73%N)); ((TAtom "L45"), (file_2, 73%N)); ((TAtom "L65"), (file_2, 73%N)); ((TAtom "L66"), (file_2, 73%N)); ((TAtom "L70"), (file_2, 73%N)); ((TAtom "L59"), (file_2, 73%N)); ((TAtom "L46"), (file_2, 73%N)); ((TAtom "L22"), (file_2, 74%N)); ((TAtom "L96"), (file_2, 75%N)); ((TAtom "L107"), (file_2, 75%N)); ((TAtom "L108"), (file_2, 75%N)); ((TAtom "L101"), (file_2, 75%N)); ((TAtom "L102"), (file_2, 75%N)); ((TAtom "L127"), (file_2, 75%N)); ((TAtom "L151"), (file_2, 75%N)); ((TAtom "L152"), (file_2, 75%N)); ((TAtom "L156"), (file_2, 75%N)); ((TAtom "L145"), (file_2, 75%N)); ((TAtom "L128"), (file_2, 75%N)); ((TAtom "L91"), (file_2, 77%N)); ((TAtom "L185"), (file_2, 81%N)); ((TAtom "L199"), (file_2, 85%N)); ((TAtom "L179"), (file_2, 96%N)); ((TAtom "L262"), (file_2, 98%N)); ((TAtom "L271"), (file_2, 98%N)); ((TAtom "L272"), (file_2, 98%N)); ((TAtom "L265"), (file_2, 98%N)); ((TAtom "L266"), (file_2, 98%N)); ((TAtom "L288"), (file_2, 98%N)); ((TAtom "L309"), (file_2, 98%N)); ((TAtom "L310"), (file_2, 98%N)); ((TAtom "L321"), (file_2, 98%N)); ((TAtom "L289"), (file_2, 98%N)); ((TAtom "L257"), (file_2, 99%N)); ((TAtom "L348"), (file_2, 100%N)); ((TAtom "L349"), (file_2, 100%N)); ((TAtom "L342"), (file_2, 100%N)); ((TAtom "L343"), (file_2, 100%N)); ((TAtom "L359"), (file_2, 100%N)); ((TAtom "L374"), (file_2, 100%N)); ((TAtom "L375"), (file_2, 100%N)); ((TAtom "L386"), (file_2, 100%N)); ((TAtom "L360"), (file_2, 100%N)); ((TAtom "L401"), (file_2, 101%N)); ((TAtom "L4"), (file_2, 65%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "f"); ((TAtom "pr.2"), "_cleanup_start_doit"); ((TAtom "v0"), "fp"); ((TAtom "v100"), "__self"); ((TAtom "v105"), "__libc_single_threaded_internal"); ((TAtom "v109"), "fp"); ((TAtom "v119"), "fp"); ((TAtom "v12"), "_cleanup_routine"); ((TAtom "v122"), "fp"); ((TAtom "v126"), "__self"); ((TAtom "v130"), "fp"); ((TAtom "v135"), "__self"); ((TAtom "v140"), "fp"); ((TAtom "v142"), "__futex"); ((TAtom "v147"), "__futex"); ((TAtom "v148"), "__atg3_old"); ((TAtom "v149"), "__atg3_old"); ((TAtom "v164"), "__futex"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "fp"); ((TAtom "v17"), "_cleanup_start_doit"); ((TAtom "v170"), "__self"); ((TAtom "v171"), "fp"); ((TAtom "v18"), "_cleanup_routine"); ((TAtom "v181"), "_IO_list_all"); ((TAtom "v19"), "_cleanup_start_doit"); ((TAtom "v190"), "fp"); ((TAtom "v192"), "pr"); ((TAtom "v194"), "fp"); ((TAtom "v196"), "nx"); ((TAtom "v197"), "pr"); ((TAtom "v198"), "nx"); ((TAtom "v202"), "nx"); ((TAtom "v206"), "nx"); ((TAtom "v208"), "pr"); ((TAtom "v212"), "fp"); ((TAtom "v214"), "_IO_list_all"); ((TAtom "v220"), "_IO_list_all"); ((TAtom "v222"), "_IO_list_all"); ((TAtom "v224"), "_IO_list_all"); ((TAtom "v225"), "f"); ((TAtom "v230"), "f"); ((TAtom "v237"), "f"); ((TAtom "v239"), "fp"); ((TAtom "v24"), "__self"); ((TAtom "v243"), "f"); ((TAtom "v244"), "fp"); ((TAtom "v248"), "f"); ((TAtom "v250"), "f"); ((TAtom "v251"), "fp"); ((TAtom "v258"), "fp"); ((TAtom "v269"), "__libc_single_threaded_internal"); ((TAtom "v273"), "fp"); ((TAtom "v281"), "fp"); ((TAtom "v285"), "fp"); ((TAtom "v29"), "__libc_single_threaded_internal"); ((TAtom "v291"), "fp"); ((TAtom "v297"), "fp"); ((TAtom "v302"), "fp"); ((TAtom "v304"), "__futex"); ((TAtom "v307"), "__futex"); ((TAtom "v311"), "__oldval"); ((TAtom "v317"), "__oldval"); ((TAtom "v329"), "__futex"); ((TAtom "v330"), "__futex"); ((TAtom "v331"), "__private"); ((TAtom "v332"), "fp"); ((TAtom "v346"), "__libc_single_threaded_internal"); ((TAtom "v372"), "__futex"); ((TAtom "v376"), "__oldval"); ((TAtom "v382"), "__oldval"); ((TAtom "v394"), "__futex"); ((TAtom "v395"), "__futex"); ((TAtom "v396"), "__private"); ((TAtom "v404"), "_cleanup_start_doit"); ((TAtom "v408"), "_cleanup_routine"); ((TAtom "v44"), "__self"); ((TAtom "v5"), "fp"); ((TAtom "v51"), "__self"); ((TAtom "v61"), "__futex"); ((TAtom "v62"), "__atg3_old"); ((TAtom "v63"), "__atg3_old"); ((TAtom "v78"), "__futex"); ((TAtom "v79"), "__futex"); ((TAtom "v82"), "__self"); ((TAtom "v88"), "fp"); ((TAtom "v92"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L309"); (TAtom "L374")].

End fn___GI__IO_un_link.

Module fn___GI__IO_default_finish.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * N) := Some (file_2, 626%N).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * N)) :=
  [((TAtom "start"), (file_2, 630%N)); ((TAtom "L13"), (file_2, 630%N)); ((TAtom "L14"), (file_2, 630%N)); ((TAtom "L5"), (file_2, 632%N)); ((TAtom "L7"), (file_2, 636%N)); ((TAtom "L31"), (file_2, 629%N)); ((TAtom "L32"), (file_2, 637%N)); ((TAtom "L34"), (file_2, 639%N)); ((TAtom "L43"), (file_2, 640%N)); ((TAtom "L45"), (file_2, 642%N)); ((TAtom "L55"), (file_2, 645%N)); ((TAtom "L56"), (file_2, 626%N))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "mark"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v2"), "dummy"); ((TAtom "v21"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v28"), "fp"); ((TAtom "v30"), "mark"); ((TAtom "v35"), "mark"); ((TAtom "v39"), "mark"); ((TAtom "v41"), "mark"); ((TAtom "v42"), "mark"); ((TAtom "v46"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v57"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L31")].

End fn___GI__IO_default_finish.

(** Projection keeps instruction bodies out of the VM code used by the membership check. *)
Definition source_blocks : list (string * option (list name)) := Eval lazy in
  map (fun n => (n,
    match find_direct (TAtom n) libiounlink_module with
    | Some (Defined f) => Some (map b_label (fn_blocks f))
    | _ => None
    end)) ["_IO_new_file_finish"; "__GI__IO_un_link"; "__GI__IO_default_finish"].

(** One computation rejects missing functions and stale labels across all tables in this fixture. *)
Lemma labels_valid :
  forallb (fun row =>
  match find (fun entry => String.eqb (fst entry) (fst row)) source_blocks with
  | Some (_, Some labels) =>
      forallb (fun l => existsb (name_eqb l) labels)
        (snd row)
  | _ => false
  end) [("_IO_new_file_finish", app (map fst fn__IO_new_file_finish.block_src) fn__IO_new_file_finish.loop_heads); ("__GI__IO_un_link", app (map fst fn___GI__IO_un_link.block_src) fn___GI__IO_un_link.loop_heads); ("__GI__IO_default_finish", app (map fst fn___GI__IO_default_finish.block_src) fn___GI__IO_default_finish.loop_heads)] = true.
Proof. vm_compute. reflexivity. Qed.

End LibioUnlinkSrc.
