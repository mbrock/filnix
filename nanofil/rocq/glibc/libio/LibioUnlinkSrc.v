(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool.
From Glibc Require Import CodePrelude LibioUnlinkCode.
Import ListNotations.
Open Scope string_scope.

Module LibioUnlinkSrc.

Module fn__IO_new_file_finish.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("fileops.c", 211%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("fileops.c", 214%nat)); ((TAtom "L4"), ("fileops.c", 216%nat)); ((TAtom "L12"), ("fileops.c", 216%nat)); ((TAtom "L13"), ("fileops.c", 216%nat)); ((TAtom "L14"), ("fileops.c", 217%nat)); ((TAtom "L55"), ("fileops.c", 218%nat)); ((TAtom "iw_1.L10"), ("./libioP.h", 1049%nat)); ((TAtom "iw_1.join"), ("fileops.c", 218%nat)); ((TAtom "L6"), ("fileops.c", 220%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "iw_1.v0"), "vtable"); ((TAtom "iw_1.v13"), "offset"); ((TAtom "iw_1.v18"), "vtable"); ((TAtom "iw_1.v3"), "vtable"); ((TAtom "iw_1.v4"), "ptr"); ((TAtom "iw_1.v6"), "ptr"); ((TAtom "iw_1.v9"), "offset"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v19"), "fp"); ((TAtom "v2"), "dummy"); ((TAtom "v20"), "fp"); ((TAtom "v23"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v33"), "fp"); ((TAtom "v34"), "fp"); ((TAtom "v39"), "fp"); ((TAtom "v44"), "fp"); ((TAtom "v58"), "fp"); ((TAtom "v62"), "fp"); ((TAtom "v68"), "fp"); ((TAtom "v7"), "fp"); ((TAtom "v70"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "_IO_new_file_finish") (code_module libiounlink_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn__IO_new_file_finish.

Module fn___GI__IO_un_link.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 65%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 72%nat)); ((TAtom "L2"), ("genops.c", 72%nat)); ((TAtom "L31"), ("genops.c", 73%nat)); ((TAtom "L32"), ("genops.c", 73%nat)); ((TAtom "L25"), ("genops.c", 73%nat)); ((TAtom "L26"), ("genops.c", 73%nat)); ((TAtom "L45"), ("genops.c", 73%nat)); ((TAtom "L65"), ("genops.c", 73%nat)); ((TAtom "L66"), ("genops.c", 73%nat)); ((TAtom "L70"), ("genops.c", 73%nat)); ((TAtom "L59"), ("genops.c", 73%nat)); ((TAtom "L46"), ("genops.c", 73%nat)); ((TAtom "L22"), ("genops.c", 74%nat)); ((TAtom "L96"), ("genops.c", 75%nat)); ((TAtom "L107"), ("genops.c", 75%nat)); ((TAtom "L108"), ("genops.c", 75%nat)); ((TAtom "L101"), ("genops.c", 75%nat)); ((TAtom "L102"), ("genops.c", 75%nat)); ((TAtom "L127"), ("genops.c", 75%nat)); ((TAtom "L151"), ("genops.c", 75%nat)); ((TAtom "L152"), ("genops.c", 75%nat)); ((TAtom "L156"), ("genops.c", 75%nat)); ((TAtom "L145"), ("genops.c", 75%nat)); ((TAtom "L128"), ("genops.c", 75%nat)); ((TAtom "L91"), ("genops.c", 77%nat)); ((TAtom "L185"), ("genops.c", 81%nat)); ((TAtom "L199"), ("genops.c", 85%nat)); ((TAtom "L179"), ("genops.c", 96%nat)); ((TAtom "L262"), ("genops.c", 98%nat)); ((TAtom "L271"), ("genops.c", 98%nat)); ((TAtom "L272"), ("genops.c", 98%nat)); ((TAtom "L265"), ("genops.c", 98%nat)); ((TAtom "L266"), ("genops.c", 98%nat)); ((TAtom "L288"), ("genops.c", 98%nat)); ((TAtom "L309"), ("genops.c", 98%nat)); ((TAtom "L310"), ("genops.c", 98%nat)); ((TAtom "L321"), ("genops.c", 98%nat)); ((TAtom "L289"), ("genops.c", 98%nat)); ((TAtom "L257"), ("genops.c", 99%nat)); ((TAtom "L348"), ("genops.c", 100%nat)); ((TAtom "L349"), ("genops.c", 100%nat)); ((TAtom "L342"), ("genops.c", 100%nat)); ((TAtom "L343"), ("genops.c", 100%nat)); ((TAtom "L359"), ("genops.c", 100%nat)); ((TAtom "L374"), ("genops.c", 100%nat)); ((TAtom "L375"), ("genops.c", 100%nat)); ((TAtom "L386"), ("genops.c", 100%nat)); ((TAtom "L360"), ("genops.c", 100%nat)); ((TAtom "L401"), ("genops.c", 101%nat)); ((TAtom "L4"), ("genops.c", 65%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "f"); ((TAtom "pr.2"), "_cleanup_start_doit"); ((TAtom "v0"), "fp"); ((TAtom "v100"), "__self"); ((TAtom "v105"), "__libc_single_threaded_internal"); ((TAtom "v109"), "fp"); ((TAtom "v119"), "fp"); ((TAtom "v12"), "_cleanup_routine"); ((TAtom "v122"), "fp"); ((TAtom "v126"), "__self"); ((TAtom "v130"), "fp"); ((TAtom "v135"), "__self"); ((TAtom "v140"), "fp"); ((TAtom "v142"), "__futex"); ((TAtom "v147"), "__futex"); ((TAtom "v148"), "__atg3_old"); ((TAtom "v149"), "__atg3_old"); ((TAtom "v164"), "__futex"); ((TAtom "v165"), "__futex"); ((TAtom "v166"), "fp"); ((TAtom "v17"), "_cleanup_start_doit"); ((TAtom "v170"), "__self"); ((TAtom "v171"), "fp"); ((TAtom "v18"), "_cleanup_routine"); ((TAtom "v181"), "_IO_list_all"); ((TAtom "v19"), "_cleanup_start_doit"); ((TAtom "v190"), "fp"); ((TAtom "v192"), "pr"); ((TAtom "v194"), "fp"); ((TAtom "v196"), "nx"); ((TAtom "v197"), "pr"); ((TAtom "v198"), "nx"); ((TAtom "v202"), "nx"); ((TAtom "v206"), "nx"); ((TAtom "v208"), "pr"); ((TAtom "v212"), "fp"); ((TAtom "v214"), "_IO_list_all"); ((TAtom "v220"), "_IO_list_all"); ((TAtom "v222"), "_IO_list_all"); ((TAtom "v224"), "_IO_list_all"); ((TAtom "v225"), "f"); ((TAtom "v230"), "f"); ((TAtom "v237"), "f"); ((TAtom "v239"), "fp"); ((TAtom "v24"), "__self"); ((TAtom "v243"), "f"); ((TAtom "v244"), "fp"); ((TAtom "v248"), "f"); ((TAtom "v250"), "f"); ((TAtom "v251"), "fp"); ((TAtom "v258"), "fp"); ((TAtom "v269"), "__libc_single_threaded_internal"); ((TAtom "v273"), "fp"); ((TAtom "v281"), "fp"); ((TAtom "v285"), "fp"); ((TAtom "v29"), "__libc_single_threaded_internal"); ((TAtom "v291"), "fp"); ((TAtom "v297"), "fp"); ((TAtom "v302"), "fp"); ((TAtom "v304"), "__futex"); ((TAtom "v307"), "__futex"); ((TAtom "v311"), "__oldval"); ((TAtom "v317"), "__oldval"); ((TAtom "v329"), "__futex"); ((TAtom "v330"), "__futex"); ((TAtom "v331"), "__private"); ((TAtom "v332"), "fp"); ((TAtom "v346"), "__libc_single_threaded_internal"); ((TAtom "v372"), "__futex"); ((TAtom "v376"), "__oldval"); ((TAtom "v382"), "__oldval"); ((TAtom "v394"), "__futex"); ((TAtom "v395"), "__futex"); ((TAtom "v396"), "__private"); ((TAtom "v404"), "_cleanup_start_doit"); ((TAtom "v408"), "_cleanup_routine"); ((TAtom "v44"), "__self"); ((TAtom "v5"), "fp"); ((TAtom "v51"), "__self"); ((TAtom "v61"), "__futex"); ((TAtom "v62"), "__atg3_old"); ((TAtom "v63"), "__atg3_old"); ((TAtom "v78"), "__futex"); ((TAtom "v79"), "__futex"); ((TAtom "v82"), "__self"); ((TAtom "v88"), "fp"); ((TAtom "v92"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L309"); (TAtom "L374")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_un_link") (code_module libiounlink_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_un_link.

Module fn___GI__IO_default_finish.

(** This location identifies the C function definition when its context records contain one. *)
Definition source : option (string * nat) := Some ("genops.c", 626%nat).

(** Each entry records the first located site in a block, in execution order. *)
Definition block_src : list (name * (string * nat)) :=
  [((TAtom "start"), ("genops.c", 630%nat)); ((TAtom "L13"), ("genops.c", 630%nat)); ((TAtom "L14"), ("genops.c", 630%nat)); ((TAtom "L5"), ("genops.c", 632%nat)); ((TAtom "L7"), ("genops.c", 636%nat)); ((TAtom "L31"), ("genops.c", 629%nat)); ((TAtom "L32"), ("genops.c", 637%nat)); ((TAtom "L34"), ("genops.c", 639%nat)); ((TAtom "L43"), ("genops.c", 640%nat)); ((TAtom "L45"), ("genops.c", 642%nat)); ((TAtom "L55"), ("genops.c", 645%nat)); ((TAtom "L56"), ("genops.c", 626%nat))].

(** These recorded temporaries have a primary value hint naming their C declaration. *)
Definition temp_names : list (name * string) :=
  [((TAtom "pr.1"), "mark"); ((TAtom "v0"), "fp"); ((TAtom "v15"), "fp"); ((TAtom "v2"), "dummy"); ((TAtom "v21"), "fp"); ((TAtom "v24"), "fp"); ((TAtom "v26"), "fp"); ((TAtom "v28"), "fp"); ((TAtom "v30"), "mark"); ((TAtom "v35"), "mark"); ((TAtom "v39"), "mark"); ((TAtom "v41"), "mark"); ((TAtom "v42"), "mark"); ((TAtom "v46"), "fp"); ((TAtom "v52"), "fp"); ((TAtom "v53"), "fp"); ((TAtom "v57"), "fp"); ((TAtom "v8"), "fp")].

(** The compiler finds these reachable natural-loop headers using dominators. *)
Definition loop_heads : list name := [(TAtom "L31")].

(** Computation checks block membership without trusting the source hints or the loop analysis. *)
Lemma labels_valid :
  match find_direct (TAtom "__GI__IO_default_finish") (code_module libiounlink_term) with
  | Some (Defined f) =>
      forallb (fun l => existsb (fun b => name_eqb l (b_label b)) (fn_blocks f))
        (map fst block_src ++ loop_heads) = true
  | _ => False
  end.
Proof. vm_compute. reflexivity. Qed.

End fn___GI__IO_default_finish.

End LibioUnlinkSrc.
