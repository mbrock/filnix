(** Fil-C defers the global constructors of every library until the
    program asks for them. `c: __libc_start_main` makes that request by
    calling libpizlo's `c: zrun_deferred_global_ctors`, which runs each
    deferred constructor once, in the order the dynamic loader deferred
    them, and panics when it is called a second time. A linked image
    records the constructors as `init(ctor)` items but not their order, so
    a proof that starts at `c: __libc_start_main` has to cover every order.
    This module defines the function the model runs for that call.

    ## What libpizlo runs

    The runtime keeps the constructors in an array and the program's
    arguments in its own saved globals, as the pinned
    `libpas/src/libpas/filc_runtime.c` shows.

    ```c
    void filc_run_deferred_global_ctors(filc_thread* my_thread)
    {
        FILC_CHECK(!filc_did_run_deferred_global_ctors, NULL,
                   "cannot run deferred global constructors twice.");
        filc_did_run_deferred_global_ctors = true;
        for (index = 0; index < filc_deferred_global_ctors_size; ++index)
            run_global_ctor(my_thread, filc_deferred_global_ctors[index]);
    }
    ```

    Each constructor receives the arguments that program start saved. The
    runtime reads them with `c: filc_get_user_argc()`,
    `c: filc_get_user_argv()` and `c: filc_get_user_environ()`, so libc
    cannot change what a constructor sees. A constructor that takes no
    arguments ignores them.

    ## The model's runner

    The model appends three items to the decoded image. A read-only table
    holds argc, argv, environ and one function pointer per constructor, a
    writable flag records whether the runner has run, and the function
    [ctor_runner] reads both. The image's own initial memory leaves the
    table zero. The allowed starting states put the saved arguments and
    the constructor pointers, in any order, into it. No C code names
    either item, so only the runner can reach them. Appending the items
    after every other item keeps every existing address.

    The runner traps through [JUnreachable] when the flag is set, as the
    runtime's check panics. Otherwise it sets the flag and calls each
    table entry with the three arguments. The number of constructors is
    fixed by the image, so the calls are unrolled rather than looped. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Semantics Run.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## The constructors of an image

    The linker keeps each constructor as an `init(ctor)` data item that
    holds one pointer to its function. These definitions collect those
    functions from a decoded module. *)

(** This function returns the function that a constructor item points
    to, and it returns nothing for any other item. *)
Definition ctor_target (it : item) : option name :=
  match it with
  | IData _ (LInit (TAtom "ctor") _) _ [Sym f 0] => Some f
  | _ => None
  end.

(** This list collects the constructor functions of a module in the
    order of its items. *)
Definition ctor_names (md : module) : list name :=
  flat_map (fun it => match ctor_target it with Some f => [f] | None => [] end) md.

(** ## The runner

    The runner needs a private table and a private flag, and it needs a
    function body that reads them. This section writes all three in the
    model's IR. As compiled code does, the body copies each global's
    address into a temporary before checking it, because the validator
    accepts checks only on temporaries. It keeps the access proofs for
    the flag and the table, and the three saved arguments, in
    temporaries. *)

(** This name is the libpizlo symbol that `c: __libc_start_main` calls. *)
Definition ctor_runner_name : name := TAtom "zrun_deferred_global_ctors".

(** This name labels the read-only table that holds the saved arguments
    and the constructor pointers. *)
Definition ctor_table_name : name := TAtom "zrun_deferred_global_ctors#table".

(** This name labels the flag that records whether a first run has
    completed. *)
Definition ctor_flag_name : name := TAtom "zrun_deferred_global_ctors#did_run".

(** The table holds argc at offset 0, argv at 8, environ at 16, and the
    i-th constructor pointer at 24 + 8 i. *)
Definition ctor_table_size (n : nat) : Z := 24 + 8 * Z.of_nat n.

(** The runner reads every constructor pointer from the table before
    it calls the first one. A call ends the evidence of the table's
    check, so the validator would reject a table read after a call; the
    table is read-only, so reading it early changes nothing. *)
Definition ctor_load (i : nat) : inst :=
  Let (TApp "ctor" [TInt (Z.of_nat i)]) P (RawLoadPointer (24 + 8 * Z.of_nat i) load_effects) [Tmp (TAtom "table")].

(** Calling the i-th constructor takes two instructions: check that its
    pointer is a function entry, and call it with the saved arguments. A
    constructor with fewer parameters ignores the extra arguments, as in
    the runtime. *)
Definition ctor_call (i : nat) : list inst :=
  let p := TApp "ctor" [TInt (Z.of_nat i)] in
  let f := TApp "ctor_fn" [TInt (Z.of_nat i)] in
  [Let f F CheckFunction [Tmp p];
   RawCall CVoid (Tmp f) [Arg W (Tmp (TAtom "argc")); Arg P (Tmp (TAtom "argv")); Arg P (Tmp (TAtom "environ"))]].

(** This function is the runner for an image with n constructors. Its
    entry block reads the flag and branches. The block `twice` traps, and
    the block `run` sets the flag, reads the arguments and the n
    constructor pointers, and calls the constructors in table order. *)
Definition ctor_runner (n : nat) : func :=
  mkFunc ctor_runner_name (TAtom "export") RVoid []
    [mkBlock (TAtom "start") []
       [Let (TAtom "flag_ptr") P Copy [Global ctor_flag_name];
        Let (TAtom "flag") A (Check 0 1 Write 1) [Tmp (TAtom "flag_ptr")];
        Let (TAtom "done") W (RawLoad (LdNarrow Ub) 0) [Tmp (TAtom "flag")]]
       (JBranch (Tmp (TAtom "done")) (To (TAtom "twice")) (To (TAtom "run")));
     mkBlock (TAtom "twice") [] [] JUnreachable;
     mkBlock (TAtom "run") []
       (app [RawStore Wb 0 (Const 1) (Tmp (TAtom "flag"));
         Let (TAtom "table_ptr") P Copy [Global ctor_table_name];
         Let (TAtom "table") A (Check 0 (ctor_table_size n) Read 8) [Tmp (TAtom "table_ptr")];
         Let (TAtom "argc") W (RawLoad (LdNarrow Sw) 0) [Tmp (TAtom "table")];
         Let (TAtom "argv") P (RawLoadPointer 8 load_effects) [Tmp (TAtom "table")];
         Let (TAtom "environ") P (RawLoadPointer 16 load_effects) [Tmp (TAtom "table")]]
        (app (map ctor_load (seq 0 n)) (flat_map ctor_call (seq 0 n))))
       JRetVoid].

(** The model appends three items, which are the table, the flag and the
    runner. *)
Definition ctor_runner_items (n : nat) : list item :=
  [IData ctor_table_name (LRo (TAtom "local")) 8 [Zero (ctor_table_size n)];
   IData ctor_flag_name LLocal 8 [Zero 8];
   IFunc (ctor_runner n)].

(** This function appends the constructor runner to an image, after
    every other item. *)
Definition with_ctor_runner (md : module) : module :=
  app md (ctor_runner_items (length (ctor_names md))).

(** ## Checks on a linked image

    Appending the runner is safe for an image when no item already uses
    the three names, so that every lookup of an existing name is
    unchanged and the runner is the definition of its symbol. The checker
    below decides that by computation. *)

(** This function returns the name that an item defines. *)
Definition item_name (it : item) : name :=
  match it with IFunc f => fn_name f | IOutside n _ | IData n _ _ _ | IAlias n _ _ => n end.

(** No item of md uses a runner name. *)
Definition ctor_names_fresh (md : module) : bool :=
  forallb (fun it => negb (existsb (name_eqb (item_name it)) [ctor_runner_name; ctor_table_name; ctor_flag_name])) md.

(** With fresh names, a module followed by the runner items for k
    constructors defines the runner symbol as [ctor_runner] k. *)
Lemma find_ctor_runner md k :
  ctor_names_fresh md = true ->
  find_direct ctor_runner_name (app md (ctor_runner_items k)) = Some (Defined (ctor_runner k)).
Proof.
  unfold ctor_names_fresh. induction md as [|it md IH]; cbn [forallb]; intros H.
  - reflexivity.
  - apply andb_prop in H as [Hit Hmd]. cbn [app find_direct].
    destruct it as [f|n t|n lk al its|n lk t]; cbn [item_name existsb] in Hit; try exact (IH Hmd).
    + destruct (name_eqb (fn_name f) ctor_runner_name) eqn:E; [|exact (IH Hmd)].
      cbn in Hit. discriminate Hit.
    + destruct (name_eqb n ctor_runner_name) eqn:E; [|exact (IH Hmd)].
      cbn in Hit. discriminate Hit.
Qed.

(** With fresh names, [with_ctor_runner] defines the runner symbol as
    the runner for the module's own constructors. *)
Lemma with_ctor_runner_defines md :
  ctor_names_fresh md = true ->
  find_direct ctor_runner_name (with_ctor_runner md) = Some (Defined (ctor_runner (length (ctor_names md)))).
Proof. apply find_ctor_runner. Qed.

(** This function lays out md and returns its symbol table, without
    writing any initial contents. *)
Definition module_globals (md : module) : option (list (name * ptr)) :=
  match fold_left layout md (Some (data_base, [], [])) with
  | Some (_, globals0, _) => fold_left alias_global md (Some globals0)
  | None => None
  end.

(** [initial_memory] returns the symbol table [module_globals] computes. *)
Lemma initial_memory_globals md g m :
  initial_memory md = Some (g, m) -> module_globals md = Some g.
Proof.
  unfold initial_memory, module_globals.
  destruct (fold_left layout md _) as [[[a g0] rs]|]; cbn; [|discriminate].
  destruct (fold_left alias_global md _) as [g1|]; cbn; [|discriminate].
  destruct (fold_left (contents g1) md _); cbn; [|discriminate]. congruence.
Qed.
