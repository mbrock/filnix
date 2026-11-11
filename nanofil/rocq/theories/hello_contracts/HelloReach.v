(** Reference closure of the linked GNU Hello image, including function
    addresses passed as callbacks and symbols stored in data. This checks
    the image we run, not preservation of the original object collection:
    pruning is trusted, checked by link.pl's own reachability traversal. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Maps Syntax Values Memory Runtime Semantics
  Run HelloCode HelloModule HelloLeaf.
Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

(** Every global or initializer symbol below a term, following the same
    reference forms as link.pl; a callback address is not just a call. *)
Fixpoint image_refs (t : term) : list name :=
  let fix refs_list (ts : list term) : list name :=
    match ts with
    | [] => []
    | x :: xs => image_refs x ++ refs_list xs
    end in
  match t with
  | TApp "global" [n] => [n]
  | TApp "sym" [n; off] => [n]
  | TApp _ ts => refs_list ts
  | TList ts => refs_list ts
  | _ => []
  end.

(** The linked image's named items and all their outgoing references,
    computed once rather than unfolding its large bodies in proofs. *)
Definition hello_edges : list (name * list name) := Eval vm_compute in
  match hello_term with
  | TApp "module" [TList items] =>
      flat_map (fun t => match t with
        | TApp "func" [n; linkage; result; ps; bs] => [(n, image_refs t)]
        | TApp "data" [n; linkage; alignment; contents] => [(n, image_refs t)]
        | _ => []
        end) items
  | _ => []
  end.

(** Static reachability from main follows all references, not just direct
    calls, so registration and data initialization cannot hide an edge. *)
Inductive hello_reachable : name -> Prop :=
| hello_reach_main : hello_reachable (TAtom "main")
| hello_reach_ref source refs target :
    hello_reachable source -> In (source, refs) hello_edges ->
    In target refs -> hello_reachable target.

(** External data imports may be supplied by startup, unlike function
    imports, which [hello_linked] requires to stay outside the globals. *)
Definition hello_data_imports : list string :=
  ["stdout"; "stderr"; "program_invocation_name";
   "program_invocation_short_name"; "optarg"; "optind"].

(** Classification uses actual decoded functions and allocated globals;
    no missing definition is silently treated as an arbitrary import. *)
Definition hello_reference_ok (n : name) : bool :=
  match find_direct n hello_module with
  | Some (Defined _) => true
  | _ => match lookup n hello_globals with
         | Some _ => true
         | None => match n with
           | TAtom s => existsb (String.eqb s) hello_externals ||
                        existsb (String.eqb s) hello_data_imports
           | _ => false
           end
         end
  end.

(** Every edge in the image ends at a definition or an enumerated libc
    import, including edges originating in data rather than code. *)
Lemma hello_edges_closed :
  forallb (fun edge => forallb hello_reference_ok (snd edge)) hello_edges = true.
Proof. vm_compute. reflexivity. Qed.

(** Every statically reachable symbol is a decoded function, allocated
    module symbol, external function import, or external data import. *)
Theorem hello_reachable_closed n : hello_reachable n ->
  (exists f, find_direct n hello_module = Some (Defined f)) \/
  (exists p, lookup n hello_globals = Some p) \/
  (exists s, n = TAtom s /\
    (existsb (String.eqb s) hello_externals = true \/
     existsb (String.eqb s) hello_data_imports = true)).
Proof.
  intro Hreach.
  assert (Hok : hello_reference_ok n = true).
  { destruct Hreach as [|source refs target Hsource Hedge Hin].
    - vm_compute. reflexivity.
    - pose proof hello_edges_closed as Hclosed.
      apply forallb_forall with (x := (source, refs)) in Hclosed; [|exact Hedge].
      apply forallb_forall with (x := target) in Hclosed; [exact Hclosed|exact Hin]. }
  unfold hello_reference_ok in Hok.
  destruct (find_direct n hello_module) as [[f|outside_name]|] eqn:Hfn.
  - left. exists f. reflexivity.
  - right. destruct (lookup n hello_globals) as [p|] eqn:Hp.
    + left. exists p. reflexivity.
    + right. destruct n as [z|s|tag args|items]; try discriminate Hok.
      exists s. split; [reflexivity|]. apply orb_true_iff. exact Hok.
  - right. destruct (lookup n hello_globals) as [p|] eqn:Hp.
    + left. exists p. reflexivity.
    + right. destruct n as [z|s|tag args|items]; try discriminate Hok.
      exists s. split; [reflexivity|]. apply orb_true_iff. exact Hok.
Qed.

(** A direct call has a decoded body or names one of the enumerated
    external functions; a data import can never discharge this check. *)
Definition hello_call_ok (n : name) : bool :=
  match find_direct n hello_module with
  | Some (Defined _) => true
  | _ => match n with
         | TAtom s => existsb (String.eqb s) hello_externals
         | _ => false
         end
  end.

(** All calls in the decoded image meet the function-only classification,
    independently of whether a particular control-flow path is taken. *)
Lemma hello_calls_closed :
  forallb (fun it => match it with
    | IFunc f => forallb hello_call_ok (called f)
    | _ => true
    end) hello_module = true.
Proof. vm_compute. reflexivity. Qed.

(** Every call target of a module function is defined in the module or
    is a libc function import. This also covers code reached by callback. *)
Theorem hello_function_target f n :
  In (IFunc f) hello_module -> In n (called f) ->
  (exists body, find_direct n hello_module = Some (Defined body)) \/
  (exists s, n = TAtom s /\ existsb (String.eqb s) hello_externals = true).
Proof.
  intros Hf Hn. pose proof hello_calls_closed as Hall.
  apply forallb_forall with (x := IFunc f) in Hall; [|exact Hf].
  apply forallb_forall with (x := n) in Hall; [|exact Hn].
  unfold hello_call_ok in Hall.
  destruct (find_direct n hello_module) as [[body|outside_name]|] eqn:Hfn.
  - left. exists body. reflexivity.
  - right. destruct n as [z|s|tag args|items]; try discriminate Hall.
    exists s. split; [reflexivity|exact Hall].
  - right. destruct n as [z|s|tag args|items]; try discriminate Hall.
    exists s. split; [reflexivity|exact Hall].
Qed.

(** A reference with neither a function definition nor a module symbol is
    explicitly imported; the image cannot refer to an unlisted name. *)
Theorem hello_reachable_import n : hello_reachable n ->
  find_direct n hello_module = None -> lookup n hello_globals = None ->
  exists s, n = TAtom s /\
    (existsb (String.eqb s) hello_externals = true \/
     existsb (String.eqb s) hello_data_imports = true).
Proof.
  intros Hr Hfn Hp. destruct (hello_reachable_closed n Hr) as [Hbody|[Hglobal|Himport]].
  - destruct Hbody as [f Hf]. rewrite Hfn in Hf. discriminate Hf.
  - destruct Hglobal as [p Hglobal]. rewrite Hp in Hglobal. discriminate Hglobal.
  - exact Himport.
Qed.

(** Runtime-specific linking keeps the image and its own symbol prefix
    fixed, leaving only actual libc data cells to the entry proof. *)
Module HelloReach (R : Runtime).

(** Module definitions take precedence over any startup data extension. *)
Definition hello_genv (libc_globals : list (name * ptr)) : genv :=
  mkGenv hello_module (hello_globals ++ libc_globals) R.free.

(** A data-only extension does not bind any external function import.
    Cell layout and initialized representation remain entry obligations. *)
Definition hello_data_extension (libc_globals : list (name * ptr)) : Prop :=
  forall s, existsb (String.eqb s) hello_externals = true ->
    lookup (TAtom s) libc_globals = None.

(** Prefix lookup needs no uniqueness or disjointness premise: the actual
    association-list lookup deliberately chooses the module's binding. *)
Theorem hello_global_agreement libc_globals n p :
  lookup n hello_globals = Some p ->
  lookup n (ge_globals (hello_genv libc_globals)) = Some p.
Proof.
  intro Hp. change (lookup n (hello_globals ++ libc_globals) = Some p).
  rewrite lookup_app, Hp. reflexivity.
Qed.

(** The module itself never binds one of its external function imports. *)
Lemma hello_function_imports_unbound s :
  existsb (String.eqb s) hello_externals = true ->
  lookup (TAtom s) hello_globals = None.
Proof.
  intro Hs.
  assert (Hall : forallb (fun s =>
    match lookup (TAtom s) hello_globals with None => true | _ => false end)
    hello_externals = true) by (vm_compute; reflexivity).
  apply existsb_exists in Hs as (s' & Hin & Heq).
  apply String.eqb_eq in Heq. subst s'.
  apply forallb_forall with (x := s) in Hall; [|exact Hin].
  destruct (lookup (TAtom s) hello_globals); [discriminate Hall|reflexivity].
Qed.

(** The constructed environment discharges the leaf proofs' full linking
    contract when startup supplies no external function binding. *)
Theorem hello_genv_linked libc_globals : hello_data_extension libc_globals ->
  hello_linked (hello_genv libc_globals).
Proof.
  intro Hdata. split; [reflexivity|]. split.
  - intros n p Hp. apply hello_global_agreement. exact Hp.
  - intros s Hs. change (lookup (TAtom s) (hello_globals ++ libc_globals) = None).
    rewrite lookup_app, (hello_function_imports_unbound s Hs).
    apply Hdata. exact Hs.
Qed.

(** No wrapper changes the runtime's free operation. *)
Theorem hello_free_agreement libc_globals :
  ge_free (hello_genv libc_globals) = R.free.
Proof. reflexivity. Qed.

(** Function lookup reads only the module. This stronger agreement holds
    for every name, whether reachable, missing, or an external import. *)
Theorem hello_find_fn_agreement ge n : ge_module ge = hello_module ->
  find_fn ge n = find_fn (hello_genv []) n.
Proof. intro Hmodule. unfold find_fn. rewrite Hmodule. reflexivity. Qed.

(** In particular every reachable function definition is the exact body
    the linked environment dispatches, not a replacement with its name. *)
Theorem hello_reachable_function ge n f :
  ge_module ge = hello_module -> hello_reachable n ->
  find_direct n hello_module = Some (Defined f) ->
  find_fn ge n = Some (Defined f).
Proof.
  intros Hmodule Hreach Hfn. unfold find_fn. rewrite Hmodule, Hfn. reflexivity.
Qed.

(** External function imports cannot become internal pointer targets in
    any environment satisfying the leaf proofs' linking contract. *)
Theorem hello_external_unbound ge s : hello_linked ge ->
  existsb (String.eqb s) hello_externals = true ->
  lookup (TAtom s) (ge_globals ge) = None /\ find_fn ge (TAtom s) = None.
Proof.
  intros [Hmodule [Hglobals Himports]] Hs. split.
  - apply Himports. exact Hs.
  - apply hello_outside; assumption.
Qed.

End HelloReach.
