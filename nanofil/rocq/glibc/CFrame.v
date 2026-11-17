(** A proof about one block of a compiled function must say what the
    temporaries hold when the block starts. The compiler numbers the
    temporaries, so a premise such as `lookup "iw_1.v94" e = …` tells a
    reader nothing, and a recompile that renumbers them breaks it. The
    source tables of a fixture already record which C variable each
    temporary holds. This module uses them to state a block's
    environment by C variable.

    A cut signature lists the temporaries that are live at a label.
    For each one it gives a key and an offset. The key of a named
    temporary is its C name. A check or an address computation is
    followed back through the function body to the temporary it was
    computed from, so its key is that temporary's name and its offset
    is the constant that was added. A temporary without a C name keeps
    its own name as the key.

    The predicate [c_env] says that every temporary of a signature
    holds the value of its key, moved by its offset. It unfolds to the
    lookups that the step rules already use. The names are only keys.
    A wrong name gives a lemma that nobody can use, and it cannot give
    a false one, because [c_env] is a premise about the real
    environment. *)

From Stdlib Require Import String ZArith List Bool Lia.
From Nanofil Require Import Term Syntax Values Semantics.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## Where a temporary's value comes from *)

(** The instruction that defines a temporary is the first one in the
    function's blocks that binds it. *)
Definition inst_def (i : inst) : option name :=
  match i with
  | Let d _ _ _ | Flight d _ _ _ => Some d
  | _ => None
  end.

Definition find_def (f : func) (t : name) : option inst :=
  find (fun i => match inst_def i with Some d => name_eqb d t | None => false end)
    (flat_map b_insts (fn_blocks f)).

(** A check binds the pointer it was given as its last argument. *)
Definition is_check (o : op) : bool :=
  match o with
  | Check _ _ _ _ | CheckAhead _ _ _ _ _ | Renew _ _ _ _ | RenewHull _ _ _ _ | HalfCheck _ _ _ _ _ => true
  | _ => false
  end.

(** The function [root_of] follows a temporary back to the temporary it
    was computed from and returns the constant that was added on the
    way. It stops at a temporary that is defined in any other way. *)
Fixpoint root_of (f : func) (fuel : nat) (t : name) : name * Z :=
  match fuel with
  | O => (t, 0)
  | S fuel =>
      match find_def f t with
      | Some (Let _ A o args) =>
          if is_check o then
            match last args (Const 0) with Tmp r => root_of f fuel r | _ => (t, 0) end
          else (t, 0)
      | Some (Flight _ Add [FAddress (Tmp r); FValue (Const k)] (LowerOf (Tmp r'))) =>
          if name_eqb r r' then let '(root, off) := root_of f fuel r in (root, off + k) else (t, 0)
      | _ => (t, 0)
      end
  end.

(** ## Cut signatures *)

(** A cut signature gives each live temporary a key and an offset. *)
Definition cut_sig : Type := list (name * (string * Z)).

Definition name_string (n : name) : string :=
  match n with TAtom s => s | _ => "?" end.

(** The key of a root temporary is its C name when the tables have
    one, and the temporary's own name otherwise. *)
Definition key_of (names : list (name * string)) (t : name) : string :=
  match lookup t names with Some c => c | None => name_string t end.

(** Two temporaries can hold different values of one C variable at the
    same label. The second root with a C name that is already taken
    gets the name followed by its own name, so that no key stands for
    two values. *)
Fixpoint assign_keys (names : list (name * string)) (roots : list name) (seen : list (name * string))
    : list (name * string) :=
  match roots with
  | [] => seen
  | r :: rest =>
      if existsb (fun p => name_eqb (fst p) r) seen then assign_keys names rest seen
      else
        let k := key_of names r in
        let k' := if existsb (fun p => String.eqb (snd p) k) seen then k ++ "@" ++ name_string r else k in
        assign_keys names rest (seen ++ [(r, k')])
  end.

(** The signature at a label is computed from the function's body, the
    names of its temporaries and the temporaries that are live there. *)
Definition cut_sig_of (f : func) (names : list (name * string)) (live : list name) : cut_sig :=
  let rs := map (root_of f 16) live in
  let keys := assign_keys names (map fst rs) [] in
  map (fun '(t, (r, off)) => (t, (match lookup r keys with Some k => k | None => name_string r end, off)))
    (combine live rs).

(** The function [cut_at] computes the signature at the label l from
    the source tables of a function. *)
Definition cut_at (f : func) (names : list (name * string)) (live_in : list (name * list name)) (l : string)
    : cut_sig :=
  cut_sig_of f names (match lookup (TAtom l) live_in with Some ts => ts | None => [] end).

(** The function [cut_table] computes the signature of every label of
    a function. A proof computes this table once, and [cut_in] reads
    the signature of one label from it. *)
Definition cut_table (f : func) (names : list (name * string)) (live_in : list (name * list name))
    : list (string * cut_sig) :=
  map (fun '(l, ts) => (name_string l, cut_sig_of f names ts)) live_in.

Fixpoint cut_in (table : list (string * cut_sig)) (l : string) : cut_sig :=
  match table with
  | [] => []
  | (l', sig) :: rest => if String.eqb l l' then sig else cut_in rest l
  end.

(** The keys that have no C name are the ones a reader cannot follow,
    so a proof can ask for them and report them. *)
Definition raw_keys (names : list (name * string)) (sig : cut_sig) : list string :=
  flat_map (fun '(_, (k, _)) => if existsb (fun p => String.eqb (snd p) k) names then [] else [k]) sig.

(** ## The environment at a cut *)

(** A pointer moved by an offset keeps its capability. An integer has
    no offset. *)
Definition word_shift (w : word) (off : Z) : word :=
  match w with
  | WPtr p => if off =? 0 then w else WPtr (mkPtr (ptr_addr p + off) (ptr_cap p))
  | _ => w
  end.

Fixpoint assoc (k : string) (vals : list (string * word)) : option word :=
  match vals with
  | [] => None
  | (k', w) :: rest => if String.eqb k k' then Some w else assoc k rest
  end.

(** The environment e fits a signature and a list of values when every
    temporary of the signature holds the value of its key, moved by its
    offset. A key that the list lacks makes the statement false. *)
Fixpoint c_env (sig : cut_sig) (e : env) (vals : list (string * word)) : Prop :=
  match sig with
  | [] => True
  | (t, (k, off)) :: rest =>
      match assoc k vals with
      | Some w => lookup t e = Some (word_shift w off)
      | None => False
      end /\ c_env rest e vals
  end.

(** One temporary of the signature can be read from the environment. *)
Lemma c_env_lookup sig e vals t k off w :
  c_env sig e vals -> In (t, (k, off)) sig -> assoc k vals = Some w ->
  lookup t e = Some (word_shift w off).
Proof.
  induction sig as [|[t' [k' off']] sig IH]; cbn [c_env In]; [tauto|].
  intros [H Hrest] [E | Hin] Hk.
  - injection E as -> -> ->. rewrite Hk in H. exact H.
  - exact (IH Hrest Hin Hk).
Qed.

(** The empty signature fits every environment. A return block has it,
    because nothing is live there. *)
Lemma c_env_nil e vals : c_env [] e vals.
Proof. exact I. Qed.

(** Two pointers with one capability are equal when their addresses
    are. The closing tactic uses this to compare a computed address
    with the one a signature asks for. *)
Lemma some_ptr_eq a a' c : a = a' -> Some (WPtr (mkPtr a c)) = Some (WPtr (mkPtr a' c)).
Proof. intros ->. reflexivity. Qed.

(** ## Tactics *)

(** The tactic [c_env_open] turns a hypothesis H : c_env sig e vals
    into one lookup hypothesis for each temporary. *)
Ltac c_env_split H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "Hlk" in let H2 := fresh "Henv" in destruct H as [H1 H2]; c_env_split H2
  | True => clear H
  | _ => idtac
  end.

Ltac c_env_sig :=
  lazymatch goal with
  | |- c_env ?s ?e ?v =>
      let s' := eval vm_compute in s in let v' := eval hnf in v in change (c_env s' e v')
  end.

Ltac c_env_open H :=
  lazymatch type of H with
  | c_env ?s ?e ?v =>
      let s' := eval vm_compute in s in let v' := eval hnf in v in change (c_env s' e v') in H
  end;
  let T := type of H in
  let T' := eval cbv [c_env assoc word_shift String.eqb Ascii.eqb Bool.eqb Z.eqb] in T in
  change T' in H; cbn [ptr_addr ptr_cap] in H; c_env_split H.

(** A proof that jumps to a label must show that its environment fits
    the label's signature. The tactic [c_env_close_with] shows it by
    looking up each temporary with the tactic lk. A pointer may differ
    from the expected one in how its address is written, and the
    tactic side proves that the two addresses are equal. *)
Ltac c_env_close_with lk side :=
  c_env_sig;
  lazymatch goal with
  | |- c_env _ ?e _ =>
      let e' := fresh "e" in
      set (e' := e); cbv [c_env assoc word_shift String.eqb Ascii.eqb Bool.eqb Z.eqb]; subst e'
  end;
  cbn [ptr_addr ptr_cap];
  repeat lazymatch goal with
    | |- _ /\ _ => split
    | |- True => exact I
    | |- lookup _ _ = Some _ => first [solve [lk] | (etransitivity; [solve [lk] | apply some_ptr_eq; side])]
    end.
