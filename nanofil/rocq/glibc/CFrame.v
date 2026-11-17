(** A proof about one block of a compiled function must say what the
    temporaries hold when the block starts. The compiler numbers the
    temporaries, so a premise such as `lookup "iw_1.v94" e = …` tells a
    reader nothing, and a recompile that renumbers them breaks it. The
    source tables of a fixture already record which C variable each
    temporary holds. This module uses them to state a block's
    environment by C variable.

    A cut signature lists the temporaries that are live at a label.
    For each one it gives a key and an offset. The key of a named
    temporary is its C name, and the key of a temporary that holds the
    address of a variable is `&` and the variable's name. A check or
    an address computation holds the value of the temporary it was
    computed from, so its key is that temporary's key and its offset
    is the constant that was added. A temporary without a C name keeps
    its own name as the key. The code generator works these keys out
    and writes them to the `temp_keys` table of the function.

    The predicate [c_env] says that every temporary of a signature
    holds the value of its key, moved by its offset. It unfolds to the
    lookups that the step rules already use. The names are only keys.
    A wrong name gives a lemma that nobody can use, and it cannot give
    a false one, because [c_env] is a premise about the real
    environment. *)

From Stdlib Require Import String Ascii ZArith NArith List Bool Lia DecimalString.
From iris.proofmode Require Import string_ident.
From Nanofil Require Import Term Syntax Values Semantics.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## Cut signatures *)

(** A cut signature gives each live temporary a key and an offset. *)
Definition cut_sig : Type := list (name * (string * Z)).

Definition name_string (n : name) : string :=
  match n with TAtom s => s | _ => "?" end.

(** The source tables of a function record, for each temporary of its
    body, the temporary it was computed from, a key and an offset. The
    code generator follows checks and constant pointer additions to
    find them, so this module does not search the body. A temporary
    without a row is its own root, and its key is its own name. *)
Definition key_table : Type := list (name * (name * string * Z)).

Definition key_row (keys : key_table) (t : name) : name * string * Z :=
  match lookup t keys with Some r => r | None => (t, name_string t, 0) end.

(** Two temporaries can hold different values of one C variable at the
    same label. The second root with a key that is already taken gets
    the key followed by its own name, so that no key stands for two
    values. *)
Fixpoint assign_keys (roots : list (name * string)) (seen : list (name * string)) : list (name * string) :=
  match roots with
  | [] => seen
  | (r, k) :: rest =>
      if existsb (fun p => name_eqb (fst p) r) seen then assign_keys rest seen
      else
        let k' := if existsb (fun p => String.eqb (snd p) k) seen then k ++ "@" ++ name_string r else k in
        assign_keys rest (seen ++ [(r, k')])
  end.

(** The signature at a label is computed from the function's key table
    and the temporaries that are live there. *)
Definition cut_sig_of (keys : key_table) (live : list name) : cut_sig :=
  let rs := map (key_row keys) live in
  let assigned := assign_keys (map (fun '(r, k, _) => (r, k)) rs) [] in
  map (fun '(t, (r, _, off)) => (t, (match lookup r assigned with Some k => k | None => name_string r end, off)))
    (combine live rs).

(** The function [cut_table] computes the signature of every label of
    a function. A proof computes this table once, and [cut_in] reads
    the signature of one label from it. *)
Definition cut_table (keys : key_table) (live_in : list (name * list name)) : list (string * cut_sig) :=
  map (fun '(l, ts) => (name_string l, cut_sig_of keys ts)) live_in.

(** The function [cut_at] computes the signature of one label. A
    large function has hundreds of labels, and a proof cuts it at a
    few, so it computes only their signatures. *)
Definition cut_at (keys : key_table) (live_in : list (name * list name)) (l : string) : cut_sig :=
  cut_sig_of keys (match lookup (TAtom l) live_in with Some ts => ts | None => [] end).

(** A block with phi nodes reads, along each edge, the temporaries
    that the phi nodes name for that edge. The function [phi_sources]
    lists them for the edge from the block named from. *)
Definition phi_sources (phis : list phi) (from : string) : list name :=
  flat_map (fun ph => match ph with
                      | Phi _ _ pairs => match lookup (TAtom from) pairs with Some (Tmp t) => [t] | _ => [] end
                      end) phis.

Fixpoint add_new (ts seen : list name) : list name :=
  match ts with
  | [] => seen
  | t :: rest => add_new rest (if existsb (name_eqb t) seen then seen else seen ++ [t])
  end.

(** The signature of an edge lists the temporaries that are live at
    the label together with the temporaries that its phi nodes read
    along the edge. *)
Definition cut_edge (keys : key_table) (live_in : list (name * list name)) (f : func) (l from : string) : cut_sig :=
  let live := match lookup (TAtom l) live_in with Some ts => ts | None => [] end in
  let phis := match find_block (TAtom l) (fn_blocks f) with Some b => b_phis b | None => [] end in
  cut_sig_of keys (add_new (phi_sources phis from) live).

Fixpoint cut_in (table : list (string * cut_sig)) (l : string) : cut_sig :=
  match table with
  | [] => []
  | (l', sig) :: rest => if String.eqb l l' then sig else cut_in rest l
  end.

(** ## Names for the hypotheses of a cut *)

(** A proof reads more easily when the hypothesis about a temporary is
    named after the C value that the temporary holds. The first
    temporary that holds a key without an offset gets the name `H` and
    the key, such as `Hbuf`. Every other temporary gets the key, its
    offset and its own name, such as `Hbuf_8_chk0`, so that two
    temporaries never share a name. *)
Definition ident_char (a : ascii) : string :=
  let n := nat_of_ascii a in
  if ((48 <=? n) && (n <=? 57) || (65 <=? n) && (n <=? 90) || (97 <=? n) && (n <=? 122) || (n =? 95))%nat
  then String a EmptyString
  else if (n =? 38)%nat then "addr_" else "_".

Fixpoint ident_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String a rest => ident_char a ++ ident_string rest
  end.

Definition offset_string (off : Z) : string :=
  (if off <? 0 then "m" else "") ++ NilZero.string_of_uint (N.to_uint (Z.to_N (Z.abs off))).

Fixpoint hyp_names (sig : cut_sig) (seen : list string) : list string :=
  match sig with
  | [] => []
  | (t, (k, off)) :: rest =>
      if (off =? 0) && negb (existsb (String.eqb k) seen)
      then ("H" ++ ident_string k) :: hyp_names rest (k :: seen)
      else ("H" ++ ident_string k ++ (if off =? 0 then "" else "_" ++ offset_string off) ++ "_" ++
            ident_string (name_string t)) :: hyp_names rest seen
  end.

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
    into one lookup hypothesis for each temporary, named as
    [hyp_names] says. *)
Ltac c_env_take H rest id :=
  let H1 := fresh id in let H2 := fresh "Henv" in destruct H as [H1 H2]; rest H2.

Ltac c_env_split H ns :=
  lazymatch type of H with
  | _ /\ _ =>
      lazymatch ns with
      | ?n :: ?ns' => StringToIdent.string_to_ident_cps n ltac:(c_env_take H ltac:(fun H2 => c_env_split H2 ns'))
      end
  | True => clear H
  | _ => idtac
  end.

Ltac c_env_sig :=
  lazymatch goal with
  | |- c_env ?s ?e ?v =>
      let s' := eval vm_compute in s in let v0 := eval hnf in v in let v' := eval cbn in v0 in
      change (c_env s' e v')
  end.

Ltac c_env_open H :=
  lazymatch type of H with
  | c_env ?s ?e ?v =>
      let s' := eval vm_compute in s in let v0 := eval hnf in v in let v' := eval cbn in v0 in
      let ns := eval vm_compute in (hyp_names s' []) in
      change (c_env s' e v') in H;
      let T := type of H in
      let T' := eval cbv [c_env assoc word_shift String.eqb Ascii.eqb Bool.eqb Z.eqb] in T in
      change T' in H; cbn [ptr_addr ptr_cap] in H; c_env_split H ns
  end.

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
