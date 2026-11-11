(** # λANF to nanofil IR over the 32-bit arena

    Milestone M2 of docs/lambda-anf.md: CertiRocq's core λANF, after
    its whole λANF pipeline (closure conversion and hoisting
    included, `-O 1 --anf-variant 8`), lowered to a [[stage|checked]]
    module of nanofil IR whose every functional value is a 32-bit `w`
    word in the arena of nanofil/anf (anf_arena.h). The module is
    judged by the [[validator]] and compiled by
    Compile.compile_allocated like any other: [lower] writes IR terms,
    and `nanofil-backend compile-allocated` takes them.

    CertiRocq's tap (nix/certirocq-anf-tap.patch) writes the λANF as
    Prolog clauses, which IrText.v's reader reads:

    | Clause | Means |
    |---|---|
    | `anf_ctor(T, I, A, O, Name)` | constructor tag T of inductive I, arity A, ordinal O |
    | `anf_ftag(T, A)` | function tag T of arity A |
    | `anf_name(F, Name)` | the function F's name |
    | `anf_body(E)` | the program |

    ## Values

    A value is a `w` word. An odd word `(v << 1) | 1` is an immediate:
    a constructor without arguments (its ordinal), or a function's id
    (its fid, for a closure's code). An even word `idx << 1` is the
    block at word idx of the arena: its header `(arity << 10) | ord`
    (scanned, anf_arena.h's `ANF_HDR(arity, 0, ord)`) and its fields.

    ## Functions, clusters and joins

    Every hoisted function is a candidate to be a [[block]] of
    another function rather than a function of its own: one that is
    never a value and never called but in tail position, and all of
    whose tail callers are in one cluster. CertiRocq binds the rest of
    a `match` as such a function (a join point), and a loop's body
    tail-calls itself. A cluster is one IR function: its root's body,
    then each absorbed function's body, each behind a head block whose
    [[phi|phis]] take the parameters and the cached young index. A tail
    call within the cluster is a `goto`, polled when it goes back to
    an earlier or the same body, so every cycle polls; any other tail
    call is a `call` and a `ret`.

    A function that is a value has a fid. A call through a closure's
    code calls the dispatcher of its arity (`anf_applyN`), which
    finds the function by a binary search on the fid.

    ## Allocation and roots

    Each function reads the young index and the nursery's end from the
    state (`struct anf_state`) at its entry and keeps the young index
    in a temporary. At the head of each stretch without a call, one
    test asks for all the words the stretch allocates on its longest
    path (CertiRocq's `max_allocs`); when they are not there, the live
    values go to the shadow roots, `anf_lower_reserve` collects, and
    they come back. A call (`Eletapp`) does the same around itself:
    the values live after it are pushed onto `roots[]` before and
    reloaded after, so a collection in the callee moves them.

    Every arena and state access is a [[check]] and a raw access; a
    run of projections from one block shares one check. *)

From Stdlib Require Import String ZArith List Bool Ascii.
From Nanofil Require Import Term Maps.
From Backend Require Import Text Order.
Import ListNotations.
Local Open Scope Z_scope.

(** ## Results *)

(** A result, or why there is none. *)
Inductive res (A : Type) : Type :=
| Ok (a : A)
| Err (why : string).
Arguments Ok {A} a.
Arguments Err {A} why.

(** The result of [f] on [r]'s, or [r]'s failure. *)
Definition bind {A B : Type} (r : res A) (f : A -> res B) : res B :=
  match r with Ok a => f a | Err w => Err w end.

Notation "'let?' x := r 'in' k" := (bind r (fun x => k))
  (at level 200, x pattern, r at level 100, k at level 200).

(** ## λANF *)

(** CertiRocq's [LambdaANF.term.exp] and [fundefs], with variables and
    tags as integers. [Eletapp] also holds the variables live after
    the call: the free variables of its continuation without its
    result. A primitive value is kept as its text. *)
Inductive exp : Type :=
| Econstr (x t : Z) (ys : list Z) (e : exp)
| Ecase (x : Z) (arms : list (Z * exp))
| Eproj (x t n y : Z) (e : exp)
| Eletapp (x f ft : Z) (ys : list Z) (live : list Z) (e : exp)
| Efun (fds : fundefs) (e : exp)
| Eapp (f ft : Z) (ys : list Z)
| Eprim_val (x : Z) (e : exp)
| Eprim (x p : Z) (ys : list Z) (e : exp)
| Ehalt (x : Z)
with fundefs : Type :=
| Fcons (f ft : Z) (xs : list Z) (body : exp) (rest : fundefs)
| Fnil.

(** ## Sets of variables, as sorted lists *)

(** [x] put in the sorted list [ys]. *)
Fixpoint zinsert (x : Z) (ys : list Z) : list Z :=
  match ys with
  | [] => [x]
  | y :: ys' => if x <? y then x :: ys else if x =? y then ys else y :: zinsert x ys'
  end.

(** The union of the sorted lists [xs] and [ys]. *)
Fixpoint zunion (xs : list Z) : list Z -> list Z :=
  match xs with
  | [] => fun ys => ys
  | x :: xs' =>
      fix go (ys : list Z) : list Z :=
        match ys with
        | [] => xs
        | y :: ys' =>
            if x <? y then x :: zunion xs' ys
            else if y <? x then y :: go ys'
            else x :: zunion xs' ys'
        end
  end.

(** The sorted list [ys] without [x]. *)
Definition zremove (x : Z) (ys : list Z) : list Z := filter (fun y => negb (y =? x)) ys.

(** The set of the elements of [xs]. *)
Definition zset (xs : list Z) : list Z := fold_right zinsert [] xs.

(** ## Reading the tap's clauses *)

(** The integer t. *)
Definition dint (t : term) : res Z :=
  match t with TInt n => Ok n | _ => Err "an integer was expected" end.

(** The integers of the list ts. *)
Fixpoint dints (ts : list term) : res (list Z) :=
  match ts with
  | [] => Ok []
  | t :: ts' => let? n := dint t in let? ns := dints ts' in Ok (n :: ns)
  end.

(** The integers of the list term t. *)
Definition dintlist (t : term) : res (list Z) :=
  match t with TList ts => dints ts | _ => Err "a list was expected" end.

(** The expression the term t writes, with its free variables. A call
    whose result is returned at once, `letapp(X, F, FT, Ys, halt(X))`,
    which is how CertiRocq's direct style writes most tail calls, is
    the tail call `app(F, FT, Ys)`. *)
Fixpoint dexp (t : term) : res (exp * list Z) :=
  match t with
  | TApp f args =>
      if String.eqb f "constr" then
        match args with
        | [x; tg; ys; e1] =>
            let? x := dint x in let? tg := dint tg in let? ys := dintlist ys in
            let? (e, fv) := dexp e1 in
            Ok (Econstr x tg ys e, zunion (zset ys) (zremove x fv))
        | _ => Err "constr/4"
        end
      else if String.eqb f "case" then
        match args with
        | [x; TList arms] =>
            let? x := dint x in
            let? (arms', fv) :=
              (fix go (l : list term) : res (list (Z * exp) * list Z) :=
                 match l with
                 | [] => Ok ([], [])
                 | TApp g [tg; e1] :: l' =>
                     if String.eqb g "arm" then
                       let? tg := dint tg in let? (e, fv1) := dexp e1 in
                       let? (rest, fv2) := go l' in Ok ((tg, e) :: rest, zunion fv1 fv2)
                     else Err "arm/2"
                 | _ :: _ => Err "arm/2"
                 end) arms in
            Ok (Ecase x arms', zinsert x fv)
        | _ => Err "case/2"
        end
      else if String.eqb f "proj" then
        match args with
        | [x; tg; n; y; e1] =>
            let? x := dint x in let? tg := dint tg in let? n := dint n in let? y := dint y in
            let? (e, fv) := dexp e1 in
            Ok (Eproj x tg n y e, zinsert y (zremove x fv))
        | _ => Err "proj/5"
        end
      else if String.eqb f "letapp" then
        match args with
        | [x; g; ft; ys; e1] =>
            let? x := dint x in let? g := dint g in let? ft := dint ft in let? ys := dintlist ys in
            let? (e, fv) := dexp e1 in
            let live := zremove x fv in
            match e with
            | Ehalt x' => if x' =? x then Ok (Eapp g ft ys, zinsert g (zset ys))
                          else Ok (Eletapp x g ft ys live e, zinsert g (zunion (zset ys) live))
            | _ => Ok (Eletapp x g ft ys live e, zinsert g (zunion (zset ys) live))
            end
        | _ => Err "letapp/5"
        end
      else if String.eqb f "fun" then
        match args with
        | [TList defs; e1] =>
            let? fds :=
              (fix go (l : list term) : res fundefs :=
                 match l with
                 | [] => Ok Fnil
                 | TApp g [h; ft; xs; b1] :: l' =>
                     if String.eqb g "def" then
                       let? h := dint h in let? ft := dint ft in let? xs := dintlist xs in
                       let? (b, _) := dexp b1 in let? rest := go l' in Ok (Fcons h ft xs b rest)
                     else Err "def/4"
                 | _ :: _ => Err "def/4"
                 end) defs in
            let? (e, fv) := dexp e1 in
            Ok (Efun fds e, fv)
        | _ => Err "fun/2"
        end
      else if String.eqb f "app" then
        match args with
        | [g; ft; ys] =>
            let? g := dint g in let? ft := dint ft in let? ys := dintlist ys in
            Ok (Eapp g ft ys, zinsert g (zset ys))
        | _ => Err "app/3"
        end
      else if String.eqb f "prim_val" then
        match args with
        | [x; _; e1] => let? x := dint x in let? (e, fv) := dexp e1 in Ok (Eprim_val x e, zremove x fv)
        | _ => Err "prim_val/3"
        end
      else if String.eqb f "prim" then
        match args with
        | [x; p; ys; e1] =>
            let? x := dint x in let? p := dint p in let? ys := dintlist ys in
            let? (e, fv) := dexp e1 in
            Ok (Eprim x p ys e, zunion (zset ys) (zremove x fv))
        | _ => Err "prim/4"
        end
      else if String.eqb f "halt" then
        match args with
        | [x] => let? x := dint x in Ok (Ehalt x, [x])
        | _ => Err "halt/1"
        end
      else Err ("not an expression: " ++ f)%string
  | _ => Err "not an expression"
  end.

(** What a constructor tag says: its inductive, arity and ordinal. *)
Record ctor := mkctor { c_ind : Z; c_arity : Z; c_ord : Z }.

(** The program the tap's clauses describe. *)
Record prog := mkprog {
  p_ctors : list (Z * ctor);
  p_names : list (Z * string);
  p_body : option exp
}.

(** The clauses cs read into the program p. *)
Fixpoint read_clauses (cs : list term) (p : prog) : res prog :=
  match cs with
  | [] => Ok p
  | TApp f args :: cs' =>
      if String.eqb f "anf_ctor" then
        match args with
        | [TInt t; TInt i; TInt a; TInt o; _] =>
            read_clauses cs' (mkprog ((t, mkctor i a o) :: p_ctors p) (p_names p) (p_body p))
        | _ => Err "anf_ctor/5"
        end
      else if String.eqb f "anf_name" then
        match args with
        | [TInt v; TAtom s] => read_clauses cs' (mkprog (p_ctors p) ((v, s) :: p_names p) (p_body p))
        | _ => Err "anf_name/2"
        end
      else if String.eqb f "anf_body" then
        match args with
        | [e1] => let? (e, _) := dexp e1 in read_clauses cs' (mkprog (p_ctors p) (p_names p) (Some e))
        | _ => Err "anf_body/1"
        end
      else if String.eqb f "anf_ftag" then read_clauses cs' p
      else Err ("an unknown clause: " ++ f)%string
  | _ :: _ => Err "a clause that is not a compound"
  end.

(** ## The functions of a program *)

(** A hoisted function. *)
Record fdef := mkfd { fd_f : Z; fd_xs : list Z; fd_body : exp }.

(** The functions of fds, in order. *)
Fixpoint fundefs_list (fds : fundefs) : list fdef :=
  match fds with
  | Fcons f _ xs e rest => mkfd f xs e :: fundefs_list rest
  | Fnil => []
  end.

(** Whether e has no [Efun]: after hoisting, only the program does. *)
Fixpoint flat (e : exp) : bool :=
  match e with
  | Econstr _ _ _ e' | Eproj _ _ _ _ e' | Eletapp _ _ _ _ _ e'
  | Eprim_val _ e' | Eprim _ _ _ e' => flat e'
  | Ecase _ arms =>
      (fix go (l : list (Z * exp)) : bool :=
         match l with [] => true | (_, e1) :: l' => flat e1 && go l' end) arms
  | Efun _ _ => false
  | Eapp _ _ _ | Ehalt _ => true
  end.

(** What a body does with the functions: use one as a value, call one
    with [Eletapp], tail-call one (from the function [caller], the
    program being 0), or call through a closure with n arguments. *)
Inductive event : Type :=
| Escape (f : Z)
| LetCall (f : Z)
| TailCall (caller f : Z)
| Indirect (n : nat).

(** The events of the body e of the function cur, in front of acc;
    isfn tells the functions' names. *)
Fixpoint events (isfn : Z -> bool) (cur : Z) (e : exp) (acc : list event) : list event :=
  let esc (ys : list Z) (acc : list event) :=
    fold_left (fun acc y => if isfn y then Escape y :: acc else acc) ys acc in
  match e with
  | Econstr _ _ ys e' => events isfn cur e' (esc ys acc)
  | Ecase x arms =>
      (fix go (l : list (Z * exp)) (acc : list event) : list event :=
         match l with [] => acc | (_, e1) :: l' => go l' (events isfn cur e1 acc) end) arms (esc [x] acc)
  | Eproj _ _ _ y e' => events isfn cur e' (esc [y] acc)
  | Eletapp _ f _ ys _ e' =>
      events isfn cur e'
        (esc ys (if isfn f then LetCall f :: acc else Indirect (length ys) :: esc [f] acc))
  | Efun _ e' => events isfn cur e' acc
  | Eapp f _ ys => esc ys (if isfn f then TailCall cur f :: acc else Indirect (length ys) :: esc [f] acc)
  | Eprim_val _ e' => events isfn cur e' acc
  | Eprim _ _ ys e' => events isfn cur e' (esc ys acc)
  | Ehalt x => esc [x] acc
  end.

(** The root of f's cluster: f's parent's root, or f if it has none. *)
Fixpoint root_of (fuel : nat) (par : ZMap.t Z) (f : Z) : Z :=
  match fuel with
  | O => f
  | S fuel' => match ZMap.find f par with Some g => root_of fuel' par g | None => f end
  end.

(** One round of absorption: each candidate g that is still a root
    and whose tail callers outside its cluster are all in one cluster
    joins that cluster. Also whether any did. *)
Definition absorb_round (fuel : nat) (cands : list (Z * list Z)) (par : ZMap.t Z) : ZMap.t Z * bool :=
  fold_left
    (fun acc gc =>
       let '(par, changed) := acc in
       let '(g, callers) := gc in
       if ZMap.mem g par then acc
       else
         match zset (filter (fun r => negb (r =? g)) (map (root_of fuel par) callers)) with
         | [r] => (ZMap.add g r par, true)
         | _ => acc
         end)
    cands (par, false).

(** Rounds of absorption until none absorbs, at most fuel of them. *)
Fixpoint absorb (rounds fuel : nat) (cands : list (Z * list Z)) (par : ZMap.t Z) : ZMap.t Z :=
  match rounds with
  | O => par
  | S rounds' =>
      let '(par', changed) := absorb_round fuel cands par in
      if changed then absorb rounds' fuel cands par' else par'
  end.

(** What the lowering knows of a function: the name of its IR
    function (its cluster's, if absorbed), its fid if it is a value,
    its cluster's root, its place in the cluster, and its
    parameters. *)
Record fninfo := mkfi {
  fi_name : string;
  fi_fid : option Z;
  fi_root : Z;
  fi_seg : Z;
  fi_xs : list Z
}.

(** The program's constants: the variables of its body e that a
    constructor binds whose fields are all constants or functions,
    in front of acc. The body runs once, so its constants are
    allocated once, in the major heap ([gen]), where a collection
    never moves them: no test of the nursery waits for them and no
    call spills them, as OCaml makes them static data. *)
Fixpoint closed_vars (isfn : Z -> bool) (e : exp) (acc : ZMap.t unit) : ZMap.t unit :=
  match e with
  | Econstr x _ ys e' =>
      let acc := if forallb (fun y => ZMap.mem y acc || isfn y) ys then ZMap.add x tt acc else acc in
      closed_vars isfn e' acc
  | Ecase _ arms =>
      (fix go (l : list (Z * exp)) (acc : ZMap.t unit) : ZMap.t unit :=
         match l with [] => acc | (_, e1) :: l' => go l' (closed_vars isfn e1 acc) end) arms acc
  | Eproj _ _ _ _ e' | Eletapp _ _ _ _ _ e' | Efun _ e' | Eprim_val _ e' | Eprim _ _ _ e' =>
      closed_vars isfn e' acc
  | Eapp _ _ _ | Ehalt _ => acc
  end.

(** The words the boxed constants closed of e take, on all its paths
    together; arity a constructor's tag's arity. *)
Fixpoint closed_words (arity : Z -> Z) (closed : ZMap.t unit) (e : exp) : Z :=
  match e with
  | Econstr x t _ e' =>
      (if ZMap.mem x closed && negb (arity t =? 0) then arity t + 1 else 0) + closed_words arity closed e'
  | Ecase _ arms =>
      (fix go (l : list (Z * exp)) : Z :=
         match l with [] => 0 | (_, e1) :: l' => closed_words arity closed e1 + go l' end) arms
  | Eproj _ _ _ _ e' | Eletapp _ _ _ _ _ e' | Efun _ e' | Eprim_val _ e' | Eprim _ _ _ e' =>
      closed_words arity closed e'
  | Eapp _ _ _ | Ehalt _ => 0
  end.

(** A character of an assembler symbol: a letter, a digit or `_`. *)
Definition symbol_char (c : ascii) : ascii :=
  let n := nat_of_ascii c in
  if ((48 <=? n) && (n <=? 57))%nat || ((65 <=? n) && (n <=? 90))%nat
     || ((97 <=? n) && (n <=? 122))%nat then c else "_"%char.

(** The string s with each character that cannot be in a symbol made
    `_`. *)
Fixpoint symbol_string (s : string) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => String (symbol_char c) (symbol_string s')
  end.

(** The IR name of the function f, from its CertiRocq name if it has
    one. *)
Definition fn_name (names : list (Z * string)) (f : Z) : string :=
  match find (fun p => fst p =? f) names with
  | Some (_, s) => ("anf_" ++ symbol_string s ++ "_" ++ decimal f)%string
  | None => ("anf_f" ++ decimal f)%string
  end.

(** ## Code generation *)

(** What all of a module's code generation reads: the constructors,
    each inductive's kinds of constructors (whether it has immediate
    ones, boxed ones, and how many boxed), the functions, and the
    program's constants ([closed_vars]) with the words they take. *)
Record cl := mkcl {
  cl_ctors : ZMap.t ctor;
  cl_inds : ZMap.t (bool * bool * Z);
  cl_fns : ZMap.t fninfo;
  cl_closed : ZMap.t unit;
  cl_major : Z
}.

(** A finished block, its phis still to be built from the edges. *)
Record pblock := mkpb { pb_label : term; pb_phis : list term; pb_insts : list term; pb_jump : term }.

(** The state of an IR function's generation: the next fresh number,
    the finished blocks, last first, the edges into each label (from
    which block, with which values for its phis), and the next word of
    the program's constants in the major heap. *)
Record st := mkst {
  s_next : Z;
  s_blocks : list pblock;
  s_edges : nmap (list (term * list term));
  s_major : Z
}.

(** The block being generated: its label and phis, its instructions
    so far (last first), the IR value of each λANF variable, the
    young index, the [[check]] proofs that cover a block's fields (by
    the block's value, with how many bytes), the cluster and body it
    is in, how many words the last test of the nursery reserved that
    are still free, and the proof that covers them, if this block has
    made one, with how many words of it are used; and the proof that
    covers the program's constants from a word on, with that word. *)
Record bc := mkbc {
  b_label : term;
  b_phis : list term;
  b_insts : list term;
  b_env : ZMap.t term;
  b_yg : term;
  b_proofs : list (term * (term * Z));
  b_root : Z;
  b_seg : Z;
  b_budget : Z;
  b_aproof : option (term * Z);
  b_mproof : option (term * Z)
}.

Definition tmpv (n : term) : term := TApp "tmp" [n].
Definition cst (n : Z) : term := TApp "const" [TInt n].
Definition t_arena : term := tmpv (TAtom "arena").
Definition t_st : term := tmpv (TAtom "st").
Definition t_ne : term := tmpv (TAtom "ne").
Definition tname (k : Z) : term := TAtom ("t" ++ decimal k)%string.
Definition lname (k : Z) : term := TAtom ("b" ++ decimal k)%string.
Definition head_label (f : Z) : term := TAtom ("f" ++ decimal f)%string.

(** A fresh number. *)
Definition fresh (s : st) : Z * st := (s_next s, mkst (s_next s + 1) (s_blocks s) (s_edges s) (s_major s)).

(** n fresh numbers. *)
Fixpoint fresh_n (n : nat) (s : st) : list Z * st :=
  match n with
  | O => ([], s)
  | S n' => let (k, s) := fresh s in let (ks, s) := fresh_n n' s in (k :: ks, s)
  end.

Definition i_let (d : term) (k : string) (o : term) (args : list term) : term :=
  TApp "let" [tmpv d; TAtom k; o; TList args].
Definition o_check (lo hi : Z) (r : string) : term := TApp "check" [TInt lo; TInt hi; TAtom r; TInt 4].
Definition o_load (off : Z) : term := TApp "raw_load" [TAtom "uw"; TInt off].
Definition i_store (off : Z) (v a : term) : term := TApp "raw_store" [TAtom "w"; TInt off; v; tmpv a].
Definition i_flight (d base off : term) : term :=
  TApp "flight" [tmpv d; TAtom "add"; TList [TApp "address" [base]; off]; TApp "lower" [base]].
Definition o_cmp (c : string) : term := TApp "cmp" [TAtom c; TAtom "w"].
Definition j_goto (l : term) : term := TApp "goto" [l].
Definition j_poll (l : term) : term := TApp "goto" [TApp "poll" [l]].
Definition j_branch (v l1 l2 : term) : term := TApp "branch" [v; l1; l2].
Definition j_ret (v : term) : term := TApp "ret" [v].
Definition a_p (v : term) : term := TApp "arg" [TAtom "p"; v].
Definition a_w (v : term) : term := TApp "arg" [TAtom "w"; v].

(** The block b with the instructions is after its own. *)
Definition b_emit (is : list term) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (rev_append is (b_insts b)) (b_env b) (b_yg b) (b_proofs b) (b_root b) (b_seg b) (b_budget b) (b_aproof b) (b_mproof b).

(** The block b with the λANF variable x now the IR value v. *)
Definition b_bind (x : Z) (v : term) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (ZMap.add x v (b_env b)) (b_yg b) (b_proofs b) (b_root b) (b_seg b) (b_budget b) (b_aproof b) (b_mproof b).

(** The block b with the young index yg and the environment env, and
    no proofs (after a call, which ends what checks proved). *)
Definition b_after (env : ZMap.t term) (yg : term) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) env yg [] (b_root b) (b_seg b) 0 None None.

(** The block b with the young index yg, after an allocation of
    words words through the proof q, of which used words were used
    before. *)
Definition b_alloc (yg : term) (words : Z) (q : term) (used : Z) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (b_env b) yg (b_proofs b) (b_root b) (b_seg b)
       (b_budget b - words) (Some (q, used + words)) (b_mproof b).

(** The block b with words words reserved. *)
Definition b_reserve (words : Z) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (b_env b) (b_yg b) (b_proofs b) (b_root b) (b_seg b) words None (b_mproof b).

(** The block b knowing that the proof q covers the program's
    constants from the word base on. *)
Definition b_mprove (q : term) (base : Z) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (b_env b) (b_yg b) (b_proofs b) (b_root b) (b_seg b)
       (b_budget b) (b_aproof b) (Some (q, base)).

(** The block b knowing that the proof q covers hi bytes of the
    block v. *)
Definition b_prove (v q : term) (hi : Z) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (b_env b) (b_yg b) ((v, (q, hi)) :: b_proofs b) (b_root b) (b_seg b) (b_budget b) (b_aproof b) (b_mproof b).

(** A new block l after b: in its cluster and body, with its
    variables, young index and reserved words, and no proofs. *)
Definition b_next (l : term) (phis : list term) (b : bc) : bc :=
  mkbc l phis [] (b_env b) (b_yg b) [] (b_root b) (b_seg b) (b_budget b) None None.

(** The state with the block b finished by the jump j. *)
Definition finish (b : bc) (j : term) (s : st) : st :=
  mkst (s_next s) (mkpb (b_label b) (b_phis b) (rev (b_insts b)) j :: s_blocks s) (s_edges s) (s_major s).

(** The state with an edge into l from pred, with the values vs. *)
Definition add_edge (l pred : term) (vs : list term) (s : st) : st :=
  let old := match nm_find l (s_edges s) with Some es => es | None => [] end in
  mkst (s_next s) (s_blocks s) (nm_add l ((pred, vs) :: old) (s_edges s)) (s_major s).

(** Whether the variable x is one of the program's constants: in the
    program's body, which runs once, and bound to a constant. *)
Definition is_closed (c : cl) (b : bc) (x : Z) : bool :=
  (b_root b =? 0) && (b_seg b =? 0) && ZMap.mem x (cl_closed c).

Definition t_mj : term := tmpv (TAtom "mj").
Definition t_mj2 : term := tmpv (TAtom "mj2").

(** The constructor of the tag t. *)
Definition ctor_of (c : cl) (t : Z) : res ctor :=
  match ZMap.find t (cl_ctors c) with
  | Some k => Ok k
  | None => Err ("an unknown constructor tag " ++ decimal t)%string
  end.

(** The IR value of the λANF variable x: its binding, or the
    immediate fid of the function x. *)
Definition val_of (c : cl) (b : bc) (x : Z) : res term :=
  match ZMap.find x (b_env b) with
  | Some v => Ok v
  | None =>
      match ZMap.find x (cl_fns c) with
      | Some fi =>
          match fi_fid fi with
          | Some k => Ok (cst (2 * k + 1))
          | None => Err ("a function used as a value without a fid: " ++ decimal x)%string
          end
      | None => Err ("an unbound variable " ++ decimal x)%string
      end
  end.

(** The IR values of the variables xs. *)
Fixpoint vals (c : cl) (b : bc) (xs : list Z) : res (list term) :=
  match xs with
  | [] => Ok []
  | x :: xs' => let? v := val_of c b x in let? vs := vals c b xs' in Ok (v :: vs)
  end.

(** Whether v is a constant. *)
Definition is_const (v : term) : bool := match v with TApp "const" _ => true | _ => false end.

(** Whether v is among vs. *)
Definition mem_term (v : term) (vs : list term) : bool := existsb (term_eqb v) vs.

(** The IR values of the live variables xs that may be blocks, each
    once: what a collection must see and may move. A function's name
    is never one, nor one of the program's constants. *)
Definition live_vals (c : cl) (b : bc) (xs : list Z) : res (list term) :=
  let? vs := vals c b (filter (fun x => (ZMap.mem x (b_env b) || negb (ZMap.mem x (cl_fns c)))
                                        && negb (is_closed c b x)) xs) in
  Ok (rev (fold_left (fun acc v => if is_const v || mem_term v acc then acc else v :: acc) vs [])).

(** The environment env with each variable of xs whose value is one
    of olds given the new value at the same place in news. *)
Definition rebind (xs : list Z) (olds news : list term) (env : ZMap.t term) : ZMap.t term :=
  let pairs := combine olds news in
  fold_left
    (fun env x =>
       match ZMap.find x env with
       | Some v =>
           match find (fun p => term_eqb (fst p) v) pairs with
           | Some (_, v') => ZMap.add x v' env
           | None => env
           end
       | None => env
       end) xs env.

(** The instructions that store the values vs at the proof a, from the
    byte offset off on. *)
Fixpoint stores (off : Z) (vs : list term) (a : term) : list term :=
  match vs with
  | [] => []
  | v :: vs' => i_store off v a :: stores (off + 4) vs' a
  end.

(** The instructions that load n words at the proof a, from the byte
    offset off on, into the temporaries ks. *)
Fixpoint loads (off : Z) (ks : list Z) (a : term) : list term :=
  match ks with
  | [] => []
  | k :: ks' => i_let (tname k) "w" (o_load off) [tmpv a] :: loads (off + 4) ks' a
  end.

(** The instructions that make the pointer to the arena's word idx,
    and that pointer's temporary. *)
Definition addr_of_idx (idx : term) (s : st) : list term * term * st :=
  let (k1, s) := fresh s in
  let (k2, s) := fresh s in
  let (k3, s) := fresh s in
  ([i_let (tname k1) "l" (TApp "ext" [TAtom "uw"]) [idx];
    i_let (tname k2) "l" (TAtom "shl") [tmpv (tname k1); cst 2];
    i_flight (tname k3) t_arena (tmpv (tname k2))], tname k3, s).

(** The instructions of a call that a collection may run in: the young
    index yg stored to the state, the values vs pushed onto the shadow
    roots, the call, then the young index and the values, perhaps
    moved, read back and the roots popped. Also the values' new
    temporaries and the new young index. *)
Definition around_call (vs : list term) (call : term) (yg : term) (s : st)
  : list term * list term * term * st :=
  let n := Z.of_nat (length vs) in
  let (q0, s) := fresh s in
  let (q1, s) := fresh s in
  let (yg', s) := fresh s in
  let pre_state := [i_let (tname q0) "a" (o_check 0 24 "write") [t_st]; i_store 0 yg (tname q0)] in
  let post_state := [i_let (tname q1) "a" (o_check 0 24 "write") [t_st];
                     i_let (tname yg') "w" (o_load 0) [tmpv (tname q1)]] in
  match vs with
  | [] => (pre_state ++ call :: post_state, [], tmpv (tname yg'), s)
  | _ =>
      let (sp, s) := fresh s in
      let (sp64, s) := fresh s in
      let (off, s) := fresh s in
      let (off2, s) := fresh s in
      let (rp, s) := fresh s in
      let (qr, s) := fresh s in
      let (sp2, s) := fresh s in
      let (qr2, s) := fresh s in
      let (ks, s) := fresh_n (length vs) s in
      let push :=
        [i_let (tname sp) "w" (o_load 20) [tmpv (tname q0)];
         i_let (tname sp64) "l" (TApp "ext" [TAtom "uw"]) [tmpv (tname sp)];
         i_let (tname off) "l" (TAtom "shl") [tmpv (tname sp64); cst 2];
         i_let (tname off2) "l" (TAtom "add") [tmpv (tname off); cst 64];
         i_flight (tname rp) t_st (tmpv (tname off2));
         i_let (tname qr) "a" (o_check 0 (4 * n) "write") [tmpv (tname rp)]]
        ++ stores 0 vs (tname qr)
        ++ [i_let (tname sp2) "w" (TAtom "add") [tmpv (tname sp); cst n];
            i_store 20 (tmpv (tname sp2)) (tname q0)] in
      let pop :=
        [i_store 20 (tmpv (tname sp)) (tname q1);
         i_let (tname qr2) "a" (o_check 0 (4 * n) "read") [tmpv (tname rp)]]
        ++ loads 0 ks (tname qr2) in
      (pre_state ++ push ++ call :: post_state ++ pop,
       map (fun k => tmpv (tname k)) ks, tmpv (tname yg'), s)
  end.

(** The words the expression e allocates in the nursery before its
    first call, on its longest path; closed tells the constants, which
    are not in the nursery. *)
Fixpoint need (c : cl) (closed : Z -> bool) (e : exp) : Z :=
  match e with
  | Econstr x t _ e' =>
      let a := match ZMap.find t (cl_ctors c) with Some k => c_arity k | None => 0 end in
      (if (a =? 0) || closed x then 0 else a + 1) + need c closed e'
  | Ecase _ arms =>
      (fix go (l : list (Z * exp)) : Z :=
         match l with [] => 0 | (_, e1) :: l' => Z.max (need c closed e1) (go l') end) arms
  | Eproj _ _ _ _ e' | Eprim_val _ e' | Eprim _ _ _ e' => need c closed e'
  | _ => 0
  end.

(** The most words one test of the nursery reserves: a stretch that
    allocates more, such as a constant list written out in
    constructors, tests again when it has used them. Any test then
    fits in an empty nursery of this many words. *)
Definition seg_cap : Z := 128.

(** The free variables of e. *)
Fixpoint fv_exp (e : exp) : list Z :=
  match e with
  | Econstr x _ ys e' => zunion (zset ys) (zremove x (fv_exp e'))
  | Ecase x arms =>
      zinsert x ((fix go (l : list (Z * exp)) : list Z :=
                    match l with [] => [] | (_, e1) :: l' => zunion (fv_exp e1) (go l') end) arms)
  | Eproj x _ _ y e' => zinsert y (zremove x (fv_exp e'))
  | Eletapp _ f _ ys live _ => zinsert f (zunion (zset ys) live)
  | Efun _ e' => fv_exp e'
  | Eapp f _ ys => zinsert f (zset ys)
  | Eprim_val x e' => zremove x (fv_exp e')
  | Eprim x _ ys e' => zunion (zset ys) (zremove x (fv_exp e'))
  | Ehalt x => [x]
  end.

(** The highest field of y that the projections at the start of e
    read, before y is bound again or anything but a projection or a
    constructor; -1 if none. *)
Fixpoint proj_max (y : Z) (e : exp) : Z :=
  match e with
  | Eproj x _ n y' e' =>
      let m := if y' =? y then n else -1 in
      if x =? y then m else Z.max m (proj_max y e')
  | Econstr x _ _ e' => if x =? y then -1 else proj_max y e'
  | _ => -1
  end.

(** A proof that covers hi bytes of the block v, if b has one. *)
Fixpoint proof_for (v : term) (hi : Z) (ps : list (term * (term * Z))) : option term :=
  match ps with
  | [] => None
  | (v', (q, hi')) :: ps' => if term_eqb v v' && (hi <=? hi') then Some q else proof_for v hi ps'
  end.

(** The head of a stretch without a call that reserves n words, whose
    live variables are xs: the test of the nursery, and the slow path
    that collects. Gives the block that goes on, the live values in
    its phis, with n words to allocate. *)
Definition seg_head (c : cl) (n : Z) (xs : list Z) (b : bc) (s : st) : res (bc * st) :=
  if n <=? 0 then Ok (b, s)
  else
    let? vs := live_vals c b xs in
    let (k_end, s) := fresh s in
    let (k_over, s) := fresh s in
    let (lslow, s) := fresh s in
    let (lcont, s) := fresh s in
    let b := b_emit [i_let (tname k_end) "w" (TAtom "add") [b_yg b; cst n];
                     i_let (tname k_over) "w" (o_cmp "ugt") [tmpv (tname k_end); t_ne]] b in
    let s := finish b (j_branch (tmpv (tname k_over)) (lname lslow) (lname lcont)) s in
    let s := add_edge (lname lcont) (b_label b) (b_yg b :: vs) s in
    let call := TApp "call" [TAtom "void"; TApp "global" [TAtom "anf_lower_reserve"];
                             TList [a_p t_arena; a_p t_st; a_w (cst n)]] in
    let '(is, vs', yg', s) := around_call vs call (b_yg b) s in
    let s := finish (b_emit is (b_next (lname lslow) [] b)) (j_goto (lname lcont)) s in
    let s := add_edge (lname lcont) (lname lslow) (yg' :: vs') s in
    let (ks, s) := fresh_n (S (length vs)) s in
    let news := map (fun k => tmpv (tname k)) (tl ks) in
    let yg := tmpv (tname (hd 0 ks)) in
    Ok (b_reserve n (b_after (rebind xs vs news (b_env b)) yg (b_next (lname lcont) (map tname ks) b)), s).

(** The chain of tests of the value v against each case's value,
    each going to its label; the last case is the default. *)
Fixpoint chain (v : term) (cases : list (Z * term)) (b : bc) (s : st) : st :=
  match cases with
  | [] => finish b (TAtom "unreachable") s
  | [(_, l)] => finish b (j_goto l) s
  | (k, l) :: rest =>
      let (kc, s) := fresh s in
      let (kn, s) := fresh s in
      let b' := b_emit [i_let (tname kc) "w" (o_cmp "eq") [v; cst k]] b in
      let s := finish b' (j_branch (tmpv (tname kc)) l (lname kn)) s in
      chain v rest (b_next (lname kn) [] b) s
  end.

(** The dispatch on the boxed block v among the boxed cases (ordinal,
    label): on its header's ordinal when there are two or more. *)
Definition box_dispatch (v : term) (boxes : list (Z * term)) (b : bc) (s : st) : st :=
  match boxes with
  | _ :: _ :: _ =>
      let (ki, s) := fresh s in
      let '(is, p, s) := addr_of_idx (tmpv (tname ki)) s in
      let (kq, s) := fresh s in
      let (kh, s) := fresh s in
      let (ko, s) := fresh s in
      let b := b_emit ([i_let (tname ki) "w" (TAtom "shr") [v; cst 1]] ++ is ++
                       [i_let (tname kq) "a" (o_check 0 4 "read") [tmpv p];
                        i_let (tname kh) "w" (o_load 0) [tmpv (tname kq)];
                        i_let (tname ko) "w" (TAtom "and") [tmpv (tname kh); cst 255]]) b in
      chain (tmpv (tname ko)) boxes b s
  | _ => chain v boxes b s
  end.

(** The constructors of the arms (tag, label), split into immediates
    (value, label) and boxed (ordinal, label). *)
Fixpoint split_arms (c : cl) (arms : list (Z * term)) : res (list (Z * term) * list (Z * term)) :=
  match arms with
  | [] => Ok ([], [])
  | (t, l) :: arms' =>
      let? k := ctor_of c t in
      let? (imms, boxes) := split_arms c arms' in
      if c_arity k =? 0 then Ok ((2 * c_ord k + 1, l) :: imms, boxes)
      else if 256 <=? c_ord k then Err "a boxed ordinal above 255"
      else Ok (imms, (c_ord k, l) :: boxes)
  end.

(** The dispatch of a case on v to its arms (tag, label). *)
Definition dispatch (c : cl) (v : term) (arms : list (Z * term)) (b : bc) (s : st) : res st :=
  match arms with
  | [] => Ok (finish b (TAtom "unreachable") s)
  | (t, _) :: _ =>
      let? k := ctor_of c t in
      let '(has_imm, has_box, _) :=
        match ZMap.find (c_ind k) (cl_inds c) with Some i => i | None => (true, true, 0) end in
      let? (imms, boxes) := split_arms c arms in
      if has_imm && has_box then
        let (kt, s) := fresh s in
        let (li, s) := fresh s in
        let (lb, s) := fresh s in
        let b' := b_emit [i_let (tname kt) "w" (TAtom "and") [v; cst 1]] b in
        let s := finish b' (j_branch (tmpv (tname kt)) (lname li) (lname lb)) s in
        let s := chain v imms (b_next (lname li) [] b) s in
        Ok (box_dispatch v boxes (b_next (lname lb) [] b) s)
      else if has_box then Ok (box_dispatch v boxes b s)
      else Ok (chain v imms b s)
  end.

(** The IR function a call of the function f with the values vs goes
    to, and its arguments after the arena and state: f's own, or the
    dispatcher of its arity with the closure code's fid first. *)
Definition callee (c : cl) (b : bc) (f : Z) (vs : list term) : res (term * list term) :=
  match ZMap.find f (cl_fns c) with
  | Some fi =>
      if negb (Nat.eqb (length (fi_xs fi)) (length vs)) then
        Err ("a call of " ++ decimal f ++ " with the wrong number of arguments")%string
      else if negb (fi_root fi =? f) then Err ("a call of the absorbed function " ++ decimal f)%string
      else Ok (TAtom (fi_name fi), vs)
  | None =>
      let? vf := val_of c b f in
      Ok (TAtom ("anf_apply" ++ decimal (Z.of_nat (length vs)))%string, vf :: vs)
  end.

(** The call instruction of g with the arguments vs into the
    temporary r. *)
Definition call_inst (r g : term) (vs : list term) : term :=
  TApp "call" [TApp "result" [tmpv r; TAtom "w"]; TApp "global" [g];
               TList (a_p t_arena :: a_p t_st :: map a_w vs)].

(** The instructions that store the young index yg to the state. *)
Definition flush (yg : term) (s : st) : list term * st :=
  let (q, s) := fresh s in
  ([i_let (tname q) "a" (o_check 0 4 "write") [t_st]; i_store 0 yg (tname q)], s).

(** The code of the expression e, in the block b. *)
Fixpoint gen (c : cl) (e : exp) (b : bc) (s : st) {struct e} : res st :=
  match e with
  | Econstr x t ys e' =>
      let? k := ctor_of c t in
      let ar := c_arity k in
      if ar =? 0 then gen c e' (b_bind x (cst (2 * c_ord k + 1)) b) s
      else if is_closed c b x then
        (* A constant: at its own word of the major heap, which the
           program's entry reserved for all of them (from mj on); one
           check covers the words left from the block's first. *)
        let? vs := vals c b ys in
        if negb (Z.of_nat (length vs) =? ar) then Err "a constructor with the wrong number of fields"
        else if 256 <=? c_ord k then Err "a boxed ordinal above 255"
        else
          let off := s_major s in
          let s := mkst (s_next s) (s_blocks s) (s_edges s) (off + ar + 1) in
          let '(is, q, base, s) :=
            match b_mproof b with
            | Some (q, base) => ([], q, base, s)
            | None =>
                let (ki, s) := fresh s in
                let '(is, p, s) := addr_of_idx (tmpv (tname ki)) s in
                let (kq, s) := fresh s in
                ([i_let (tname ki) "w" (TAtom "add") [t_mj; cst off]] ++ is
                 ++ [i_let (tname kq) "a" (o_check 0 (4 * (cl_major c - off)) "write") [tmpv p]],
                 tname kq, off, s)
            end in
          let (kx, s) := fresh s in
          let is := is ++ [i_store (4 * (off - base)) (cst (ar * 1024 + c_ord k)) q]
                       ++ stores (4 * (off - base) + 4) vs q
                       ++ [i_let (tname kx) "w" (TAtom "add") [t_mj2; cst (2 * off)]] in
          gen c e' (b_mprove q base (b_bind x (tmpv (tname kx)) (b_emit is b))) s
      else
        let? (b, s) := if ar + 1 <=? b_budget b then Ok (b, s)
                        else seg_head c (Z.max (ar + 1) (Z.min (need c (is_closed c b) e) seg_cap)) (fv_exp e) b s in
        let? vs := vals c b ys in
        if negb (Z.of_nat (length vs) =? ar) then Err "a constructor with the wrong number of fields"
        else if 256 <=? c_ord k then Err "a boxed ordinal above 255"
        else
          (* One check covers every word the stretch has reserved and
             not used, from the young index on; the constructors after
             this one in the block store through it too. *)
          let '(is, q, used, s) :=
            match b_aproof b with
            | Some (q, used) => ([], q, used, s)
            | None =>
                let '(is, p, s) := addr_of_idx (b_yg b) s in
                let (kq, s) := fresh s in
                (is ++ [i_let (tname kq) "a" (o_check 0 (4 * b_budget b) "write") [tmpv p]], tname kq, 0, s)
            end in
          let (kx, s) := fresh s in
          let (ky, s) := fresh s in
          let is := is ++ [i_store (4 * used) (cst (ar * 1024 + c_ord k)) q]
                       ++ stores (4 * used + 4) vs q
                       ++ [i_let (tname kx) "w" (TAtom "shl") [b_yg b; cst 1];
                           i_let (tname ky) "w" (TAtom "add") [b_yg b; cst (ar + 1)]] in
          gen c e' (b_alloc (tmpv (tname ky)) (ar + 1) q used (b_bind x (tmpv (tname kx)) (b_emit is b))) s
  | Eproj x _ n y e' =>
      let? vy := val_of c b y in
      let (kx, s) := fresh s in
      let load q := i_let (tname kx) "w" (o_load (4 * (n + 1))) [tmpv q] in
      match proof_for vy (4 * (n + 2)) (b_proofs b) with
      | Some q => gen c e' (b_bind x (tmpv (tname kx)) (b_emit [load q] b)) s
      | None =>
          let hi := 4 * (Z.max n (proj_max y e') + 2) in
          let (ki, s) := fresh s in
          let '(is, p, s) := addr_of_idx (tmpv (tname ki)) s in
          let (kq, s) := fresh s in
          let is := [i_let (tname ki) "w" (TAtom "shr") [vy; cst 1]] ++ is ++
                    [i_let (tname kq) "a" (o_check 0 hi "read") [tmpv p];
                     TApp "touch" [tmpv (tname kq)]; load (tname kq)] in
          gen c e' (b_prove vy (tname kq) hi (b_bind x (tmpv (tname kx)) (b_emit is b))) s
      end
  | Ecase x arms =>
      let? vx := val_of c b x in
      let (ks, s) := fresh_n (length arms) s in
      let labels := map lname ks in
      let? s := dispatch c vx (combine (map fst arms) labels) b s in
      (fix go (l : list (Z * exp)) (ls : list term) (s : st) : res st :=
         match l, ls with
         | (_, e1) :: l', lb :: ls' => let? s := gen c e1 (b_next lb [] b) s in go l' ls' s
         | _, _ => Ok s
         end) arms labels s
  | Eletapp x f _ ys live e' =>
      let? vs := vals c b ys in
      let? (g, args) := callee c b f vs in
      let? lvs := live_vals c b live in
      let (r, s) := fresh s in
      let '(is, lvs', yg', s) := around_call lvs (call_inst (tname r) g args) (b_yg b) s in
      let env := ZMap.add x (tmpv (tname r)) (rebind live lvs lvs' (b_env b)) in
      let b := b_after env yg' (b_emit is b) in
      let? (b, s) := seg_head c (Z.min (need c (is_closed c b) e') seg_cap) (x :: live) b s in
      gen c e' b s
  | Eapp f _ ys =>
      let? vs := vals c b ys in
      match ZMap.find f (cl_fns c) with
      | Some fi =>
          if fi_root fi =? b_root b then
            if negb (Nat.eqb (length (fi_xs fi)) (length vs)) then Err "a jump with the wrong number of arguments"
            else
              let l := head_label f in
              let s := add_edge l (b_label b) (b_yg b :: vs) s in
              Ok (finish b (if fi_seg fi <=? b_seg b then j_poll l else j_goto l) s)
          else
            let? (g, args) := callee c b f vs in
            let '(is, s) := flush (b_yg b) s in
            let (r, s) := fresh s in
            Ok (finish (b_emit (is ++ [call_inst (tname r) g args]) b) (j_ret (tmpv (tname r))) s)
      | None =>
          let? (g, args) := callee c b f vs in
          let '(is, s) := flush (b_yg b) s in
          let (r, s) := fresh s in
          Ok (finish (b_emit (is ++ [call_inst (tname r) g args]) b) (j_ret (tmpv (tname r))) s)
      end
  | Ehalt x =>
      let? v := val_of c b x in
      let '(is, s) := flush (b_yg b) s in
      Ok (finish (b_emit is b) (j_ret v) s)
  | Efun _ _ => Err "a nested Efun"
  | Eprim_val _ _ | Eprim _ _ _ _ => Err "a primitive (M3)"
  end.

(** The code of one body of a cluster: the function f, the body seg of
    the cluster of root, with the parameters xs. Its head block's phis
    take the young index and the parameters. *)
Definition gen_body (c : cl) (root seg f : Z) (xs : list Z) (body : exp) (s : st) : res st :=
  let (ks, s) := fresh_n (S (length xs)) s in
  let env := fold_left (fun env p => ZMap.add (fst p) (tmpv (tname (snd p))) env)
                       (combine xs (tl ks)) (ZMap.empty term) in
  let b := mkbc (head_label f) (map tname ks) [] env (tmpv (tname (hd 0 ks))) [] root seg 0 None None in
  let? (b, s) := seg_head c (Z.min (need c (is_closed c b) body) seg_cap) xs b s in
  gen c body b s.

(** [f] applied to each element of xs with its index. *)
Fixpoint mapi {A B : Type} (f : nat -> A -> B) (i : nat) (xs : list A) : list B :=
  match xs with [] => [] | x :: xs' => f i x :: mapi f (S i) xs' end.

(** The block term of pb, its phis built from the edges into it. *)
Definition block_term (s : st) (pb : pblock) : term :=
  let es := match nm_find (pb_label pb) (s_edges s) with Some l => rev l | None => [] end in
  let phi i d := TApp "phi" [tmpv d; TAtom "w";
                             TList (map (fun e => TApp "-" [fst e; nth i (snd e) (cst 0)]) es)] in
  TApp "block" [pb_label pb; TList (mapi phi 0 (pb_phis pb)); TList (pb_insts pb); pb_jump pb].

(** The function term named name with the w parameters ps and the
    blocks of s. *)
Definition func_term (name linkage : string) (ps : list term) (s : st) : term :=
  TApp "func" [TAtom name; TAtom linkage; TAtom "w";
               TList (TApp "param" [TAtom "p"; t_arena] :: TApp "param" [TAtom "p"; t_st]
                      :: map (fun p => TApp "param" [TAtom "w"; tmpv p]) ps);
               TList (map (block_term s) (rev (s_blocks s)))].

(** The IR function of the cluster of root, named name, whose
    parameters are xs and body body, with the absorbed functions
    members, in order. *)
Definition gen_cluster (c : cl) (name linkage : string) (root : Z) (xs : list Z) (body : exp)
  (members : list fdef) : res term :=
  let s := mkst 1 [] nm_empty 0 in
  let (ps, s) := fresh_n (length xs) s in
  let (kq, s) := fresh s in
  let (k0, s) := fresh s in
  let entry := mkbc (TAtom "entry") [] [] (ZMap.empty term) (cst 0) [] root 0 0 None None in
  (* The program's entry reserves the major words of its constants. *)
  let entry :=
    if (root =? 0) && (0 <? cl_major c) then
      b_emit [TApp "call" [TApp "result" [t_mj; TAtom "w"]; TApp "global" [TAtom "anf_lower_major"];
                           TList [a_p t_arena; a_p t_st; a_w (cst (cl_major c))]];
              i_let (TAtom "mj2") "w" (TAtom "shl") [t_mj; cst 1]] entry
    else entry in
  let entry := b_emit [i_let (tname kq) "a" (o_check 0 16 "read") [t_st];
                       i_let (tname k0) "w" (o_load 0) [tmpv (tname kq)];
                       i_let (TAtom "ne") "w" (o_load 12) [tmpv (tname kq)]] entry in
  let s := finish entry (j_goto (head_label root)) s in
  let s := add_edge (head_label root) (TAtom "entry")
             (tmpv (tname k0) :: map (fun k => tmpv (tname k)) ps) s in
  let? s := gen_body c root 0 root xs body s in
  let? (s, _) :=
    fold_left (fun acc fd =>
                 let? (s, seg) := acc in
                 let? s := gen_body c root seg (fd_f fd) (fd_xs fd) (fd_body fd) s in
                 Ok (s, seg + 1)) members (Ok (s, 1)) in
  Ok (func_term name linkage (map tname ps) s).

(** The dispatcher's blocks from the label lbl on: a binary search of
    the fid among the candidates (fid immediate, function name), each
    called with the arguments args. *)
Fixpoint disp (fuel : nat) (args : list term) (cands : list (Z * string)) (lbl : term) (s : st) : st :=
  let blk is j s := mkst (s_next s) (mkpb lbl [] is j :: s_blocks s) (s_edges s) (s_major s) in
  match fuel with
  | O => blk [] (TAtom "unreachable") s
  | S fuel' =>
      match cands with
      | [] => blk [] (TAtom "unreachable") s
      | [(_, f)] =>
          let (r, s) := fresh s in
          blk [call_inst (tname r) (TAtom f) args] (j_ret (tmpv (tname r))) s
      | _ =>
          let k := Nat.div (length cands) 2 in
          let right := skipn k cands in
          let mid := match right with (m, _) :: _ => m | [] => 0 end in
          let (kc, s) := fresh s in
          let (ll, s) := fresh s in
          let (lr, s) := fresh s in
          let s := blk [i_let (tname kc) "w" (o_cmp "ult") [tmpv (TAtom "fid"); cst mid]]
                       (j_branch (tmpv (tname kc)) (lname ll) (lname lr)) s in
          let s := disp fuel' args (firstn k cands) (lname ll) s in
          disp fuel' args right (lname lr) s
      end
  end.

(** The dispatcher of arity n over the candidates (fid immediate,
    function name), sorted by fid. *)
Definition dispatcher (n : nat) (cands : list (Z * string)) : term :=
  let s := mkst 1 [] nm_empty 0 in
  let (ks, s) := fresh_n n s in
  let args := map (fun k => tmpv (tname k)) ks in
  let s := disp (S (length cands)) args cands (TAtom "entry") s in
  func_term ("anf_apply" ++ decimal (Z.of_nat n))%string "local" (TAtom "fid" :: map tname ks) s.

(** ## The module *)

(** The order of integers. *)
Definition zcompare (a b : Z) : comparison := Z.compare a b.

(** What [lower] tells of a program besides its module: how many
    hoisted functions it has, how many of them became blocks of
    another's IR function (joins and loops), and how many are values,
    with a fid. *)
Record counts := mkcounts { n_functions : nat; n_blocks : nat; n_fids : nat }.

(** The module of the program the tap's clauses cs describe: an
    exported `anf_main(arena, st)` that runs the program and returns
    its value, an IR function for each cluster, and a dispatcher for
    each arity a closure is called with. *)
Definition lower (cs : list term) : res (term * counts) :=
  let? p := read_clauses cs (mkprog [] [] None) in
  let? body := match p_body p with Some e => Ok e | None => Err "no anf_body" end in
  let '(fds, main) := match body with
                      | Efun fds e => (fundefs_list fds, e)
                      | e => ([], e)
                      end in
  if negb (forallb flat (main :: map fd_body fds)) then Err "a nested Efun"
  else
    let fnset := fold_left (fun m fd => ZMap.add (fd_f fd) fd m) fds (ZMap.empty fdef) in
    let isfn f := ZMap.mem f fnset in
    let evs := fold_left (fun acc fd => events isfn (fd_f fd) (fd_body fd) acc) fds
                         (events isfn 0 main []) in
    let escapes := zset (flat_map (fun ev => match ev with Escape f => [f] | _ => [] end) evs) in
    let lets := zset (flat_map (fun ev => match ev with LetCall f => [f] | _ => [] end) evs) in
    let arities := Order.sort Nat.compare
                     (flat_map (fun ev => match ev with Indirect n => [n] | _ => [] end) evs) in
    let callers f := flat_map (fun ev => match ev with TailCall c g => if g =? f then [c] else [] | _ => [] end) evs in
    let in_set x xs := existsb (Z.eqb x) xs in
    let cands := flat_map (fun fd =>
                             let f := fd_f fd in
                             if in_set f escapes || in_set f lets then []
                             else match callers f with [] => [] | cs => [(f, cs)] end) fds in
    let fuel := S (length fds) in
    let par := absorb fuel fuel cands (ZMap.empty Z) in
    let rootf f := root_of fuel par f in
    (* fids: the escaping functions, by arity then name *)
    let esc_fds := Order.msort (fun a b => match Nat.compare (length (fd_xs a)) (length (fd_xs b)) with
                                           | Eq => zcompare (fd_f a) (fd_f b)
                                           | o => o
                                           end)
                     (filter (fun fd => in_set (fd_f fd) escapes) fds) in
    let fids := snd (fold_left (fun acc fd => (fst acc + 1, ZMap.add (fd_f fd) (fst acc) (snd acc)))
                               esc_fds (0, ZMap.empty Z)) in
    (* each function's place in its cluster: the root 0, then the
       absorbed ones in order *)
    let members r := filter (fun fd => negb (fd_f fd =? r) && (rootf (fd_f fd) =? r)) fds in
    let seg_of f := let r := rootf f in
                    if r =? f then 0
                    else match find (fun p => fd_f (snd p) =? f) (combine (seq 1 (length (members r))) (members r)) with
                         | Some (i, _) => Z.of_nat i
                         | None => 0
                         end in
    let name_of f := fn_name (p_names p) f in
    let fns := fold_left (fun m fd =>
                            let f := fd_f fd in
                            let r := rootf f in
                            ZMap.add f (mkfi (name_of r) (ZMap.find f fids) r (seg_of f) (fd_xs fd)) m)
                         fds (ZMap.empty fninfo) in
    let ctors := fold_left (fun m tc => ZMap.add (fst tc) (snd tc) m) (p_ctors p) (ZMap.empty ctor) in
    let inds := fold_left (fun m tc =>
                             let k := snd tc in
                             let '(hi, hb, nb) := match ZMap.find (c_ind k) m with
                                                  | Some i => i | None => (false, false, 0) end in
                             ZMap.add (c_ind k)
                               (if c_arity k =? 0 then (true, hb, nb) else (hi, true, nb + 1)) m)
                          (p_ctors p) (ZMap.empty (bool * bool * Z)) in
    let closed := closed_vars isfn main (ZMap.empty unit) in
    let arity t := match ZMap.find t ctors with Some k => c_arity k | None => 0 end in
    let c := mkcl ctors inds fns closed (closed_words arity closed main) in
    let? main_fn := gen_cluster c "anf_main" "export" 0 [] main (members 0) in
    let? fn_items :=
      fold_right (fun fd acc =>
                    let? items := acc in
                    let f := fd_f fd in
                    if rootf f =? f then
                      let? it := gen_cluster c (name_of f) "local" f (fd_xs fd) (fd_body fd) (members f) in
                      Ok (it :: items)
                    else Ok items) (Ok []) fds in
    let disps := map (fun n =>
                        dispatcher n
                          (flat_map (fun fd => if Nat.eqb (length (fd_xs fd)) n then
                                                 match ZMap.find (fd_f fd) fids with
                                                 | Some k => [(2 * k + 1, name_of (fd_f fd))]
                                                 | None => []
                                                 end
                                               else []) esc_fds)) arities in
    Ok (TApp "module" [TList (main_fn :: fn_items ++ disps)],
        mkcounts (length fds) (length (filter (fun fd => negb (rootf (fd_f fd) =? fd_f fd)) fds))
                 (length esc_fds)).

(** ## Examples *)

(** A program that builds the constant `Cons(Nil, Nil)` and returns
    it: its entry reserves the three major words of the constant
    (`anf_lower_major`), and no test of the nursery is needed, so
    `anf_main` has two blocks, the entry and the body. *)
Example lower_constant :
  match lower [TApp "anf_ctor" [TInt 1; TInt 1; TInt 0; TInt 0; TAtom "Nil"];
               TApp "anf_ctor" [TInt 2; TInt 1; TInt 2; TInt 0; TAtom "Cons"];
               TApp "anf_body" [TApp "constr" [TInt 5; TInt 1; TList [];
                 TApp "constr" [TInt 6; TInt 2; TList [TInt 5; TInt 5]; TApp "halt" [TInt 6]]]]] with
  | Ok (TApp "module" [TList [TApp "func" [TAtom "anf_main"; _; _; _;
          TList ((TApp "block" [_; _; TList (TApp "call" [_; TApp "global" [TAtom "anf_lower_major"];
                                                          TList [_; _; TApp "arg" [_; TApp "const" [TInt w]]]]
                                                 :: _); _] :: _) as blocks)]]], _) => Some (length blocks, w)
  | _ => None
  end = Some (2%nat, 3).
Proof. vm_compute. reflexivity. Qed.

(** A function that conses its argument onto `Nil`, called but not
    in tail position, allocates in the nursery: its own IR function
    tests the nursery once, and the slow path collects
    (`anf_lower_reserve`). *)
Example lower_cons :
  match lower [TApp "anf_ctor" [TInt 1; TInt 1; TInt 0; TInt 0; TAtom "Nil"];
               TApp "anf_ctor" [TInt 2; TInt 1; TInt 2; TInt 0; TAtom "Cons"];
               TApp "anf_body" [TApp "fun" [
                 TList [TApp "def" [TInt 7; TInt 1; TList [TInt 8];
                          TApp "constr" [TInt 5; TInt 1; TList [];
                            TApp "constr" [TInt 6; TInt 2; TList [TInt 8; TInt 5]; TApp "halt" [TInt 6]]]]];
                 TApp "constr" [TInt 9; TInt 1; TList [];
                   TApp "letapp" [TInt 10; TInt 7; TInt 1; TList [TInt 9];
                     TApp "constr" [TInt 11; TInt 2; TList [TInt 10; TInt 9]; TApp "halt" [TInt 11]]]]]]] with
  | Ok (TApp "module" [TList [_; TApp "func" [_; _; _; _; TList blocks]]], _) =>
      Some (length blocks,
            length (filter (fun bl => match bl with
                                     | TApp "block" [_; _; TList is; _] =>
                                         existsb (fun i => match i with
                                                           | TApp "call" [_; TApp "global" [TAtom "anf_lower_reserve"]; _] => true
                                                           | _ => false
                                                           end) is
                                     | _ => false
                                     end) blocks))
  | _ => None
  end = Some (4%nat, 1%nat).
Proof. vm_compute. reflexivity. Qed.
