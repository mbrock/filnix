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
    | `anf_ctor(T, I, A, O, Name, IndName)` | constructor tag T of inductive I, arity A, ordinal O (M2's taps wrote it without IndName) |
    | `anf_prim(P, Target, A, Alloc, Const)` | the primitive P, the constant Const that `CertiRocq Register` realizes as Target |
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

    A function that is a value has a fid; the fids of one arity are
    consecutive. A call through a closure's code loads the function
    from the table of its arity (`anf_fnsN`) at its fid and calls it
    through the pointer; `anf_applyN` does the same for a driver in C.

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
    run of projections from one block shares one check.

    ## Numbers, characters, strings and primitives (M3)

    The stdlib's `nat`, `positive`, `N`, `Z`, `ascii` and `string` are
    represented as integers, codes and bytes rather than as their
    constructors (see Representations below), the constants CertiRocq
    leaves as primitives (`anf_prim`, named by anf/lower/Prims.v and
    by a program's own `CertiRocq Register`) are lowered by
    [prim_table], inline or as calls of anf_prims.c, and a program's
    constants are folded into a pool its entry copies to the major
    heap. *)

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
    tags as integers. [Eletapp] and [Eprim] also hold the variables
    live after them: the free variables of the continuation without
    the result, which a primitive that allocates must keep across a
    collection as a call does. A primitive value is kept as its
    text. *)
Inductive exp : Type :=
| Econstr (x t : Z) (ys : list Z) (e : exp)
| Ecase (x : Z) (arms : list (Z * exp))
| Eproj (x t n y : Z) (e : exp)
| Eletapp (x f ft : Z) (ys : list Z) (live : list Z) (e : exp)
| Efun (fds : fundefs) (e : exp)
| Eapp (f ft : Z) (ys : list Z)
| Eprim_val (x : Z) (e : exp)
| Eprim (x p : Z) (ys : list Z) (live : list Z) (e : exp)
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
            let live := zremove x fv in
            Ok (Eprim x p ys live e, zunion (zset ys) live)
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

(** What a constructor tag says: its inductive, arity and ordinal, and
    its own and its inductive's names. *)
Record ctor := mkctor { c_ind : Z; c_arity : Z; c_ord : Z; c_name : string; c_iname : string }.

(** The program the tap's clauses describe, with the target name of
    each primitive. *)
Record prog := mkprog {
  p_ctors : list (Z * ctor);
  p_prims : list (Z * string);
  p_names : list (Z * string);
  p_body : option exp
}.

(** The atom's name, or `_`. *)
Definition atom_name (t : term) : string := match t with TAtom s => s | _ => "_" end.

(** The clauses cs read into the program p. *)
Fixpoint read_clauses (cs : list term) (p : prog) : res prog :=
  match cs with
  | [] => Ok p
  | TApp f args :: cs' =>
      if String.eqb f "anf_ctor" then
        match args with
        | [TInt t; TInt i; TInt a; TInt o; n] =>
            read_clauses cs' (mkprog ((t, mkctor i a o (atom_name n) "_") :: p_ctors p) (p_prims p)
                                     (p_names p) (p_body p))
        | [TInt t; TInt i; TInt a; TInt o; n; ind] =>
            read_clauses cs' (mkprog ((t, mkctor i a o (atom_name n) (atom_name ind)) :: p_ctors p)
                                     (p_prims p) (p_names p) (p_body p))
        | _ => Err "anf_ctor/6"
        end
      else if String.eqb f "anf_prim" then
        match args with
        | [TInt q; TAtom target; _; _; _] =>
            read_clauses cs' (mkprog (p_ctors p) ((q, target) :: p_prims p) (p_names p) (p_body p))
        | _ => Err "anf_prim/5"
        end
      else if String.eqb f "anf_name" then
        match args with
        | [TInt v; TAtom s] => read_clauses cs' (mkprog (p_ctors p) (p_prims p) ((v, s) :: p_names p) (p_body p))
        | _ => Err "anf_name/2"
        end
      else if String.eqb f "anf_body" then
        match args with
        | [e1] => let? (e, _) := dexp e1 in read_clauses cs' (mkprog (p_ctors p) (p_prims p) (p_names p) (Some e))
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
  | Eprim_val _ e' | Eprim _ _ _ _ e' => flat e'
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
  | Eprim _ _ ys _ e' => events isfn cur e' (esc ys acc)
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

(** ## Representations

    The stdlib's numbers, characters and strings are not kept as
    their constructors (M3 of docs/lambda-anf.md). An inductive is
    represented this way when its name and its constructors' names
    and arities are those of the stdlib's, which is how the tap
    identifies it ([ctor] has the inductive's name):

    | Inductive | Constructors | A value is |
    |---|---|---|
    | `nat`, `positive`, `N`, `Z` | `O`, `S`; `xI`, `xO`, `xH`; `N0`, `Npos`; `Z0`, `Zpos`, `Zneg` | the integer, as anf_arena.h's `Z`: an immediate `(v << 1) \| 1` for -2^30 <= v < 2^30, else an `ANF_ST_BIGINT` block |
    | `ascii` | `Ascii` (8 bools) | the immediate of its code, as a `Byte.byte` |
    | `string` | `EmptyString`, `String` | the immediate 0 when empty, else an `ANF_ST_BYTES` block of its bytes, or a slice of one (anf_prims.c) |

    So `Zpos p` and `Npos p` are p itself, `S n` is n + 1, `xO p` is
    2p, `nat_of_ascii` is the identity, and a match on a number tests
    its value. A constructor of these inductives may take a call when
    its value leaves the immediates; a projection of `String`'s rest
    is a call that copies it when it is short and makes a slice of
    the same bytes when it is not, so a match down a string costs as
    much as the string is long. Roles are numbers: *)
Definition r_plain : Z := 0.
Definition r_O : Z := 1.
Definition r_S : Z := 2.
Definition r_xI : Z := 3.
Definition r_xO : Z := 4.
Definition r_xH : Z := 5.
Definition r_N0 : Z := 6.
Definition r_Npos : Z := 7.
Definition r_Z0 : Z := 8.
Definition r_Zpos : Z := 9.
Definition r_Zneg : Z := 10.
Definition r_ascii : Z := 11.
Definition r_empty : Z := 12.
Definition r_string : Z := 13.

(** The constructors an inductive named iname must have, by name and
    arity, to be represented as above, each with its role. *)
Definition mapped_shape (iname : string) : list (string * Z * Z) :=
  if String.eqb iname "nat" then [("O"%string, 0, r_O); ("S"%string, 1, r_S)]
  else if String.eqb iname "positive" then [("xI"%string, 1, r_xI); ("xO"%string, 1, r_xO); ("xH"%string, 0, r_xH)]
  else if String.eqb iname "N" then [("N0"%string, 0, r_N0); ("Npos"%string, 1, r_Npos)]
  else if String.eqb iname "Z" then [("Z0"%string, 0, r_Z0); ("Zpos"%string, 1, r_Zpos); ("Zneg"%string, 1, r_Zneg)]
  else if String.eqb iname "ascii" then [("Ascii"%string, 8, r_ascii)]
  else if String.eqb iname "string" then [("EmptyString"%string, 0, r_empty); ("String"%string, 2, r_string)]
  else [].

(** The roles of the constructor tags of one inductive, ks, if it has
    exactly the constructors of its [mapped_shape]. *)
Definition shape_roles (ks : list (Z * ctor)) : option (string * list (Z * Z)) :=
  match ks with
  | [] => None
  | (_, k0) :: _ =>
      let sh := mapped_shape (c_iname k0) in
      if negb (Nat.eqb (length sh) (length ks)) then None
      else
        match fold_right
                (fun tk acc =>
                   match acc with
                   | None => None
                   | Some rs =>
                       let '(t, k) := tk in
                       match find (fun x => let '(n, a, _) := x in String.eqb n (c_name k) && (a =? c_arity k)) sh with
                       | Some (_, _, r) => Some ((t, r) :: rs)
                       | None => None
                       end
                   end) (Some []) ks with
        | Some rs => Some (c_iname k0, rs)
        | None => None
        end
  end.

(** The role of each constructor tag the program represents as above:
    `N` and `Z` only with `positive`, and `string` only with
    `ascii`. *)
Definition roles (ctors : list (Z * ctor)) : ZMap.t Z :=
  let by_ind := fold_left (fun m tk =>
                             let k := snd tk in
                             ZMap.add (c_ind k) (tk :: match ZMap.find (c_ind k) m with Some l => l | None => [] end) m)
                          ctors (ZMap.empty (list (Z * ctor))) in
  let shaped := ZMap.fold (fun _ ks acc => match shape_roles ks with Some r => r :: acc | None => acc end)
                          by_ind [] in
  let has (n : string) := existsb (fun r => String.eqb (fst r) n) shaped in
  fold_left (fun m r =>
               let '(n, rs) := r in
               if ((String.eqb n "N"%string || String.eqb n "Z"%string) && negb (has "positive"%string))
                  || (String.eqb n "string"%string && negb (has "ascii"%string)) then m
               else fold_left (fun m tr => ZMap.add (fst tr) (snd tr) m) rs m)
            shaped (ZMap.empty Z).

(** The immediate of the constructor named cname of the inductive
    named iname, which takes no arguments, or dflt if the program has
    none. *)
Definition ctor_word (ctors : list (Z * ctor)) (iname cname : string) (dflt : Z) : Z :=
  match find (fun tk => String.eqb (c_iname (snd tk)) iname && String.eqb (c_name (snd tk)) cname) ctors with
  | Some (_, k) => 2 * c_ord k + 1
  | None => dflt
  end.

(** The header of a block of the constructor named cname of the
    inductive named iname, or dflt. *)
Definition ctor_header (ctors : list (Z * ctor)) (iname cname : string) (dflt : Z) : Z :=
  match find (fun tk => String.eqb (c_iname (snd tk)) iname && String.eqb (c_name (snd tk)) cname) ctors with
  | Some (_, k) => c_arity k * 1024 + c_ord k
  | None => dflt
  end.

(** ## Constants

    A variable bound by a constructor whose fields are all constants
    is a constant, as is the result of a primitive on constant
    integers that [kprim] folds: its value is known when the program
    is lowered. A constant that is not an immediate goes in the
    [[lambda-anf|pool]], the block of words that the program's entry
    copies to the bottom of the major heap (anf_lower_pool), from
    word 1 on, where a collection never moves it: its value is then
    a number too, no test of the nursery waits for it and no call
    spills it, as OCaml makes such constants static data. A string
    literal, a chain of `String` constructors, is one block of
    bytes. *)
Inductive cval : Type :=
| KW (w : Z)
| KInt (z : Z)
| KStr (bs : list Z)
| KBlk (hdr : Z) (fs : list cval).

(** Whether the integer z is an immediate. *)
Definition small (z : Z) : bool := (- 2 ^ 30 <=? z) && (z <? 2 ^ 30).

(** What folding constants reads: the constructors and their roles,
    the immediates of `true` and `false`, the functions with a fid,
    and each primitive's target. *)
Record kctx := mkkc {
  kc_ctors : ZMap.t ctor;
  kc_roles : ZMap.t Z;
  kc_true : Z;
  kc_false : Z;
  kc_fids : ZMap.t Z;
  kc_prims : ZMap.t string
}.

(** The role of the constructor tag t. *)
Definition role_of (roles : ZMap.t Z) (t : Z) : Z :=
  match ZMap.find t roles with Some r => r | None => r_plain end.

(** The bytes of the string constant k. *)
Definition kbytes (k : cval) : option (list Z) :=
  match k with KW w => if w =? 1 then Some [] else None | KStr bs => Some bs | _ => None end.

(** The code of the character whose eight bools are the immediates
    ws, low bit first. *)
Fixpoint ascii_code (kc : kctx) (i : Z) (fs : list cval) : option Z :=
  match fs with
  | [] => Some 0
  | KW w :: fs' =>
      match ascii_code kc (i + 1) fs' with
      | Some n => if w =? kc_true kc then Some (n + 2 ^ i) else if w =? kc_false kc then Some n else None
      | None => None
      end
  | _ :: _ => None
  end.

(** The constant a constructor of the tag t, k, makes of the constant
    fields fs, if it is one. *)
Definition kconstr (kc : kctx) (t : Z) (k : ctor) (fs : list cval) : option cval :=
  let r := role_of (kc_roles kc) t in
  if r =? r_plain then
    if c_arity k =? 0 then Some (KW (2 * c_ord k + 1))
    else if (c_ord k <? 256) && Nat.eqb (length fs) (Z.to_nat (c_arity k)) then Some (KBlk (c_arity k * 1024 + c_ord k) fs)
    else None
  else if (r =? r_O) || (r =? r_N0) || (r =? r_Z0) then Some (KInt 0)
  else if r =? r_xH then Some (KInt 1)
  else if r =? r_empty then Some (KW 1)
  else if r =? r_ascii then match ascii_code kc 0 fs with Some n => Some (KW (2 * n + 1)) | None => None end
  else
    match fs with
    | [KInt z] =>
        if r =? r_S then Some (KInt (z + 1))
        else if r =? r_xI then Some (KInt (2 * z + 1))
        else if r =? r_xO then Some (KInt (2 * z))
        else if (r =? r_Npos) || (r =? r_Zpos) then Some (KInt z)
        else if r =? r_Zneg then Some (KInt (- z))
        else None
    | [KW c; s] =>
        if r =? r_string then match kbytes s with Some bs => Some (KStr (Z.shiftr c 1 :: bs)) | None => None end
        else None
    | _ => None
    end.

(** The constant of the primitive named target on the constant
    integers zs, for those whose value is an integer and that cannot
    fail; the rest are left to run. *)
Definition kprim (target : string) (zs : list Z) : option cval :=
  match zs with
  | [a] =>
      if String.eqb target "nf_succ" then Some (KInt (a + 1))
      else if String.eqb target "nf_pred" then Some (KInt (a - 1))
      else if String.eqb target "nf_neg" then Some (KInt (- a))
      else if String.eqb target "nf_id" then Some (KInt a)
      else None
  | [a; b] =>
      if String.eqb target "nf_add" then Some (KInt (a + b))
      else if String.eqb target "nf_sub" then Some (KInt (a - b))
      else if String.eqb target "nf_mul" then Some (KInt (a * b))
      else if String.eqb target "nf_pow" then if (0 <=? b) && (b <=? 256) then Some (KInt (a ^ b)) else None
      else if String.eqb target "nf_shiftl" then if (-256 <=? b) && (b <=? 256) then Some (KInt (Z.shiftl a b)) else None
      else if String.eqb target "nf_land" then Some (KInt (Z.land a b))
      else if String.eqb target "nf_lor" then Some (KInt (Z.lor a b))
      else None
  | _ => None
  end.

(** The constants of the variables ys, if they all are: bound in kv,
    or functions with a fid. *)
Fixpoint kvals (kc : kctx) (kv : ZMap.t cval) (ys : list Z) : option (list cval) :=
  match ys with
  | [] => Some []
  | y :: ys' =>
      let k := match ZMap.find y kv with
               | Some k => Some k
               | None => match ZMap.find y (kc_fids kc) with Some fid => Some (KW (2 * fid + 1)) | None => None end
               end in
      match k, kvals kc kv ys' with
      | Some k, Some ks => Some (k :: ks)
      | _, _ => None
      end
  end.

(** The integers of the constants ks, if they all are integers. *)
Fixpoint kints (ks : list cval) : option (list Z) :=
  match ks with
  | [] => Some []
  | KInt z :: ks' => match kints ks' with Some zs => Some (z :: zs) | None => None end
  | _ :: _ => None
  end.

(** The constants of the expression e, added to kv. *)
Fixpoint kfold (kc : kctx) (e : exp) (kv : ZMap.t cval) : ZMap.t cval :=
  match e with
  | Econstr x t ys e' =>
      let kv := match ZMap.find t (kc_ctors kc), kvals kc kv ys with
                | Some k, Some fs => match kconstr kc t k fs with Some v => ZMap.add x v kv | None => kv end
                | _, _ => kv
                end in
      kfold kc e' kv
  | Eprim x p ys _ e' =>
      let kv := match ZMap.find p (kc_prims kc), option_map kints (kvals kc kv ys) with
                | Some target, Some (Some zs) =>
                    match kprim target zs with Some v => ZMap.add x v kv | None => kv end
                | _, _ => kv
                end in
      kfold kc e' kv
  | Ecase _ arms =>
      (fix go (l : list (Z * exp)) (kv : ZMap.t cval) : ZMap.t cval :=
         match l with [] => kv | (_, e1) :: l' => go l' (kfold kc e1 kv) end) arms kv
  | Eproj _ _ _ _ e' | Eletapp _ _ _ _ _ e' | Efun _ e' | Eprim_val _ e' => kfold kc e' kv
  | Eapp _ _ _ | Ehalt _ => kv
  end.

(** Whether the constant k needs a place in the pool. *)
Definition pooled (k : cval) : bool :=
  match k with KW _ => false | KInt z => negb (small z) | _ => true end.

(** The constants of kv that the expression e uses as values, rather
    than only as fields of other constants, added to acc: those the
    pool holds. *)
Fixpoint kuses (kv : ZMap.t cval) (e : exp) (acc : ZMap.t unit) : ZMap.t unit :=
  let use y acc := match ZMap.find y kv with
                   | Some k => if pooled k then ZMap.add y tt acc else acc
                   | None => acc
                   end in
  let uses ys acc := fold_left (fun acc y => use y acc) ys acc in
  match e with
  | Econstr x _ ys e' => kuses kv e' (if ZMap.mem x kv then acc else uses ys acc)
  | Eprim x _ ys _ e' => kuses kv e' (if ZMap.mem x kv then acc else uses ys acc)
  | Ecase x arms =>
      (fix go (l : list (Z * exp)) (acc : ZMap.t unit) : ZMap.t unit :=
         match l with [] => acc | (_, e1) :: l' => go l' (kuses kv e1 acc) end) arms (use x acc)
  | Eproj _ _ _ y e' => kuses kv e' (use y acc)
  | Eletapp _ f _ ys _ e' => kuses kv e' (uses ys (use f acc))
  | Eapp f _ ys => uses ys (use f acc)
  | Ehalt x => use x acc
  | Efun _ e' | Eprim_val _ e' => kuses kv e' acc
  end.

(** ## The pool *)

(** The pool so far: its words, last first, the arena index of its
    next word, and the value of each constant it holds, by a term
    that writes the constant. *)
Record pool := mkpool { pl_words : list Z; pl_next : Z; pl_map : nmap Z }.

(** The empty pool, whose first block is at word 1 of the arena. *)
Definition pool0 : pool := mkpool [] 1 nm_empty.

(** The pool with the block ws added, the constant key: the block's
    value. *)
Definition pl_emit (key : term) (ws : list Z) (pl : pool) : Z * pool :=
  let idx := pl_next pl in
  (2 * idx, mkpool (rev_append ws (pl_words pl)) (idx + Z.of_nat (length ws)) (nm_add key (2 * idx) (pl_map pl))).

(** The digits of m in base 2^32, low first, at most fuel of them. *)
Fixpoint limbs (fuel : nat) (m : Z) : list Z :=
  match fuel with
  | O => []
  | S f => if m =? 0 then [] else (m mod 2 ^ 32) :: limbs f (m / 2 ^ 32)
  end.

(** The bytes bs packed four to a word, low first. *)
Fixpoint pack (bs : list Z) : list Z :=
  match bs with
  | [] => []
  | [a] => [a]
  | [a; b] => [a + 256 * b]
  | [a; b; c] => [a + 256 * b + 65536 * c]
  | a :: b :: c :: d :: r => (a + 256 * b + 65536 * c + 16777216 * d) :: pack r
  end.

(** The value of the constant k, and the pool with it (and the
    constants it holds) added, each block once. *)
Fixpoint materialize (k : cval) (pl : pool) {struct k} : Z * pool :=
  let find_or key ws pl :=
    match nm_find key (pl_map pl) with Some w => (w, pl) | None => pl_emit key ws pl end in
  match k with
  | KW w => (w, pl)
  | KInt z =>
      if small z then (2 * z + 1, pl)
      else
        let ls := limbs (S (Z.to_nat (Z.log2 (Z.abs z) / 32 + 1))) (Z.abs z) in
        find_or (TApp "int" [TInt z])
                ((Z.of_nat (length ls) * 1024 + 512 + (if z <? 0 then 1 else 0)) :: ls) pl
  | KStr bs =>
      let len := Z.of_nat (length bs) in
      find_or (TApp "str" [TList (map TInt bs)])
              (((1 + (len + 3) / 4) * 1024 + 256) :: len :: pack bs) pl
  | KBlk hdr fs =>
      let '(ws, pl) :=
        (fix go (fs : list cval) (pl : pool) : list Z * pool :=
           match fs with
           | [] => ([], pl)
           | f :: fs' => let (w, pl) := materialize f pl in let (ws, pl) := go fs' pl in (w :: ws, pl)
           end) fs pl in
      find_or (TApp "blk" [TInt hdr; TList (map TInt ws)]) (hdr :: ws) pl
  end.

(** The pool's data item: its number of words, then the words, each
    as an unsigned 32-bit number. *)
Definition pool_item (pl : pool) : term :=
  let ws := rev (pl_words pl) in
  TApp "data" [TAtom "anf_pool"; TApp "ro" [TAtom "local"]; TInt 4;
               TList (map (fun w => TApp "item" [TAtom "w"; TApp "const" [TInt (w mod 2 ^ 32)]])
                          (Z.of_nat (length ws) :: ws))].

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

(** How a primitive's target is lowered: by its own instructions
    ([PInl]); as a call of the runtime that does not collect whose
    result is a value ([PRt]), a 0 or 1 that makes a bool
    ([PRtBool]), or a -1, 0 or 1 that makes a comparison ([PRtCmp]);
    as two such calls whose results make a pair ([PPair]); or as a
    call that may collect ([PAlloc]), which also takes `nil`'s
    immediate and the header of `cons` when lists is true. Each takes
    the arguments at the indices args. *)
Inductive pkind : Type :=
| PInl (args : list nat)
| PRt (f : string) (args : list nat)
| PRtBool (f : string) (args : list nat)
| PRtCmp (f : string) (args : list nat)
| PPair (f g : string) (args : list nat)
| PAlloc (f : string) (args : list nat) (lists : bool).

(** The lowering of each target the runtime knows. An `nf_` target is
    a function of integers, characters, strings or lists in the
    representation above; anf/lower/Prims.v names the stdlib's
    constants it realizes. *)
Definition prim_table : list (string * pkind) :=
  [("nf_add"%string, PInl [0; 1]); ("nf_sub"%string, PInl [0; 1]); ("nf_succ"%string, PInl [0]); ("nf_pred"%string, PInl [0]);
   ("nf_pred0"%string, PInl [0]); ("nf_neg"%string, PInl [0]); ("nf_max0"%string, PInl [0]); ("nf_id"%string, PInl [0]);
   ("nf_ascii_of_nat"%string, PInl [0]); ("nf_max"%string, PInl [0; 1]); ("nf_min"%string, PInl [0; 1]);
   ("nf_eqb"%string, PInl [0; 1]); ("nf_ltb"%string, PInl [0; 1]); ("nf_leb"%string, PInl [0; 1]);
   ("nf_compare"%string, PInl [0; 1]); ("nf_ascii_eqb"%string, PInl [0; 1]); ("nf_ascii_compare"%string, PInl [0; 1]);
   ("nf_mul"%string, PRt "anf_p_mul" [0; 1]); ("nf_div"%string, PRt "anf_p_div" [0; 1]);
   ("nf_mod"%string, PRt "anf_p_mod" [0; 1]); ("nf_quot"%string, PRt "anf_p_quot" [0; 1]);
   ("nf_rem"%string, PRt "anf_p_rem" [0; 1]); ("nf_sub0"%string, PRt "anf_p_sub0" [0; 1]);
   ("nf_sub1"%string, PRt "anf_p_sub1" [0; 1]); ("nf_pred1"%string, PRt "anf_p_pred1" [0]);
   ("nf_abs"%string, PRt "anf_p_abs" [0]); ("nf_pow"%string, PRt "anf_p_pow" [0; 1]);
   ("nf_land"%string, PRt "anf_p_land" [0; 1]); ("nf_lor"%string, PRt "anf_p_lor" [0; 1]);
   ("nf_lxor"%string, PRt "anf_p_lxor" [0; 1]); ("nf_shiftl"%string, PRt "anf_p_shiftl" [0; 1]);
   ("nf_shiftr"%string, PRt "anf_p_shiftr" [0; 1]); ("nf_testbit"%string, PRtBool "anf_p_testbit" [0; 1]);
   ("nf_even"%string, PRtBool "anf_p_even" [0]); ("nf_odd"%string, PRtBool "anf_p_odd" [0]);
   ("nf_div_eucl"%string, PPair "anf_p_div" "anf_p_mod" [0; 1]);
   ("nf_str_eqb"%string, PRtBool "anf_p_str_eqb" [0; 1]); ("nf_str_compare"%string, PRtCmp "anf_p_str_compare" [0; 1]);
   ("nf_str_length"%string, PRt "anf_p_str_length" [0]); ("nf_str_hash"%string, PRt "anf_p_str_hash" [0; 1]);
   ("nf_list_length"%string, PRt "anf_p_list_length" [1]);
   ("nf_str_append"%string, PAlloc "anf_p_str_append" [0; 1] false);
   ("nf_str_concat"%string, PAlloc "anf_p_str_concat" [0; 1] true);
   ("nf_str_of_list"%string, PAlloc "anf_p_str_of_list" [0] true);
   ("nf_str_of_rev"%string, PAlloc "anf_p_str_of_rev" [0] true);
   ("nf_list_of_str"%string, PAlloc "anf_p_list_of_str" [0] true);
   ("nf_substring"%string, PAlloc "anf_p_substring" [0; 1; 2] false)]%nat.

(** The lowering of the target t, if the runtime knows it. *)
Definition prim_kind (t : string) : option pkind :=
  match find (fun e => String.eqb (fst e) t) prim_table with Some (_, k) => Some k | None => None end.

(** Whether the primitive p makes a pair in the nursery. *)
Definition pair_prim (prims : ZMap.t string) (p : Z) : bool :=
  match ZMap.find p prims with
  | Some t => match prim_kind t with Some (PPair _ _ _) => true | _ => false end
  | None => false
  end.


(** ## Code generation *)

(** What all of a module's code generation reads: the constructors,
    each inductive's kinds of constructors (whether it has immediate
    ones, boxed ones, and how many boxed), the functions, the roles of
    the represented constructors ([roles]), the constants ([kfold])
    with the values of those in the pool, each primitive's target, the
    immediates of `true`, `false`, `Eq`, `Lt` and `Gt`, `nil`'s
    immediate and the headers of `cons` and `pair`, and how many words
    the pool has. *)
Record cl := mkcl {
  cl_ctors : ZMap.t ctor;
  cl_inds : ZMap.t (bool * bool * Z);
  cl_fns : ZMap.t fninfo;
  cl_roles : ZMap.t Z;
  cl_kv : ZMap.t cval;
  cl_kw : ZMap.t Z;
  cl_prims : ZMap.t string;
  cl_true : Z;
  cl_false : Z;
  cl_eq : Z;
  cl_lt : Z;
  cl_gt : Z;
  cl_nil : Z;
  cl_cons : Z;
  cl_pair : Z;
  cl_poolw : Z;
  cl_tbl : list (nat * Z)
}.

(** A finished block, its phis still to be built from the edges. *)
Record pblock := mkpb { pb_label : term; pb_phis : list term; pb_insts : list term; pb_jump : term }.

(** The state of an IR function's generation: the next fresh number,
    the finished blocks, last first, and the edges into each label
    (from which block, with which values for its phis). *)
Record st := mkst {
  s_next : Z;
  s_blocks : list pblock;
  s_edges : nmap (list (term * list term))
}.

(** The block being generated: its label and phis, its instructions
    so far (last first), the IR value of each λANF variable, the
    young index, the [[check]] proofs that cover a block's fields (by
    the block's value, with how many bytes), the cluster and body it
    is in, how many words the last test of the nursery reserved that
    are still free, and the proof that covers them, if this block has
    made one, with how many words of it are used. *)
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
  b_aproof : option (term * Z)
}.

Definition tmpv (n : term) : term := TApp "tmp" [n].
Definition cst (n : Z) : term := TApp "const" [TInt n].
Definition t_arena : term := tmpv (TAtom "arena").
Definition t_st : term := tmpv (TAtom "st").
Definition t_ne : term := tmpv (TAtom "ne").
Definition t_sp : term := tmpv (TAtom "sp").
Definition t_fr : term := tmpv (TAtom "fr").
Definition tname (k : Z) : term := TAtom ("t" ++ decimal k)%string.
Definition lname (k : Z) : term := TAtom ("b" ++ decimal k)%string.
Definition head_label (f : Z) : term := TAtom ("f" ++ decimal f)%string.

(** A fresh number. *)
Definition fresh (s : st) : Z * st := (s_next s, mkst (s_next s + 1) (s_blocks s) (s_edges s)).

(** n fresh numbers. *)
Fixpoint fresh_n (n : nat) (s : st) : list Z * st :=
  match n with
  | O => ([], s)
  | S n' => let (k, s) := fresh s in let (ks, s) := fresh_n n' s in (k :: ks, s)
  end.

Definition i_let (d : term) (k : string) (o : term) (args : list term) : term :=
  TApp "let" [tmpv d; TAtom k; o; TList args].
(** A [[check]] of the bytes lo up to hi at alignment 1: arena and
    state words are 4-aligned by construction (anf_arena.h), and an
    integer access needs no more, so the check tests no alignment. *)
Definition o_check (lo hi : Z) (r : string) : term := TApp "check" [TInt lo; TInt hi; TAtom r; TInt 1].
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
  mkbc (b_label b) (b_phis b) (rev_append is (b_insts b)) (b_env b) (b_yg b) (b_proofs b) (b_root b) (b_seg b) (b_budget b) (b_aproof b).

(** The block b with the λANF variable x now the IR value v. *)
Definition b_bind (x : Z) (v : term) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (ZMap.add x v (b_env b)) (b_yg b) (b_proofs b) (b_root b) (b_seg b) (b_budget b) (b_aproof b).

(** The block b with the young index yg and the environment env, and
    no proofs (after a call, which ends what checks proved). *)
Definition b_after (env : ZMap.t term) (yg : term) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) env yg [] (b_root b) (b_seg b) 0 None.

(** The block b with the young index yg, after an allocation of
    words words through the proof q, of which used words were used
    before. *)
Definition b_alloc (yg : term) (words : Z) (q : term) (used : Z) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (b_env b) yg (b_proofs b) (b_root b) (b_seg b)
       (b_budget b - words) (Some (q, used + words)).

(** The block b with words words reserved. *)
Definition b_reserve (words : Z) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (b_env b) (b_yg b) (b_proofs b) (b_root b) (b_seg b) words None.

(** The block b knowing that the proof q covers hi bytes of the
    block v. *)
Definition b_prove (v q : term) (hi : Z) (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (b_env b) (b_yg b) ((v, (q, hi)) :: b_proofs b) (b_root b) (b_seg b) (b_budget b) (b_aproof b).

(** A new block l after b: in its cluster and body, with its
    variables, young index and reserved words, and no proofs. *)
Definition b_next (l : term) (phis : list term) (b : bc) : bc :=
  mkbc l phis [] (b_env b) (b_yg b) [] (b_root b) (b_seg b) (b_budget b) None.

(** The state with the block b finished by the jump j. *)
Definition finish (b : bc) (j : term) (s : st) : st :=
  mkst (s_next s) (mkpb (b_label b) (b_phis b) (rev (b_insts b)) j :: s_blocks s) (s_edges s).

(** The state with an edge into l from pred, with the values vs. *)
Definition add_edge (l pred : term) (vs : list term) (s : st) : st :=
  let old := match nm_find l (s_edges s) with Some es => es | None => [] end in
  mkst (s_next s) (s_blocks s) (nm_add l ((pred, vs) :: old) (s_edges s)).

(** The constructor of the tag t. *)
Definition ctor_of (c : cl) (t : Z) : res ctor :=
  match ZMap.find t (cl_ctors c) with
  | Some k => Ok k
  | None => Err ("an unknown constructor tag " ++ decimal t)%string
  end.

(** The IR value of the λANF variable x: its binding, its constant's
    value, or the immediate fid of the function x. *)
Definition val_of (c : cl) (b : bc) (x : Z) : res term :=
  match ZMap.find x (b_env b) with
  | Some v => Ok v
  | None =>
      match ZMap.find x (cl_kv c) with
      | Some (KW w) => Ok (cst w)
      | Some (KInt z) =>
          if small z then Ok (cst (2 * z + 1))
          else match ZMap.find x (cl_kw c) with
               | Some w => Ok (cst w)
               | None => Err ("a constant not in the pool: " ++ decimal x)%string
               end
      | Some _ =>
          match ZMap.find x (cl_kw c) with
          | Some w => Ok (cst w)
          | None => Err ("a constant not in the pool: " ++ decimal x)%string
          end
      | None =>
      match ZMap.find x (cl_fns c) with
      | Some fi =>
          match fi_fid fi with
          | Some k => Ok (cst (2 * k + 1))
          | None => Err ("a function used as a value without a fid: " ++ decimal x)%string
          end
      | None => Err ("an unbound variable " ++ decimal x)%string
      end
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
    is never one, nor a constant. *)
Definition live_vals (c : cl) (b : bc) (xs : list Z) : res (list term) :=
  let? vs := vals c b (filter (fun x => ZMap.mem x (b_env b)
                                        || negb (ZMap.mem x (cl_fns c) || ZMap.mem x (cl_kv c))) xs) in
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

(** The instructions that make the pointer to the block whose word is
    w, and the pointer's temporary: arena + 2 w, which is the arena's word
    w >> 1 when w is a block's (even) word. *)
Definition addr_of_word (w : term) (s : st) : list term * term * st :=
  let (k1, s) := fresh s in
  let (k2, s) := fresh s in
  let (k3, s) := fresh s in
  ([i_let (tname k1) "l" (TApp "ext" [TAtom "uw"]) [w];
    i_let (tname k2) "l" (TAtom "shl") [tmpv (tname k1); cst 1];
    i_flight (tname k3) t_arena (tmpv (tname k2))], tname k3, s).

(** The instructions that store the values vs in the function's frame
    of shadow roots (at fr, from roots[sp] on), and those that read
    them back into fresh temporaries after a call, which a collection
    may have moved them in; and those temporaries. *)
Definition frame_spill (vs : list term) (s : st) : list term * list term * list term * st :=
  match vs with
  | [] => ([], [], [], s)
  | _ =>
      let n := Z.of_nat (length vs) in
      let (qr, s) := fresh s in
      let (qr2, s) := fresh s in
      let (ks, s) := fresh_n (length vs) s in
      ([i_let (tname qr) "a" (o_check 0 (4 * n) "write") [t_fr]] ++ stores 0 vs (tname qr),
       [i_let (tname qr2) "a" (o_check 0 (4 * n) "read") [t_fr]] ++ loads 0 ks (tname qr2),
       map (fun k => tmpv (tname k)) ks, s)
  end.

(** The roots' top past the n values of the frame. *)
Definition sp_past (n : nat) (s : st) : list term * term * st :=
  match n with
  | O => ([], t_sp, s)
  | _ => let (k, s) := fresh s in
         ([i_let (tname k) "w" (TAtom "add") [t_sp; cst (Z.of_nat n)]], tmpv (tname k), s)
  end.

(** The instructions of a call of the runtime that a collection may run
    in (a collection, or a primitive that allocates): the young index yg
    and the roots' top stored to the state, the values vs to the frame,
    the call, then the young index and the values, perhaps moved, read
    back. Also the values' new temporaries and the new young index. *)
Definition around_gc (vs : list term) (call : term) (yg : term) (s : st)
  : list term * list term * term * st :=
  let (q0, s) := fresh s in
  let (q1, s) := fresh s in
  let (yg', s) := fresh s in
  let '(top, spn, s) := sp_past (length vs) s in
  let '(push, pop, vs', s) := frame_spill vs s in
  (top ++ [i_let (tname q0) "a" (o_check 0 24 "write") [t_st]; i_store 0 yg (tname q0); i_store 20 spn (tname q0)]
       ++ push ++ [call; i_let (tname q1) "a" (o_check 0 4 "read") [t_st];
                   i_let (tname yg') "w" (o_load 0) [tmpv (tname q1)]] ++ pop,
   vs', tmpv (tname yg'), s).

(** What a lowered function returns: two 64-bit words, its value and
    the young index, in `%rdx` and `%rcx`. *)
Definition t_ret2 : term := TApp "tuple" [TList [TAtom "l"; TAtom "l"]].

(** The jump that returns the words vs. *)
Definition j_rets (vs : list term) : term := TApp "rets" [TList vs].

(** A call of a lowered function: the callee g with the arguments args
    after the young index, the roots' top and the nursery's end, its
    value and the young index in two 64-bit temporaries. The
    instruction, and those temporaries. *)
Definition lcall (g : term) (yg spn : term) (args : list term) (s : st) : term * (Z * Z) * st :=
  let (rv, s) := fresh s in
  let (ry, s) := fresh s in
  (TApp "call" [TApp "tuple" [TList [TApp "result" [tmpv (tname rv); TAtom "l"];
                                     TApp "result" [tmpv (tname ry); TAtom "l"]]]; g;
                TList (a_p t_arena :: a_p t_st :: map a_w (yg :: spn :: t_ne :: args))], (rv, ry), s).

(** The return of the results rl of a tail call. *)
Definition j_rets_of (rl : Z * Z) : term := j_rets [tmpv (tname (fst rl)); tmpv (tname (snd rl))].

(** The instructions that take the results rl of a lowered function
    as its value, into r, and the young index; and that index. *)
Definition split_result (rl : Z * Z) (r : Z) (s : st) : list term * term * st :=
  let (yg', s) := fresh s in
  ([i_let (tname r) "w" (TAtom "copy") [tmpv (tname (fst rl))];
    i_let (tname yg') "w" (TAtom "copy") [tmpv (tname (snd rl))]], tmpv (tname yg'), s).

(** The instructions of a call of a lowered function g with args, its
    value into r, whose live values vs go to the frame and come back:
    nothing of the state is read or written. Also the values' new
    temporaries and the new young index. *)
Definition around_lcall (vs : list term) (r : Z) (g : term) (args : list term) (yg : term) (s : st)
  : list term * list term * term * st :=
  let '(top, spn, s) := sp_past (length vs) s in
  let '(push, pop, vs', s) := frame_spill vs s in
  let '(call, rl, s) := lcall g yg spn args s in
  let '(split, yg', s) := split_result rl r s in
  (top ++ push ++ call :: split ++ pop, vs', yg', s).

(** The instructions that widen the value v and the young index yg
    for a return, and the jump that returns them. *)
Definition pack_result (yg v : term) (s : st) : list term * term * st :=
  let (k1, s) := fresh s in
  let (k2, s) := fresh s in
  ([i_let (tname k1) "l" (TApp "ext" [TAtom "uw"]) [v];
    i_let (tname k2) "l" (TApp "ext" [TAtom "uw"]) [yg]],
   j_rets [tmpv (tname k1); tmpv (tname k2)], s).

(** The words the expression e allocates in the nursery before its
    first call, on its longest path: neither constants nor the
    represented constructors take any. *)
Fixpoint need (c : cl) (e : exp) : Z :=
  match e with
  | Econstr x t _ e' =>
      let a := match ZMap.find t (cl_ctors c) with Some k => c_arity k | None => 0 end in
      (if (a =? 0) || ZMap.mem x (cl_kv c) || ZMap.mem t (cl_roles c) then 0 else a + 1) + need c e'
  | Ecase _ arms =>
      (fix go (l : list (Z * exp)) : Z :=
         match l with [] => 0 | (_, e1) :: l' => Z.max (need c e1) (go l') end) arms
  | Eprim x p _ _ e' =>
      (if negb (ZMap.mem x (cl_kv c)) && pair_prim (cl_prims c) p then 3 else 0) + need c e'
  | Eproj _ _ _ _ e' | Eprim_val _ e' => need c e'
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
  | Eprim _ _ ys live _ => zunion (zset ys) live
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
    let '(is, vs', yg', s) := around_gc vs call (b_yg b) s in
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
      let '(is, p, s) := addr_of_word v s in
      let (kq, s) := fresh s in
      let (kh, s) := fresh s in
      let (ko, s) := fresh s in
      let b := b_emit (is ++
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

(** The table of the functions of n parameters that are values,
    `anf_fnsN`: their code, in the order of their fids, from the fid
    lo on (the fids of one arity are consecutive). *)
Definition table_name (n : nat) : string := ("anf_fns" ++ decimal (Z.of_nat n))%string.

(** The instructions that load the code of the function of n
    parameters whose fid is the value vf from its table, whose first
    fid is lo, and the pointer's temporary. A fid outside the table
    fails the check. *)
Definition code_ptr (n : nat) (lo : Z) (vf : term) (s : st) : list term * term * st :=
  let (k1, s) := fresh s in
  let (k2, s) := fresh s in
  let (k3, s) := fresh s in
  let (k4, s) := fresh s in
  let (k5, s) := fresh s in
  let (k6, s) := fresh s in
  let (k7, s) := fresh s in
  ([i_let (tname k1) "w" (TAtom "sub") [vf; cst (2 * lo + 1)];
    i_let (tname k2) "l" (TApp "ext" [TAtom "uw"]) [tmpv (tname k1)];
    i_let (tname k3) "l" (TAtom "shl") [tmpv (tname k2); cst 2];
    i_let (tname k4) "p" (TAtom "copy") [TApp "global" [TAtom (table_name n)]];
    i_flight (tname k5) (tmpv (tname k4)) (tmpv (tname k3));
    i_let (tname k6) "a" (TApp "check" [TInt 0; TInt 8; TAtom "read"; TInt 8]) [tmpv (tname k5)];
    i_let (tname k7) "p" (TApp "raw_load_pointer" [TInt 0; TList [TAtom "aux_read"; TAtom "lower_resolve"; TAtom "address_read"]])
          [tmpv (tname k6)]], tname k7, s).

(** The callee of a call of the function f with the values vs, its
    arguments after the arena and state, and the instructions that
    must come first: f itself, or the code of the closure whose fid
    f is, loaded from the table of its arity. *)
Definition callee (c : cl) (b : bc) (f : Z) (vs : list term) (s : st) : res (list term * term * list term * st) :=
  match ZMap.find f (cl_fns c) with
  | Some fi =>
      if negb (Nat.eqb (length (fi_xs fi)) (length vs)) then
        Err ("a call of " ++ decimal f ++ " with the wrong number of arguments")%string
      else if negb (fi_root fi =? f) then Err ("a call of the absorbed function " ++ decimal f)%string
      else Ok ([], TApp "global" [TAtom (fi_name fi)], vs, s)
  | None =>
      let? vf := val_of c b f in
      let n := length vs in
      let lo := match find (fun p => Nat.eqb (fst p) n) (cl_tbl c) with Some (_, lo) => lo | None => 0 end in
      let '(is, k, s) := code_ptr n lo vf s in
      Ok (is, tmpv k, vs, s)
  end.

(** The call instruction of the callee g (a global or a pointer) with
    the arguments vs into the temporary r. *)
Definition call_inst (r g : term) (vs : list term) : term :=
  TApp "call" [TApp "result" [tmpv r; TAtom "w"]; g;
               TList (a_p t_arena :: a_p t_st :: map a_w vs)].

(** ## Represented values and primitives

    An operation on a represented value ([roles]) or a primitive
    (`anf_prim`, which `CertiRocq Register` names, anf/lower/Prims.v)
    is lowered in one of three ways:

    - inline, when it needs no call: `Npos p`, an `ascii` and its
      bits, a string's first character;
    - with a fast path and a slow one ([fast_slow]): instructions
      compute the value and whether it is right (both operands
      immediates, no overflow), and when it is not, a call of the
      runtime (anf_prims.c) computes it. Such a call never collects:
      an integer it makes that is not an immediate goes to the major
      heap, a leaf that no collection scans. The live values stay
      where they are and the stretch's reserved words stay reserved;
    - as a call that may collect ([collecting]), as [Eletapp] is: the
      functions that make strings and lists. *)

Definition tv (k : Z) : term := tmpv (tname k).

(** The instruction that makes k the `w` value o of args. *)
Definition i_w (k : Z) (o : string) (args : list term) : term := i_let (tname k) "w" (TAtom o) args.

(** The instruction that makes k 1 if a and b compare by cnd, else 0. *)
Definition i_c (k : Z) (cnd : string) (a b : term) : term := i_let (tname k) "w" (o_cmp cnd) [a; b].

(** A call of the runtime's function f on the arena, the state and the
    words args, into k. *)
Definition i_rt (k : Z) (f : string) (args : list term) : term :=
  TApp "call" [TApp "result" [tv k; TAtom "w"]; TApp "global" [TAtom f];
               TList (a_p t_arena :: a_p t_st :: map a_w args)].

(** The block b after a call that does not collect: what checks
    proved is gone, the reserved words stay. *)
Definition b_drop (b : bc) : bc :=
  mkbc (b_label b) (b_phis b) (b_insts b) (b_env b) (b_yg b) [] (b_root b) (b_seg b) (b_budget b) None.

(** The block b with the instructions is and then a branch on ok: when
    it is nonzero, the value is v; else the runtime's f on args
    computes it. Gives the block where the two meet, with the same
    variables, young index and reserved words and no proofs, and the
    value there. *)
Definition fast_slow (is : list term) (ok v : term) (f : string) (args : list term)
  (b : bc) (s : st) : bc * term * st :=
  let (ls, s) := fresh s in
  let (lj, s) := fresh s in
  let (kr, s) := fresh s in
  let (kc, s) := fresh s in
  let b1 := b_emit is b in
  let s := finish b1 (j_branch ok (lname lj) (lname ls)) s in
  let s := add_edge (lname lj) (b_label b1) [v] s in
  let s := finish (b_emit [i_rt kc f args] (b_next (lname ls) [] b)) (j_goto (lname lj)) s in
  let s := add_edge (lname lj) (lname ls) [tv kc] s in
  (b_next (lname lj) [tname kr] b, tv kr, s).

(** `String.eqb a b`, 0 or 1, told from the words when it can be: the
    same word; an empty string, an immediate, and another; two blocks
    of bytes whose headers or lengths differ, or whose bytes, four at
    most, fit their one word (zero past the last byte, as every block
    of bytes is made). Else anf_p_str_eqb, which also reads slices,
    tells it. Gives the block where they meet and the value there. *)
Definition str_eqb_inline (a w : term) (b : bc) (s : st) : bc * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (k3, s) := fresh s in let (k4, s) := fresh s in
  let (l2, s) := fresh s in let (ls, s) := fresh s in let (lj, s) := fresh s in let (kr, s) := fresh s in
  let b1 := b_emit [i_c k1 "eq" a w; i_w k2 "or" [a; w]; i_w k3 "and" [tv k2; cst 1];
                    i_w k4 "or" [tv k1; tv k3]] b in
  let s := finish b1 (j_branch (tv k4) (lname lj) (lname l2)) s in
  let s := add_edge (lname lj) (b_label b1) [tv k1] s in
  let '(isa, pa, s) := addr_of_word a s in
  let '(isb, pb, s) := addr_of_word w s in
  let (qa, s) := fresh s in let (ha, s) := fresh s in let (na, s) := fresh s in let (wa, s) := fresh s in
  let (qb, s) := fresh s in let (hb, s) := fresh s in let (nb, s) := fresh s in let (wb, s) := fresh s in
  let (sa, s) := fresh s in let (ea, s) := fresh s in let (sb, s) := fresh s in let (eb, s) := fresh s in
  let (both, s) := fresh s in let (dh, s) := fresh s in let (dn, s) := fresh s in let (df, s) := fresh s in
  let (sh, s) := fresh s in let (dec, s) := fresh s in let (ok, s) := fresh s in
  let (ew, s) := fresh s in let (nd, s) := fresh s in let (v2, s) := fresh s in
  let is2 :=
    isa ++ [i_let (tname qa) "a" (o_check 0 12 "read") [tmpv pa];
            i_let (tname ha) "w" (o_load 0) [tv qa]; i_let (tname na) "w" (o_load 4) [tv qa];
            i_let (tname wa) "w" (o_load 8) [tv qa]]
    ++ isb ++ [i_let (tname qb) "a" (o_check 0 12 "read") [tmpv pb];
               i_let (tname hb) "w" (o_load 0) [tv qb]; i_let (tname nb) "w" (o_load 4) [tv qb];
               i_let (tname wb) "w" (o_load 8) [tv qb]]
    ++ [i_w sa "and" [tv ha; cst 768]; i_c ea "eq" (tv sa) (cst 256);
        i_w sb "and" [tv hb; cst 768]; i_c eb "eq" (tv sb) (cst 256); i_w both "and" [tv ea; tv eb];
        i_c dh "ne" (tv ha) (tv hb); i_c dn "ne" (tv na) (tv nb); i_w df "or" [tv dh; tv dn];
        i_c sh "ule" (tv na) (cst 4); i_w dec "or" [tv df; tv sh]; i_w ok "and" [tv both; tv dec];
        i_c ew "eq" (tv wa) (tv wb); i_w nd "xor" [tv df; cst 1]; i_w v2 "and" [tv nd; tv ew]] in
  let s := finish (b_emit is2 (b_next (lname l2) [] b)) (j_branch (tv ok) (lname lj) (lname ls)) s in
  let s := add_edge (lname lj) (lname l2) [tv v2] s in
  let (kc, s) := fresh s in
  let s := finish (b_emit [i_rt kc "anf_p_str_eqb" [a; w]] (b_next (lname ls) [] b)) (j_goto (lname lj)) s in
  let s := add_edge (lname lj) (lname ls) [tv kc] s in
  (b_next (lname lj) [tname kr] b, tv kr, s).

(** The instructions that make k the immediate w0 when c is 0 and w1
    when it is 1. *)
Definition select01 (k : Z) (c : term) (w0 w1 : Z) (s : st) : list term * st :=
  let (k1, s) := fresh s in
  ([i_w k1 "mul" [c; cst (w1 - w0)]; i_w k "add" [tv k1; cst w0]], s).

(** The block b with x bound to the bool that the 0 or 1 of cv says. *)
Definition bind_bool (c : cl) (x : Z) (cv : term) (b : bc) (s : st) : bc * st :=
  let (k, s) := fresh s in
  let (is, s) := select01 k cv (cl_false c) (cl_true c) s in
  (b_bind x (tv k) (b_emit is b), s).

(** The block b with x bound to the comparison that r, -1, 0 or 1,
    says. *)
Definition bind_comparison (c : cl) (x : Z) (r : term) (b : bc) (s : st) : bc * st :=
  let (kl, s) := fresh s in
  let (kg, s) := fresh s in
  let (k1, s) := fresh s in
  let (k2, s) := fresh s in
  let (k3, s) := fresh s in
  let (k, s) := fresh s in
  let (is1, s) := select01 k1 (tv kl) 0 (cl_lt c - cl_eq c) s in
  let (is2, s) := select01 k2 (tv kg) 0 (cl_gt c - cl_eq c) s in
  (b_bind x (tv k)
     (b_emit ([i_c kl "slt" r (cst 0); i_c kg "sgt" r (cst 0)] ++ is1 ++ is2
              ++ [i_w k3 "add" [tv k1; tv k2]; i_w k "add" [tv k3; cst (cl_eq c)]]) b), s).

(** The comparison of the integers a and b: -1, 0 or 1. Immediates
    compare as their words do. *)
Definition int_cmp (a b : term) (bc0 : bc) (s : st) : bc * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (kg, s) := fresh s in
  let (kl, s) := fresh s in let (kr, s) := fresh s in
  fast_slow [i_w k1 "and" [a; b]; i_w k2 "and" [tv k1; cst 1];
             i_c kg "sgt" a b; i_c kl "slt" a b; i_w kr "sub" [tv kg; tv kl]]
            (tv k2) (tv kr) "anf_p_cmp" [a; b] bc0 s.

(** Whether the integers a and b differ: 0 when they are equal. An
    integer that fits an immediate is always one, so when either is an
    immediate they are equal exactly when their words are. *)
Definition int_ne (a b : term) (bc0 : bc) (s : st) : bc * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (kn, s) := fresh s in
  fast_slow [i_w k1 "or" [a; b]; i_w k2 "and" [tv k1; cst 1]; i_c kn "ne" a b]
            (tv k2) (tv kn) "anf_p_cmp" [a; b] bc0 s.

(** A one-operand integer operation: the instructions mk gives for a
    compute the value and whether it is right; else the runtime's f. *)
Definition int_op1 (mk : term -> st -> list term * term * term * st) (f : string) (a : term)
  (b : bc) (s : st) : bc * term * st :=
  let '(is, ok, v, s) := mk a s in fast_slow is ok v f [a] b s.

(** The successor: a an immediate other than the largest. *)
Definition mk_succ (a : term) (s : st) : list term * term * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (k3, s) := fresh s in let (kv, s) := fresh s in
  ([i_w k1 "and" [a; cst 1]; i_c k2 "ne" a (cst 2147483647); i_w k3 "and" [tv k1; tv k2];
    i_w kv "add" [a; cst 2]], tv k3, tv kv, s).

(** The predecessor: a an immediate other than the least. *)
Definition mk_pred (a : term) (s : st) : list term * term * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (k3, s) := fresh s in let (kv, s) := fresh s in
  ([i_w k1 "and" [a; cst 1]; i_c k2 "ne" a (cst (-2147483647)); i_w k3 "and" [tv k1; tv k2];
    i_w kv "sub" [a; cst 2]], tv k3, tv kv, s).

(** The predecessor of a natural number, 0 for 0. *)
Definition mk_pred0 (a : term) (s : st) : list term * term * term * st :=
  let (k1, s) := fresh s in let (kd, s) := fresh s in let (kz, s) := fresh s in
  let (kz2, s) := fresh s in let (kv, s) := fresh s in
  ([i_w k1 "and" [a; cst 1]; i_w kd "sub" [a; cst 2]; i_c kz "eq" a (cst 1);
    i_w kz2 "shl" [tv kz; cst 1]; i_w kv "add" [tv kd; tv kz2]], tv k1, tv kv, s).

(** The opposite: a an immediate other than the least, as
    2(-v) + 1 = 2 - (2v + 1). *)
Definition mk_neg (a : term) (s : st) : list term * term * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (k3, s) := fresh s in let (kv, s) := fresh s in
  ([i_w k1 "and" [a; cst 1]; i_c k2 "ne" a (cst (-2147483647)); i_w k3 "and" [tv k1; tv k2];
    i_w kv "sub" [cst 2; a]], tv k3, tv kv, s).

(** Half a positive, rounded down, what `xI p` or `xO p` holds: for
    a = 2v + 1, 2(v >> 1) + 1 = v | 1. *)
Definition mk_half (a : term) (s : st) : list term * term * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (kv, s) := fresh s in
  ([i_w k1 "and" [a; cst 1]; i_w k2 "shr" [a; cst 1]; i_w kv "or" [tv k2; cst 1]], tv k1, tv kv, s).

(** Twice a positive v, plus one (`xI`, the word 2a + 1) or not (`xO`,
    2a - 1): v below 2^29. *)
Definition mk_double (one : bool) (a : term) (s : st) : list term * term * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (k3, s) := fresh s in
  let (kd, s) := fresh s in let (kv, s) := fresh s in
  ([i_w k1 "and" [a; cst 1]; i_c k2 "slt" a (cst 1073741824); i_w k3 "and" [tv k1; tv k2];
    i_w kd "shl" [a; cst 1]; i_w kv (if one then "add" else "sub") [tv kd; cst 1]], tv k3, tv kv, s).

(** The integer, or 0 when it is negative (`Z.to_nat`). *)
Definition mk_max0 (a : term) (s : st) : list term * term * term * st :=
  let (k1, s) := fresh s in let (kc, s) := fresh s in let (km, s) := fresh s in
  let (ka, s) := fresh s in let (kv, s) := fresh s in
  ([i_w k1 "and" [a; cst 1]; i_c kc "slt" a (cst 1); i_w km "sub" [tv kc; cst 1];
    i_w ka "and" [a; tv km]; i_w kv "or" [tv ka; tv kc]], tv k1, tv kv, s).

(** The character of a natural number's low byte (`ascii_of_nat`). *)
Definition mk_lowbyte (a : term) (s : st) : list term * term * term * st :=
  let (k1, s) := fresh s in let (kv, s) := fresh s in
  ([i_w k1 "and" [a; cst 1]; i_w kv "and" [a; cst 511]], tv k1, tv kv, s).

(** The sum (add) or difference of the integers a and b: a + (b - 1)
    or a - (b - 1) when both are immediates and it does not overflow
    32 bits, which is when the result is an immediate. *)
Definition int_addsub (add : bool) (a b : term) (bc0 : bc) (s : st) : bc * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (kb, s) := fresh s in
  let (kr, s) := fresh s in let (x1, s) := fresh s in let (x2, s) := fresh s in
  let (x3, s) := fresh s in let (ko, s) := fresh s in let (kn, s) := fresh s in let (ok, s) := fresh s in
  fast_slow
    [i_w k1 "and" [a; b]; i_w k2 "and" [tv k1; cst 1]; i_w kb "sub" [b; cst 1];
     i_w kr (if add then "add" else "sub") [a; tv kb];
     i_w x1 "xor" [a; tv kr];
     (if add then i_w x2 "xor" [tv kb; tv kr] else i_w x2 "xor" [a; tv kb]);
     i_w x3 "and" [tv x1; tv x2]; i_c ko "slt" (tv x3) (cst 0); i_w kn "xor" [tv ko; cst 1];
     i_w ok "and" [tv k2; tv kn]]
    (tv ok) (tv kr) (if add then "anf_p_add" else "anf_p_sub") [a; b] bc0 s.

(** The larger (max) or smaller of the integers a and b. *)
Definition int_minmax (max : bool) (a b : term) (bc0 : bc) (s : st) : bc * term * st :=
  let (k1, s) := fresh s in let (k2, s) := fresh s in let (kc, s) := fresh s in
  let (km, s) := fresh s in let (kd, s) := fresh s in let (ka, s) := fresh s in let (kv, s) := fresh s in
  fast_slow
    [i_w k1 "and" [a; b]; i_w k2 "and" [tv k1; cst 1]; i_c kc (if max then "sgt" else "slt") a b;
     i_w km "neg" [tv kc]; i_w kd "sub" [a; b]; i_w ka "and" [tv kd; tv km]; i_w kv "add" [b; tv ka]]
    (tv k2) (tv kv) (if max then "anf_p_max" else "anf_p_min") [a; b] bc0 s.

(** The values at the indices is of vs. *)
Definition pick (vs : list term) (is : list nat) : list term := map (fun i => nth i vs (cst 1)) is.

(** The block b with the inline primitive t on the values vs bound to
    x; [None] for a target lowered otherwise. *)
Definition prim_inline (c : cl) (t : string) (x : Z) (vs : list term) (b : bc) (s : st) : option (bc * st) :=
  let bindv r := let '(b, v, s) := r in (b_bind x v b, s) in
  let tf (cnd : string) (r : bc * term * st) :=
    let '(b, v, s) := r in
    let (k, s) := fresh s in bind_bool c x (tv k) (b_emit [i_c k cnd v (cst 0)] b) s in
  match vs with
  | [a] =>
      if String.eqb t "nf_succ" then Some (bindv (int_op1 mk_succ "anf_p_succ" a b s))
      else if String.eqb t "nf_pred" then Some (bindv (int_op1 mk_pred "anf_p_pred" a b s))
      else if String.eqb t "nf_pred0" then Some (bindv (int_op1 mk_pred0 "anf_p_pred0" a b s))
      else if String.eqb t "nf_neg" then Some (bindv (int_op1 mk_neg "anf_p_neg" a b s))
      else if String.eqb t "nf_max0" then Some (bindv (int_op1 mk_max0 "anf_p_max0" a b s))
      else if String.eqb t "nf_ascii_of_nat" then Some (bindv (int_op1 mk_lowbyte "anf_p_lowbyte" a b s))
      else if String.eqb t "nf_id" then Some (b_bind x a b, s)
      else None
  | [a; a2] =>
      if String.eqb t "nf_add" then Some (bindv (int_addsub true a a2 b s))
      else if String.eqb t "nf_sub" then Some (bindv (int_addsub false a a2 b s))
      else if String.eqb t "nf_max" then Some (bindv (int_minmax true a a2 b s))
      else if String.eqb t "nf_min" then Some (bindv (int_minmax false a a2 b s))
      else if String.eqb t "nf_eqb" then Some (tf "eq"%string (int_ne a a2 b s))
      else if String.eqb t "nf_ltb" then Some (tf "slt"%string (int_cmp a a2 b s))
      else if String.eqb t "nf_leb" then Some (tf "sle"%string (int_cmp a a2 b s))
      else if String.eqb t "nf_compare" then
        let '(b, r, s) := int_cmp a a2 b s in Some (bind_comparison c x r b s)
      else if String.eqb t "nf_ascii_eqb" then
        let (k, s) := fresh s in Some (bind_bool c x (tv k) (b_emit [i_c k "eq" a a2] b) s)
      else if String.eqb t "nf_ascii_compare" then
        let (kg, s) := fresh s in let (kl, s) := fresh s in let (kr, s) := fresh s in
        Some (bind_comparison c x (tv kr) (b_emit [i_c kg "sgt" a a2; i_c kl "slt" a a2;
                                                   i_w kr "sub" [tv kg; tv kl]] b) s)
      else None
  | _ => None
  end.

(** The roles of the constructors of the inductive whose constructor
    has the role r. *)
Definition kin_roles (r : Z) : list Z :=
  if (r =? r_O) || (r =? r_S) then [r_O; r_S]
  else if (r =? r_N0) || (r =? r_Npos) then [r_N0; r_Npos]
  else if (r =? r_empty) || (r =? r_string) then [r_empty; r_string]
  else if (r =? r_xI) || (r =? r_xO) || (r =? r_xH) then [r_xI; r_xO; r_xH]
  else if (r =? r_Z0) || (r =? r_Zpos) || (r =? r_Zneg) then [r_Z0; r_Zpos; r_Zneg]
  else [r_ascii].

(** The dispatch of a case on the represented value v, whose arms
    (tag, label) are of an inductive with the role r0: a test of v
    against zero (or, for `positive`, one), then for `positive` its
    lowest bit and for `Z` its sign. *)
Definition role_dispatch (c : cl) (r0 : Z) (v : term) (arms : list (Z * term)) (b : bc) (s : st) : st :=
  let has r := existsb (fun a => role_of (cl_roles c) (fst a) =? r) arms in
  let '(lu, s) :=
    if forallb has (kin_roles r0) then (TAtom "unreachable", s)
    else let (ku, s) := fresh s in (lname ku, finish (b_next (lname ku) [] b) (TAtom "unreachable") s) in
  let arm r := match find (fun a => role_of (cl_roles c) (fst a) =? r) arms with
               | Some (_, l) => l | None => lu end in
  let two w r_eq r_ne (s : st) :=
    let (k, s) := fresh s in
    finish (b_emit [i_c k "eq" v (cst w)] b) (j_branch (tv k) (arm r_eq) (arm r_ne)) s in
  let then_test w r_eq (s : st) :=
    let (k, s) := fresh s in
    let (ln, s) := fresh s in
    (b_next (lname ln) [] b, finish (b_emit [i_c k "eq" v (cst w)] b) (j_branch (tv k) (arm r_eq) (lname ln)) s) in
  if (r0 =? r_O) || (r0 =? r_S) then two 1 r_O r_S s
  else if (r0 =? r_N0) || (r0 =? r_Npos) then two 1 r_N0 r_Npos s
  else if (r0 =? r_empty) || (r0 =? r_string) then two 1 r_empty r_string s
  else if r0 =? r_ascii then finish b (j_goto (arm r_ascii)) s
  else if (r0 =? r_xI) || (r0 =? r_xO) || (r0 =? r_xH) then
    let (b2, s) := then_test 3 r_xH s in
    let (k1, s) := fresh s in let (k2, s) := fresh s in let (k3, s) := fresh s in
    let '(b3, odd, s) := fast_slow [i_w k1 "and" [v; cst 1]; i_w k2 "and" [v; cst 2]; i_w k3 "shr" [tv k2; cst 1]]
                                   (tv k1) (tv k3) "anf_p_odd" [v] b2 s in
    finish b3 (j_branch odd (arm r_xI) (arm r_xO)) s
  else
    let (b2, s) := then_test 1 r_Z0 s in
    let (k1, s) := fresh s in let (k2, s) := fresh s in
    let '(b3, pos, s) := fast_slow [i_w k1 "and" [v; cst 1]; i_c k2 "sgt" v (cst 1)]
                                   (tv k1) (tv k2) "anf_p_zpos" [v] b2 s in
    finish b3 (j_branch pos (arm r_Zpos) (arm r_Zneg)) s.

(** The instructions that make k the `ascii` of the eight bools vs,
    lowest bit first: the immediate of its code. *)
Definition ascii_insts (c : cl) (k : Z) (vs : list term) (s : st) : list term * st :=
  let '(is, acc, _, s) :=
    fold_left (fun r v =>
                 let '(is, acc, i, s) := r in
                 let (kb, s) := fresh s in let (ks, s) := fresh s in let (ko, s) := fresh s in
                 (is ++ [i_c kb "eq" v (cst (cl_true c)); i_w ks "shl" [tv kb; cst i]; i_w ko "or" [acc; tv ks]],
                  tv ko, i + 1, s)) vs ([], cst 0, 1, s) in
  (is ++ [i_w k "or" [acc; cst 1]], s).

(** The block b with the block whose header is hdr and whose fields
    are the values vs stored in the nursery's reserved words, bound to
    x. *)
Definition store_block (x hdr : Z) (vs : list term) (b : bc) (s : st) : bc * st :=
  (* One check covers every word the stretch has reserved and not
     used, from the young index on; the blocks after this one in the
     block store through it too. *)
  let '(is, q, used, s) :=
    match b_aproof b with
    | Some (q, used) => ([], q, used, s)
    | None =>
        let '(is, p, s) := addr_of_idx (b_yg b) s in
        let (kq, s) := fresh s in
        (is ++ [i_let (tname kq) "a" (o_check 0 (4 * b_budget b) "write") [tmpv p]], tname kq, 0, s)
    end in
  let ar := Z.of_nat (length vs) in
  let (kx, s) := fresh s in
  let (ky, s) := fresh s in
  let is := is ++ [i_store (4 * used) (cst hdr) q] ++ stores (4 * used + 4) vs q
               ++ [i_let (tname kx) "w" (TAtom "shl") [b_yg b; cst 1];
                   i_let (tname ky) "w" (TAtom "add") [b_yg b; cst (ar + 1)]] in
  (b_alloc (tmpv (tname ky)) (ar + 1) q used (b_bind x (tmpv (tname kx)) (b_emit is b)), s).

(** A call of the runtime's f on args that may collect, as [Eletapp]
    is: the live variables go to the shadow roots and come back, the
    result is bound to x, and the stretch e that follows starts. *)
Definition collecting (c : cl) (x : Z) (f : string) (args : list term) (live : list Z) (e : exp)
  (b : bc) (s : st) : res (bc * st) :=
  let? lvs := live_vals c b live in
  let (r, s) := fresh s in
  let '(is, lvs', yg', s) := around_gc lvs (call_inst (tname r) (TApp "global" [TAtom f]) args) (b_yg b) s in
  let env := ZMap.add x (tmpv (tname r)) (rebind live lvs lvs' (b_env b)) in
  let b := b_after env yg' (b_emit is b) in
  seg_head c (Z.min (need c e) seg_cap) (x :: live) b s.

(** The block b with x bound to the value of the represented
    constructor of role r on the values vs; live are the variables
    live after it and e what follows, for the one that may collect
    (`String`, which copies the string). *)
Definition represent (c : cl) (x r : Z) (vs : list term) (live : list Z) (e : exp) (b : bc) (s : st)
  : res (bc * st) :=
  let bindv res := let '(b, v, s) := res in Ok (b_bind x v b, s) in
  match vs with
  | [] =>
      if r =? r_xH then Ok (b_bind x (cst 3) b, s) else Ok (b_bind x (cst 1) b, s)
  | [a] =>
      if (r =? r_Npos) || (r =? r_Zpos) then Ok (b_bind x a b, s)
      else if r =? r_S then bindv (int_op1 mk_succ "anf_p_succ" a b s)
      else if r =? r_Zneg then bindv (int_op1 mk_neg "anf_p_neg" a b s)
      else if r =? r_xI then bindv (int_op1 (mk_double true) "anf_p_xI" a b s)
      else if r =? r_xO then bindv (int_op1 (mk_double false) "anf_p_xO" a b s)
      else Err "a represented constructor with one field"
  | [a; a2] =>
      if r =? r_string then collecting c x "anf_p_str_cons" [a; a2] live e b s
      else Err "a represented constructor with two fields"
  | _ =>
      if r =? r_ascii then
        let (k, s) := fresh s in
        let (is, s) := ascii_insts c k vs s in
        Ok (b_bind x (tv k) (b_emit is b), s)
      else Err "a represented constructor with the wrong number of fields"
  end.

(** The block b with x bound to the field n of the represented value a
    of role r: what [represent] put there. *)
Definition project (c : cl) (x r n : Z) (a : term) (live : list Z) (e : exp) (b : bc) (s : st)
  : res (bc * st) :=
  let bindv res := let '(b, v, s) := res in Ok (b_bind x v b, s) in
  if (r =? r_Npos) || (r =? r_Zpos) then Ok (b_bind x a b, s)
  else if r =? r_S then bindv (int_op1 mk_pred "anf_p_pred" a b s)
  else if r =? r_Zneg then bindv (int_op1 mk_neg "anf_p_neg" a b s)
  else if (r =? r_xI) || (r =? r_xO) then bindv (int_op1 mk_half "anf_p_half" a b s)
  else if r =? r_ascii then
    let (k1, s) := fresh s in
    let (k2, s) := fresh s in
    Ok (bind_bool c x (tv k2) (b_emit [i_w k1 "shr" [a; cst (n + 1)]; i_w k2 "and" [tv k1; cst 1]] b) s)
  else if r =? r_string then
    if n =? 0 then
      let (k, s) := fresh s in Ok (b_bind x (tv k) (b_drop (b_emit [i_rt k "anf_p_str_head" [a]] b)), s)
    else collecting c x "anf_p_str_tail" [a] live e b s
  else Err "a projection of a represented constructor without fields".

(** The dispatch of a case on v to its arms (tag, label). *)
Definition dispatch (c : cl) (v : term) (arms : list (Z * term)) (b : bc) (s : st) : res st :=
  match arms with
  | [] => Ok (finish b (TAtom "unreachable") s)
  | (t, _) :: _ =>
      match ZMap.find t (cl_roles c) with
      | Some r => Ok (role_dispatch c r v arms b s)
      | None =>
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
      end
  end.

(** The code of the expression e, in the block b. *)
Fixpoint gen (c : cl) (e : exp) (b : bc) (s : st) {struct e} : res st :=
  match e with
  | Econstr x t ys e' =>
      if ZMap.mem x (cl_kv c) then gen c e' b s
      else
      let? k := ctor_of c t in
      let ar := c_arity k in
      let r := role_of (cl_roles c) t in
      if negb (r =? r_plain) then
        let? vs := vals c b ys in
        let? (b, s) := represent c x r vs (zremove x (fv_exp e')) e' b s in
        gen c e' b s
      else if ar =? 0 then gen c e' (b_bind x (cst (2 * c_ord k + 1)) b) s
      else
        let? (b, s) := if ar + 1 <=? b_budget b then Ok (b, s)
                        else seg_head c (Z.max (ar + 1) (Z.min (need c e) seg_cap)) (fv_exp e) b s in
        let? vs := vals c b ys in
        if negb (Z.of_nat (length vs) =? ar) then Err "a constructor with the wrong number of fields"
        else if 256 <=? c_ord k then Err "a boxed ordinal above 255"
        else
          let (b, s) := store_block x (ar * 1024 + c_ord k) vs b s in
          gen c e' b s
  | Eproj x t n y e' =>
      let r := role_of (cl_roles c) t in
      if negb (r =? r_plain) then
        let? a := val_of c b y in
        let? (b, s) := project c x r n a (zremove x (fv_exp e')) e' b s in
        gen c e' b s
      else
      let? vy := val_of c b y in
      let (kx, s) := fresh s in
      let load q := i_let (tname kx) "w" (o_load (4 * (n + 1))) [tmpv q] in
      match proof_for vy (4 * (n + 2)) (b_proofs b) with
      | Some q => gen c e' (b_bind x (tmpv (tname kx)) (b_emit [load q] b)) s
      | None =>
          let hi := 4 * (Z.max n (proj_max y e') + 2) in
          let '(is, p, s) := addr_of_word vy s in
          let (kq, s) := fresh s in
          let is := is ++
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
      let? (pre, g, args, s) := callee c b f vs s in
      let? lvs := live_vals c b live in
      let (r, s) := fresh s in
      let '(is, lvs', yg', s) := around_lcall lvs r g args (b_yg b) s in
      let is := pre ++ is in
      let env := ZMap.add x (tmpv (tname r)) (rebind live lvs lvs' (b_env b)) in
      let b := b_after env yg' (b_emit is b) in
      let? (b, s) := seg_head c (Z.min (need c e') seg_cap) (x :: live) b s in
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
            let? (pre, g, args, s) := callee c b f vs s in
            let '(call, rl, s) := lcall g (b_yg b) t_sp args s in
            Ok (finish (b_emit (pre ++ [call]) b) (j_rets_of rl) s)
      | None =>
          let? (pre, g, args, s) := callee c b f vs s in
          let '(call, rl, s) := lcall g (b_yg b) t_sp args s in
          Ok (finish (b_emit (pre ++ [call]) b) (j_rets_of rl) s)
      end
  | Ehalt x =>
      let? v := val_of c b x in
      let '(is, j, s) := pack_result (b_yg b) v s in
      Ok (finish (b_emit is b) j s)
  | Efun _ _ => Err "a nested Efun"
  | Eprim x p ys live e' =>
      if ZMap.mem x (cl_kv c) then gen c e' b s
      else
      let? vs := vals c b ys in
      let? t := match ZMap.find p (cl_prims c) with
                | Some t => Ok t
                | None => Err ("an unknown primitive " ++ decimal p)%string
                end in
      match prim_kind t with
      | None => Err ("a primitive the runtime does not know: " ++ t)%string
      | Some (PInl _) =>
          match prim_inline c t x vs b s with
          | Some (b, s) => gen c e' b s
          | None => Err ("a primitive with the wrong number of arguments: " ++ t)%string
          end
      | Some (PRt f is) =>
          let (k, s) := fresh s in gen c e' (b_bind x (tv k) (b_drop (b_emit [i_rt k f (pick vs is)] b))) s
      | Some (PRtBool f is) =>
          match String.eqb f "anf_p_str_eqb", pick vs is with
          | true, [a; w] =>
              let '(b, v, s) := str_eqb_inline a w b s in
              let (b, s) := bind_bool c x v b s in gen c e' b s
          | _, _ =>
              let (k, s) := fresh s in
              let (b, s) := bind_bool c x (tv k) (b_drop (b_emit [i_rt k f (pick vs is)] b)) s in gen c e' b s
          end
      | Some (PRtCmp f is) =>
          let (k, s) := fresh s in
          let (b, s) := bind_comparison c x (tv k) (b_drop (b_emit [i_rt k f (pick vs is)] b)) s in gen c e' b s
      | Some (PPair f g is) =>
          (* Two calls that do not collect, then the pair in the
             nursery: its words are reserved first. *)
          let? (b, s) := if 3 <=? b_budget b then Ok (b, s)
                          else seg_head c (Z.max 3 (Z.min (need c e) seg_cap)) (fv_exp e) b s in
          let? vs := vals c b ys in
          let (k1, s) := fresh s in
          let (k2, s) := fresh s in
          let b := b_drop (b_emit [i_rt k1 f (pick vs is); i_rt k2 g (pick vs is)] b) in
          let (b, s) := store_block x (cl_pair c) [tv k1; tv k2] b s in
          gen c e' b s
      | Some (PAlloc f is lists) =>
          let args := pick vs is ++ (if lists then [cst (cl_nil c); cst (cl_cons c)] else []) in
          let? (b, s) := collecting c x f args live e' b s in
          gen c e' b s
      end
  | Eprim_val _ _ => Err "a primitive value (integers, floats, strings of the kernel)"
  end.

(** The code of one body of a cluster: the function f, the body seg of
    the cluster of root, with the parameters xs. Its head block's phis
    take the young index and the parameters. *)
Definition gen_body (c : cl) (root seg f : Z) (xs : list Z) (body : exp) (s : st) : res st :=
  let (ks, s) := fresh_n (S (length xs)) s in
  let env := fold_left (fun env p => ZMap.add (fst p) (tmpv (tname (snd p))) env)
                       (combine xs (tl ks)) (ZMap.empty term) in
  let b := mkbc (head_label f) (map tname ks) [] env (tmpv (tname (hd 0 ks))) [] root seg 0 None in
  let? (b, s) := seg_head c (Z.min (need c body) seg_cap) xs b s in
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
Definition func_term (name linkage : string) (rk : term) (ps : list term) (s : st) : term :=
  TApp "func" [TAtom name; TAtom linkage; rk;
               TList (TApp "param" [TAtom "p"; t_arena] :: TApp "param" [TAtom "p"; t_st]
                      :: map (fun p => TApp "param" [TAtom "w"; tmpv p]) ps);
               TList (map (block_term s) (rev (s_blocks s)))].

(** Whether the term x occurs in t. *)
Fixpoint mentions (x t : term) : bool :=
  term_eqb x t ||
  match t with
  | TApp _ ts | TList ts => (fix go (l : list term) : bool :=
                               match l with [] => false | u :: l' => mentions x u || go l' end) ts
  | _ => false
  end.

(** The IR function of the cluster of root, named name, whose
    parameters are xs and body body, with the absorbed functions
    members, in order. *)
Definition gen_cluster (c : cl) (name linkage : string) (root : Z) (xs : list Z) (body : exp)
  (members : list fdef) : res term :=
  let s := mkst 1 [] nm_empty in
  let (ps, s) := fresh_n (length xs) s in
  let (k0, s) := fresh s in
  let (k1, s) := fresh s in
  let (k2, s) := fresh s in
  let (k3, s) := fresh s in
  let s := add_edge (head_label root) (TAtom "entry")
             (tmpv (tname k0) :: map (fun k => tmpv (tname k)) ps) s in
  let? s := gen_body c root 0 root xs body s in
  let? (s, _) :=
    fold_left (fun acc fd =>
                 let? (s, seg) := acc in
                 let? s := gen_body c root seg (fd_f fd) (fd_xs fd) (fd_body fd) s in
                 Ok (s, seg + 1)) members (Ok (s, 1)) in
  (* The frame of shadow roots starts at roots[sp], at st + 64 + 4 sp,
     computed at the entry when a block spills to it. *)
  let uses_fr := existsb (fun pb => existsb (mentions t_fr) (pb_insts pb)) (s_blocks s) in
  let entry := mkpb (TAtom "entry") []
                 (if uses_fr
                  then [i_let (tname k1) "l" (TApp "ext" [TAtom "uw"]) [t_sp];
                        i_let (tname k2) "l" (TAtom "shl") [tmpv (tname k1); cst 2];
                        i_let (tname k3) "l" (TAtom "add") [tmpv (tname k2); cst 64];
                        i_flight (TAtom "fr") t_st (tmpv (tname k3))]
                  else [])
                 (j_goto (head_label root)) in
  let s := mkst (s_next s) (s_blocks s ++ [entry]) (s_edges s) in
  Ok (func_term name linkage t_ret2 (tname k0 :: TAtom "sp" :: TAtom "ne" :: map tname ps) s).

(** A function that C calls, `name(arena, st, ...)` with the w
    parameters ps, which reads the young index, the nursery's end and
    the roots' top from the state, runs is, makes the call g of
    lcall's with args, and stores the young index and the roots' top
    back before it returns the value. *)
Definition c_entry (name : string) (ps : list term) (is : list term) (g : term) (args : list term) (s : st) : term :=
  let (q0, s) := fresh s in
  let (q1, s) := fresh s in
  let (yg, s) := fresh s in
  let (r, s) := fresh s in
  let '(call, rl, s) := lcall g (tmpv (tname yg)) t_sp args s in
  let '(split, yg', s) := split_result rl r s in
  let body := [i_let (tname q0) "a" (o_check 0 24 "read") [t_st];
               i_let (tname yg) "w" (o_load 0) [tmpv (tname q0)];
               i_let (TAtom "ne") "w" (o_load 12) [tmpv (tname q0)];
               i_let (TAtom "sp") "w" (o_load 20) [tmpv (tname q0)]]
              ++ is ++ call :: split
              ++ [i_let (tname q1) "a" (o_check 0 24 "write") [t_st];
                  i_store 0 yg' (tname q1); i_store 20 t_sp (tname q1)] in
  let s := mkst (s_next s) (mkpb (TAtom "entry") [] body (j_ret (tmpv (tname r))) :: s_blocks s) (s_edges s) in
  func_term name "export" (TAtom "w") ps s.

(** `anf_main(arena, st)`, which C calls on a fresh arena: it copies the
    pool to the major heap's first words, where its constants' values
    point (which leaves the young index, the nursery's end and the
    roots' top as they are), and runs the program, `anf_run`. *)
Definition main_entry (poolw : Z) : term :=
  let pool := if 0 <? poolw then
                [i_let (TAtom "pool") "p" (TAtom "copy") [TApp "global" [TAtom "anf_pool"]];
                 TApp "call" [TAtom "void"; TApp "global" [TAtom "anf_lower_pool"];
                              TList [a_p t_arena; a_p t_st; a_p (tmpv (TAtom "pool"))]]]
              else [] in
  c_entry "anf_main" [] pool (TApp "global" [TAtom "anf_run"]) [] (mkst 1 [] nm_empty).

(** The dispatcher of arity n, `anf_applyN(arena, st, fid, ...)`,
    which a driver in C calls to apply a closure: a call through the
    table of arity n, whose first fid is lo. *)
Definition dispatcher (n : nat) (lo : Z) : term :=
  let s := mkst 1 [] nm_empty in
  let (ks, s) := fresh_n n s in
  let args := map (fun k => tmpv (tname k)) ks in
  let '(is, k, s) := code_ptr n lo (tmpv (TAtom "fid")) s in
  c_entry ("anf_apply" ++ decimal (Z.of_nat n))%string (TAtom "fid" :: map tname ks) is (tmpv k) args s.

(** The table of arity n: the code of each function named, a null
    pointer for none (a call through it traps). *)
Definition table_item (n : nat) (names : list string) : term :=
  TApp "data" [TAtom (table_name n); TApp "ro" [TAtom "local"]; TInt 8;
               TList (match names with
                      | [] => [TApp "zero" [TInt 8]]
                      | _ => map (fun f => TApp "item" [TAtom "p"; TApp "sym" [TAtom f; TInt 0]]) names
                      end)].

(** ## The module *)

(** The order of integers. *)
Definition zcompare (a b : Z) : comparison := Z.compare a b.

(** What [lower] tells of a program besides its module: how many
    hoisted functions it has, how many of them became blocks of
    another's IR function (joins and loops), and how many are values,
    with a fid. *)
Record counts := mkcounts { n_functions : nat; n_blocks : nat; n_fids : nat }.

(** The variables e binds, added to the map m, or the first one it
    binds twice: the lowering keys its tables by variable, so every
    binder of the program must be unique, as CertiRocq makes them. *)
Fixpoint binders (e : exp) (m : ZMap.t unit) : res (ZMap.t unit) :=
  let bind x m := if ZMap.mem x m then Err ("a variable bound twice: " ++ decimal x)%string
                  else Ok (ZMap.add x tt m) in
  let binds xs m := fold_left (fun r x => let? m := r in bind x m) xs (Ok m) in
  match e with
  | Econstr x _ _ e' | Eproj x _ _ _ e' | Eletapp x _ _ _ _ e' | Eprim_val x e' | Eprim x _ _ _ e' =>
      let? m := bind x m in binders e' m
  | Ecase _ arms =>
      (fix go (l : list (Z * exp)) (m : ZMap.t unit) : res (ZMap.t unit) :=
         match l with [] => Ok m | (_, e1) :: l' => let? m := binders e1 m in go l' m end) arms m
  | Efun fds e' =>
      let? m := (fix go (fds : fundefs) (m : ZMap.t unit) : res (ZMap.t unit) :=
                   match fds with
                   | Fnil => Ok m
                   | Fcons f _ xs body rest =>
                       let? m := bind f m in let? m := binds xs m in let? m := binders body m in go rest m
                   end) fds m in
      binders e' m
  | Eapp _ _ _ | Ehalt _ => Ok m
  end.

(** The list stored under the key k of m, or none. *)
Definition zm_list {A : Type} (k : Z) (m : ZMap.t (list A)) : list A :=
  match ZMap.find k m with Some l => l | None => [] end.

(** ## Simplification

    `--anf-variant 8` skips CertiRocq's inliner, so a curried call
    `f x y` of a function f of one parameter stays as CertiRocq's
    closure conversion writes it: a call of f that builds a closure
    and returns it, projections of the closure's code and environment,
    and a call through the code, an uncurry wrapper that projects the
    environment and calls the function that does the work. Through
    `anf_applyN`, that is three calls and two blocks for one.

    [simplify] inlines every function whose body only builds
    constructors and projects fields before it halts or tail-calls
    ([straight]), up to [inline_depth] deep, folds a projection of a
    constructor bound in scope and a case on one, then drops the
    constructors and projections no one reads and the functions no one
    names, and computes the live variables again. The curried call is
    then one direct call, and the closure is never built.

    CertiRocq evaluates every argument before a call, so `orb` and
    `andb` do not short-circuit: `existsb` calls itself on the rest of
    the list before it tests the head, and walks the whole list as deep
    as it is long. [simplify] therefore also inlines a tail call of a
    small case function ([inline_case]) and moves a call into the one
    arm of the case after it that reads its result ([sink]). `existsb`
    and `forallb` then stop where OCaml's `(||)` and `(&&)` stop, and
    their recursive call is a tail call, which becomes a loop.

    CertiRocq also passes each global function to the functions that
    call it, as a closure in their environments. The closures' and the
    environments' tags are the tap's anonymous ones: no constructor of
    the program has them, and neither the runtime nor a driver builds
    a record of them. So [facts_fix] can tell, over the whole program,
    when every record of such a tag holds the same function, or a
    closure of it, in a field; a projection of that field is then that
    function, or a closure whose code is known, and a call through it
    a direct call, which may be inlined in turn. *)

(** Whether e binds at most n constructors and projections, then
    halts or tail-calls. *)
Fixpoint straight (n : nat) (e : exp) : bool :=
  match e with
  | Econstr _ _ _ e' | Eproj _ _ _ _ e' => match n with O => false | S n' => straight n' e' end
  | Ehalt _ | Eapp _ _ _ => true
  | _ => false
  end.

(** How many bindings a body may have to be inlined, and how many
    inlined bodies deep a call may go. *)
Definition inline_size : nat := 8.
Definition inline_depth : nat := 4.

(** A binding of an inlined body, and how it ends: it halts with a
    value or tail-calls g. *)
Inductive sbind := BCon (x t : Z) (ys : list Z) | BProj (x t n y : Z).
Inductive stail := THalt (v : Z) | TCall (g ft : Z) (ys : list Z).

(** The bindings bs around e. *)
Fixpoint wrap (bs : list sbind) (e : exp) : exp :=
  match bs with
  | [] => e
  | BCon x t ys :: bs' => Econstr x t ys (wrap bs' e)
  | BProj x t n y :: bs' => Eproj x t n y (wrap bs' e)
  end.

(** What a field of every record of one tag holds: nothing yet, always
    the function f, always a record of tag t whose field 0 is f (a
    closure of f), or anything. *)
Inductive fact := FNone | FFn (f : Z) | FClo (t f : Z) | FAny.

Definition fjoin (a b : fact) : fact :=
  match a, b with
  | FNone, c | c, FNone => c
  | FFn f, FFn g => if f =? g then a else FAny
  | FClo t f, FClo u g => if (t =? u) && (f =? g) then a else FAny
  | _, _ => FAny
  end.

Definition fleb (a b : fact) : bool :=
  match a, b with
  | FNone, _ | _, FAny => true
  | FFn f, FFn g => f =? g
  | FClo t f, FClo u g => (t =? u) && (f =? g)
  | _, _ => false
  end.

(** For each tag the analysis covers, the fact of each field. *)
Definition facts := ZMap.t (ZMap.t fact).

(** The fact of field n of tag t; anything for a tag not covered. *)
Definition fget (fs : facts) (t n : Z) : fact :=
  match ZMap.find t fs with
  | Some m => match ZMap.find n m with Some a => a | None => FNone end
  | None => FAny
  end.

(** fs with what the records e builds hold joined in, isfn telling the
    functions, loc what each variable in scope is, and fs0 the facts
    that projections give. *)
Fixpoint facts_exp (isfn : Z -> bool) (fs0 : facts) (e : exp) (loc : ZMap.t fact) (fs : facts) : facts :=
  let av y := if isfn y then FFn y else match ZMap.find y loc with Some a => a | None => FAny end in
  match e with
  | Econstr x t ys e' =>
      let fs := match ZMap.find t fs with
                | Some m =>
                    let m := snd (fold_left (fun acc y =>
                                               let '(n, m) := acc in
                                               let old := match ZMap.find n m with Some a => a | None => FNone end in
                                               (n + 1, ZMap.add n (fjoin old (av y)) m)) ys (0, m)) in
                    ZMap.add t m fs
                | None => fs
                end in
      let ax := match ys with f :: _ => if isfn f then FClo t f else FAny | [] => FAny end in
      facts_exp isfn fs0 e' (ZMap.add x ax loc) fs
  | Eproj x t n _ e' => facts_exp isfn fs0 e' (ZMap.add x (fget fs0 t n) loc) fs
  | Ecase _ arms =>
      (fix go (l : list (Z * exp)) (fs : facts) : facts :=
         match l with [] => fs | (_, e1) :: l' => go l' (facts_exp isfn fs0 e1 loc fs) end) arms fs
  | Eletapp x _ _ _ _ e' | Eprim x _ _ _ e' | Eprim_val x e' => facts_exp isfn fs0 e' (ZMap.add x FAny loc) fs
  | Efun _ _ | Eapp _ _ _ | Ehalt _ => fs
  end.

(** The least facts that the bodies es keep, from init (an empty map
    for each tag covered), or none when fuel runs out. *)
Fixpoint facts_fix (fuel : nat) (isfn : Z -> bool) (es : list exp) (init fs : facts) : facts :=
  match fuel with
  | O => ZMap.empty (ZMap.t fact)
  | S fuel' =>
      let fs' := fold_left (fun acc e => facts_exp isfn fs e (ZMap.empty fact) acc) es init in
      if ZMap.fold (fun t m ok => ok && ZMap.fold (fun n a ok => ok && fleb a (fget fs t n)) m true) fs' true
      then fs else facts_fix fuel' isfn es init fs'
  end.

(** What the simplification knows: the variable each removed variable
    stands for, the constructor each known variable is, the closures
    whose code is known (their tag and function), the facts, and the
    next fresh variable. *)
Record simp := mksimp { sm_sub : ZMap.t Z; sm_con : ZMap.t (Z * list Z); sm_code : ZMap.t (Z * Z);
                        sm_facts : facts; sm_next : Z }.

Definition sv (s : simp) (x : Z) : Z := match ZMap.find x (sm_sub s) with Some y => y | None => x end.
Definition svs (s : simp) (xs : list Z) : list Z := map (sv s) xs.
Definition s_sub (x y : Z) (s : simp) : simp :=
  mksimp (ZMap.add x y (sm_sub s)) (sm_con s) (sm_code s) (sm_facts s) (sm_next s).
Definition s_con (x t : Z) (ys : list Z) (s : simp) : simp :=
  mksimp (sm_sub s) (ZMap.add x (t, ys) (sm_con s)) (sm_code s) (sm_facts s) (sm_next s).
Definition s_code (x t f : Z) (s : simp) : simp :=
  mksimp (sm_sub s) (sm_con s) (ZMap.add x (t, f) (sm_code s)) (sm_facts s) (sm_next s).
Definition s_from (n : Z) (s : simp) : simp := mksimp (sm_sub s) (sm_con s) (sm_code s) (sm_facts s) n.

(** The field n of y if y is a known constructor of tag t. *)
Definition known_field (s : simp) (t n y : Z) : option Z :=
  match ZMap.find y (sm_con s) with
  | Some (t', fs) => if t' =? t then nth_error fs (Z.to_nat n) else None
  | None => None
  end.

(** The projection x of the field n of y, of tag t: the variable or
    function it is, if known, and the state, which notes x as a
    closure of f when the facts say so. *)
Definition simp_proj (s : simp) (x t n y : Z) : option Z * simp :=
  match known_field s t n y with
  | Some z => (Some z, s)
  | None =>
      let code := match ZMap.find y (sm_code s) with
                  | Some (t', f) => if (n =? 0) && (t' =? t) then Some f else None
                  | None => None
                  end in
      match code with
      | Some f => (Some f, s)
      | None =>
          match fget (sm_facts s) t n with
          | FFn f => (Some f, s)
          | FClo t' f => (None, s_code x t' f s)
          | _ => (None, s)
          end
      end
  end.

(** The straight body e with its variables renamed by sub (its
    parameters as the caller's values) and its binders fresh from
    next: its bindings, its end, and the next fresh variable. *)
Fixpoint inst (e : exp) (sub : ZMap.t Z) (next : Z) : list sbind * stail * Z :=
  let v x := match ZMap.find x sub with Some y => y | None => x end in
  match e with
  | Econstr x t ys e' =>
      let '(bs, tl, n) := inst e' (ZMap.add x next sub) (next + 1) in (BCon next t (map v ys) :: bs, tl, n)
  | Eproj x t i y e' =>
      let '(bs, tl, n) := inst e' (ZMap.add x next sub) (next + 1) in (BProj next t i (v y) :: bs, tl, n)
  | Eapp g ft ys => ([], TCall (v g) ft (map v ys), next)
  | Ehalt x => ([], THalt (v x), next)
  | _ => ([], THalt 0, next)
  end.

(** The bindings bs with each projection of a known constructor
    removed and its variable standing for the field, and each
    constructor known. *)
Fixpoint simp_binds (bs : list sbind) (s : simp) : list sbind * simp :=
  match bs with
  | [] => ([], s)
  | BCon x t ys :: bs' =>
      let ys := svs s ys in
      let '(bs', s) := simp_binds bs' (s_con x t ys s) in (BCon x t ys :: bs', s)
  | BProj x t n y :: bs' =>
      let y := sv s y in
      match simp_proj s x t n y with
      | (Some z, s) => simp_binds bs' (s_sub x z s)
      | (None, s) => let '(bs', s) := simp_binds bs' s in (BProj x t n y :: bs', s)
      end
  end.

(** The call of g with ys, g's straight body inlined in its place, and
    the call it ends with inlined in turn, d deep: the bindings, the
    end and the state. *)
Fixpoint inline_call (d : nat) (fns : ZMap.t (list Z * exp)) (g ft : Z) (ys : list Z) (s : simp)
  : list sbind * stail * simp :=
  match d, ZMap.find g fns with
  | S d', Some (xs, body) =>
      if straight inline_size body && Nat.eqb (length xs) (length ys) then
        let sub := fold_left (fun m p => ZMap.add (fst p) (snd p) m) (combine xs ys) (ZMap.empty Z) in
        let '(bs, tl, next) := inst body sub (sm_next s) in
        let '(bs, s) := simp_binds bs (s_from next s) in
        match tl with
        | THalt v => (bs, THalt (sv s v), s)
        | TCall h ht zs =>
            let '(bs2, tl2, s) := inline_call d' fns (sv s h) ht (svs s zs) s in (bs ++ bs2, tl2, s)
        end
      else ([], TCall g ft ys, s)
  | _, _ => ([], TCall g ft ys, s)
  end.

(** Whether the arms are those of a small case function, such as
    `orb`, `andb` or `negb`: at most four, each binding at most two
    constructors or projections before it halts. An arm that calls
    another function is a join point of the caller's cluster, which
    the inlining would split off as a function of its own. *)
Definition small_arms (arms : list (Z * exp)) : bool :=
  (length arms <=? 4)%nat
  && forallb (fun a => straight 2 (snd a)
                       && (fix halts (e : exp) : bool :=
                             match e with
                             | Econstr _ _ _ e' | Eproj _ _ _ _ e' => halts e'
                             | Ehalt _ => true
                             | _ => false
                             end) (snd a)) arms.

(** The tail call of g with ys, when g's body is a case of a small
    case function ([small_arms]): the case, its arms' bodies renamed
    and their projections of known constructors folded, and only the
    arm of a known scrutinee. CertiRocq evaluates both of `orb`'s and
    `andb`'s arguments before the call, so `f a || existsb f l` calls
    `existsb` before it tests `f a`; with the case inlined, [dce] moves
    that call into the one arm that reads it. *)
Definition inline_case (fns : ZMap.t (list Z * exp)) (g : Z) (ys : list Z) (s : simp)
  : option (exp * simp) :=
  match ZMap.find g fns with
  | Some (xs, Ecase x arms) =>
      if small_arms arms && Nat.eqb (length xs) (length ys) then
        let sub := fold_left (fun m p => ZMap.add (fst p) (snd p) m) (combine xs ys) (ZMap.empty Z) in
        let x := sv s (match ZMap.find x sub with Some y => y | None => x end) in
        let kt := match ZMap.find x (sm_con s) with Some (t, _) => Some t | None => None end in
        let arm (s : simp) (e1 : exp) : exp * simp :=
          let '(bs, tl, next) := inst e1 sub (sm_next s) in
          let '(bs, s) := simp_binds bs (s_from next s) in
          match tl with
          | THalt v => (wrap bs (Ehalt (sv s v)), s)
          | TCall h ht zs => (wrap bs (Eapp (sv s h) ht (svs s zs)), s)
          end in
        match kt with
        | Some t =>
            match find (fun a => fst a =? t) arms with
            | Some (_, e1) => Some (arm s e1)
            | None => None
            end
        | None =>
            let '(arms, s) := fold_left (fun acc a =>
                                           let '(l, s) := acc in
                                           let (e1, s) := arm s (snd a) in ((fst a, e1) :: l, s))
                                        arms ([], s) in
            Some (Ecase x (rev arms), s)
        end
      else None
  | _ => None
  end.

(** Whether the variable x occurs in e. Binders are unique, so this is
    whether e reads it. *)
Fixpoint occurs (x : Z) (e : exp) : bool :=
  match e with
  | Econstr _ _ ys e' | Eprim _ _ ys _ e' => existsb (Z.eqb x) ys || occurs x e'
  | Ecase y arms =>
      (y =? x) || (fix go (l : list (Z * exp)) : bool :=
                     match l with [] => false | (_, e1) :: l' => occurs x e1 || go l' end) arms
  | Eproj _ _ _ y e' => (y =? x) || occurs x e'
  | Eletapp _ f _ ys _ e' => (f =? x) || existsb (Z.eqb x) ys || occurs x e'
  | Efun _ e' | Eprim_val _ e' => occurs x e'
  | Eapp f _ ys => (f =? x) || existsb (Z.eqb x) ys
  | Ehalt y => y =? x
  end.

(** The call of g that binds x, then e. When e is a case on another
    variable and one arm alone reads x, the call moves into that arm.
    A Gallina function is pure and total, so the call may run on that
    arm's path only, and when the arm returns its value it becomes a
    tail call. With [inline_case], `existsb` and `forallb` stop at the
    first element that decides them, as OCaml's `(||)` and `(&&)` do,
    and loop instead of recursing. [dce] computes the live variables
    again. *)
Definition sink (x g gt : Z) (zs live : list Z) (e : exp) : exp :=
  let call e1 := Eletapp x g gt zs live e1 in
  match e with
  | Ecase y arms =>
      if negb (y =? x) && (length (filter (fun a => occurs x (snd a)) arms) =? 1)%nat
      then Ecase y (map (fun a => if occurs x (snd a) then (fst a, call (snd a)) else a) arms)
      else call e
  | _ => call e
  end.

(** The expression e simplified. *)
Fixpoint simp_exp (fns : ZMap.t (list Z * exp)) (e : exp) (s : simp) : exp * simp :=
  match e with
  | Econstr x t ys e' =>
      let ys := svs s ys in
      let (e', s) := simp_exp fns e' (s_con x t ys s) in (Econstr x t ys e', s)
  | Eproj x t n y e' =>
      let y := sv s y in
      match simp_proj s x t n y with
      | (Some z, s) => simp_exp fns e' (s_sub x z s)
      | (None, s) => let (e', s) := simp_exp fns e' s in (Eproj x t n y e', s)
      end
  | Ecase x arms =>
      let x := sv s x in
      let kt := match ZMap.find x (sm_con s) with Some (t, _) => t | None => -1 end in
      let known :=
        (fix pick (l : list (Z * exp)) : option (exp * simp) :=
           match l with
           | [] => None
           | (t, e1) :: l' => if t =? kt then Some (simp_exp fns e1 s) else pick l'
           end) arms in
      match known with
      | Some r => r
      | None =>
          let '(arms, s) :=
            (fix go (l : list (Z * exp)) (s : simp) : list (Z * exp) * simp :=
               match l with
               | [] => ([], s)
               | (t, e1) :: l' => let (e1, s) := simp_exp fns e1 s in
                                  let (l', s) := go l' s in ((t, e1) :: l', s)
               end) arms s in
          (Ecase x arms, s)
      end
  | Eletapp x f ft ys live e' =>
      let '(bs, tl, s) := inline_call inline_depth fns (sv s f) ft (svs s ys) s in
      match tl with
      | THalt v => let (e', s) := simp_exp fns e' (s_sub x v s) in (wrap bs e', s)
      | TCall g gt zs => let (e', s) := simp_exp fns e' s in (wrap bs (sink x g gt zs live e'), s)
      end
  | Eapp f ft ys =>
      let '(bs, tl, s) := inline_call inline_depth fns (sv s f) ft (svs s ys) s in
      match tl with
      | THalt v => (wrap bs (Ehalt v), s)
      | TCall g gt zs =>
          match inline_case fns g zs s with
          | Some (e, s) => (wrap bs e, s)
          | None => (wrap bs (Eapp g gt zs), s)
          end
      end
  | Eprim_val x e' => let (e', s) := simp_exp fns e' s in (Eprim_val x e', s)
  | Eprim x p ys live e' => let (e', s) := simp_exp fns e' s in (Eprim x p (svs s ys) live e', s)
  | Ehalt x => (Ehalt (sv s x), s)
  | Efun _ _ => (e, s)
  end.

(** The expression e without the constructors and projections no one
    reads, with the live variables of each call and primitive computed
    again and a call whose result is returned at once a tail call, as
    [dexp] makes them; and its free variables. *)
Fixpoint dce (e : exp) : exp * list Z :=
  match e with
  | Econstr x t ys e' =>
      let (e', fv) := dce e' in
      if existsb (Z.eqb x) fv then (Econstr x t ys e', zunion (zset ys) (zremove x fv)) else (e', fv)
  | Eproj x t n y e' =>
      let (e', fv) := dce e' in
      if existsb (Z.eqb x) fv then (Eproj x t n y e', zinsert y (zremove x fv)) else (e', fv)
  | Ecase x arms =>
      let '(arms, fv) :=
        (fix go (l : list (Z * exp)) : list (Z * exp) * list Z :=
           match l with
           | [] => ([], [])
           | (t, e1) :: l' => let (e1, fv1) := dce e1 in let (l', fv2) := go l' in ((t, e1) :: l', zunion fv1 fv2)
           end) arms in
      (Ecase x arms, zinsert x fv)
  | Eletapp x g ft ys _ e' =>
      let (e', fv) := dce e' in
      match e' with
      | Ehalt x' => if x' =? x then (Eapp g ft ys, zinsert g (zset ys))
                    else (Eletapp x g ft ys (zremove x fv) e', zinsert g (zunion (zset ys) (zremove x fv)))
      | _ => (Eletapp x g ft ys (zremove x fv) e', zinsert g (zunion (zset ys) (zremove x fv)))
      end
  | Eapp g ft ys => (e, zinsert g (zset ys))
  | Eprim_val x e' => let (e', fv) := dce e' in (Eprim_val x e', zremove x fv)
  | Eprim x p ys _ e' => let (e', fv) := dce e' in (Eprim x p ys (zremove x fv) e', zunion (zset ys) (zremove x fv))
  | Ehalt x => (e, [x])
  | Efun _ _ => (e, [])
  end.

(** The functions fds and the program main simplified, the first
    fresh variable being next, keeping only the functions that the
    program names, or a function it names. The facts cover the tags
    of anon, the closures' and environments' with their arities. *)
Definition simplify (anon : list (Z * Z)) (fds : list fdef) (main : exp) (next : Z) : list fdef * exp :=
  let fns := fold_left (fun m fd => ZMap.add (fd_f fd) (fd_xs fd, fd_body fd) m) fds (ZMap.empty (list Z * exp)) in
  let init := fold_left (fun m ta => ZMap.add (fst ta) (ZMap.empty fact) m) anon (ZMap.empty (ZMap.t fact)) in
  let fuel := S (2 * fold_left (fun n ta => n + Z.to_nat (snd ta)) anon O)%nat in
  let fs := facts_fix fuel (fun f => ZMap.mem f fns) (main :: map fd_body fds) init init in
  let s0 := mksimp (ZMap.empty Z) (ZMap.empty (Z * list Z)) (ZMap.empty (Z * Z)) fs next in
  let '(main, s) := simp_exp fns main s0 in
  let '(fds, _) := fold_left (fun acc fd =>
                                let '(l, s) := acc in
                                let (b, s) := simp_exp fns (fd_body fd) s in
                                (mkfd (fd_f fd) (fd_xs fd) b :: l, s)) fds ([], s) in
  let fds := rev fds in
  let (main, mfv) := dce main in
  let fds := map (fun fd => let (b, fv) := dce (fd_body fd) in (mkfd (fd_f fd) (fd_xs fd) b, fv)) fds in
  let fvs := fold_left (fun m p => ZMap.add (fd_f (fst p)) (snd p) m) fds (ZMap.empty (list Z)) in
  let reach := (fix go (fuel : nat) (todo : list Z) (seen : ZMap.t unit) : ZMap.t unit :=
                  match fuel, todo with
                  | O, _ | _, [] => seen
                  | S fuel', x :: todo' =>
                      if ZMap.mem x seen || negb (ZMap.mem x fvs) then go fuel' todo' seen
                      else go fuel' (zm_list x fvs ++ todo') (ZMap.add x tt seen)
                  end) (S (length fds + fold_left (fun n p => n + length (snd p)) fds (length mfv)))%nat
                 mfv (ZMap.empty unit) in
  (map fst (filter (fun p => ZMap.mem (fd_f (fst p)) reach) fds), main).

(** The module of the program the tap's clauses cs describe: an
    exported `anf_main(arena, st)` that runs the program and returns
    its value, an IR function for each cluster, a dispatcher for each
    arity a closure is called with, and the pool of its constants. *)
Definition lower (cs : list term) : res (term * counts) :=
  let? p := read_clauses cs (mkprog [] [] [] None) in
  let? body := match p_body p with Some e => Ok e | None => Err "no anf_body" end in
  let? bound := binders body (ZMap.empty unit) in
  let '(fds, main) := match body with
                      | Efun fds e => (fundefs_list fds, e)
                      | e => ([], e)
                      end in
  if negb (forallb flat (main :: map fd_body fds)) then Err "a nested Efun"
  else
    let anon := flat_map (fun tc => if String.eqb (c_name (snd tc)) "_" then [(fst tc, c_arity (snd tc))] else [])
                         (p_ctors p) in
    let '(fds, main) := simplify anon fds main (ZMap.fold (fun x _ m => Z.max (x + 1) m) bound 1) in
    let fnset := fold_left (fun m fd => ZMap.add (fd_f fd) fd m) fds (ZMap.empty fdef) in
    let isfn f := ZMap.mem f fnset in
    let evs := fold_left (fun acc fd => events isfn (fd_f fd) (fd_body fd) acc) fds
                         (events isfn 0 main []) in
    let escapes := fold_left (fun m ev => match ev with Escape f => ZMap.add f tt m | _ => m end)
                             evs (ZMap.empty unit) in
    let lets := fold_left (fun m ev => match ev with LetCall f => ZMap.add f tt m | _ => m end)
                          evs (ZMap.empty unit) in
    let arities := Order.sort Nat.compare
                     (flat_map (fun ev => match ev with Indirect n => [n] | _ => [] end) evs) in
    let callers := fold_left (fun m ev => match ev with
                                          | TailCall c g => ZMap.add g (c :: zm_list g m) m
                                          | _ => m
                                          end) evs (ZMap.empty (list Z)) in
    let cands := flat_map (fun fd =>
                             let f := fd_f fd in
                             if ZMap.mem f escapes || ZMap.mem f lets then []
                             else match zm_list f callers with [] => [] | cs => [(f, cs)] end) fds in
    let fuel := S (length fds) in
    let par := absorb fuel fuel cands (ZMap.empty Z) in
    let rootf f := root_of fuel par f in
    (* fids: the escaping functions, by arity then name *)
    let esc_fds := Order.msort (fun a b => match Nat.compare (length (fd_xs a)) (length (fd_xs b)) with
                                           | Eq => zcompare (fd_f a) (fd_f b)
                                           | o => o
                                           end)
                     (filter (fun fd => ZMap.mem (fd_f fd) escapes) fds) in
    let fids := snd (fold_left (fun acc fd => (fst acc + 1, ZMap.add (fd_f fd) (fst acc) (snd acc)))
                               esc_fds (0, ZMap.empty Z)) in
    let tbl_lo n := match find (fun fd => Nat.eqb (length (fd_xs fd)) n) esc_fds with
                    | Some fd => match ZMap.find (fd_f fd) fids with Some k => k | None => 0 end
                    | None => 0
                    end in
    (* each cluster's absorbed functions, in order, and each function's
       place in its cluster: the root 0, then the absorbed ones from 1 *)
    let membs := fold_right (fun fd m =>
                               let f := fd_f fd in
                               let r := rootf f in
                               if r =? f then m else ZMap.add r (fd :: zm_list r m) m)
                            (ZMap.empty (list fdef)) fds in
    let members r := zm_list r membs in
    let segs := ZMap.fold (fun _ l m => snd (fold_left (fun acc fd => (fst acc + 1, ZMap.add (fd_f fd) (fst acc) (snd acc)))
                                                       l (1, m)))
                          membs (ZMap.empty Z) in
    let seg_of f := match ZMap.find f segs with Some i => i | None => 0 end in
    let names := fold_left (fun m vn => ZMap.add (fst vn) (snd vn) m) (p_names p) (ZMap.empty string) in
    let name_of f := match ZMap.find f names with
                     | Some s => ("anf_" ++ symbol_string s ++ "_" ++ decimal f)%string
                     | None => ("anf_f" ++ decimal f)%string
                     end in
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
    let rl := roles (p_ctors p) in
    let cw := ctor_word (p_ctors p) in
    let prims := fold_left (fun m q => ZMap.add (fst q) (snd q) m) (p_prims p) (ZMap.empty string) in
    let kc := mkkc ctors rl (cw "bool"%string "true"%string 3) (cw "bool"%string "false"%string 1) fids prims in
    (* the constants of every body, and those the pool holds *)
    let kv := fold_left (fun kv fd => kfold kc (fd_body fd) kv) fds (kfold kc main (ZMap.empty cval)) in
    let used := fold_left (fun u fd => kuses kv (fd_body fd) u) fds (kuses kv main (ZMap.empty unit)) in
    let '(kw, pl) := ZMap.fold (fun x _ acc =>
                                  let '(kw, pl) := acc in
                                  match ZMap.find x kv with
                                  | Some k => let (w, pl) := materialize k pl in (ZMap.add x w kw, pl)
                                  | None => acc
                                  end) used (ZMap.empty Z, pool0) in
    let poolw := Z.of_nat (length (pl_words pl)) in
    let c := mkcl ctors inds fns rl kv kw prims (cw "bool"%string "true"%string 3) (cw "bool"%string "false"%string 1)
                  (cw "comparison"%string "Eq"%string 1) (cw "comparison"%string "Lt"%string 3) (cw "comparison"%string "Gt"%string 5)
                  (cw "list"%string "nil"%string 1) (ctor_header (p_ctors p) "list" "cons" 2048)
                  (ctor_header (p_ctors p) "prod" "pair" 2048) poolw (map (fun n => (n, tbl_lo n)) arities) in
    let? main_fn := gen_cluster c "anf_run" "local" 0 [] main (members 0) in
    let? fn_items :=
      fold_right (fun fd acc =>
                    let? items := acc in
                    let f := fd_f fd in
                    if rootf f =? f then
                      let? it := gen_cluster c (name_of f) "local" f (fd_xs fd) (fd_body fd) (members f) in
                      Ok (it :: items)
                    else Ok items) (Ok []) fds in
    let disps := map (fun n => dispatcher n (tbl_lo n)) arities in
    let tables := map (fun n => table_item n (map (fun fd => name_of (fd_f fd))
                                                  (filter (fun fd => Nat.eqb (length (fd_xs fd)) n) esc_fds)))
                      arities in
    Ok (TApp "module" [TList (main_entry poolw :: main_fn :: fn_items ++ disps ++ tables
                              ++ (if 0 <? poolw then [pool_item pl] else []))],
        mkcounts (length fds) (length (filter (fun fd => negb (rootf (fd_f fd) =? fd_f fd)) fds))
                 (length esc_fds)).

(** ## Examples *)

(** A program that builds the constant `Cons(Nil, Nil)` and returns
    it: the constant is a block of the pool, `[2048, 1, 1]` after the
    pool's length, which the entry copies to word 1 of the major heap
    (`anf_lower_pool`), so the program, `anf_run`, has two blocks, the
    entry and the body, which returns the word `1 << 1` and its young
    index. *)
Example lower_constant :
  match lower [TApp "anf_ctor" [TInt 1; TInt 1; TInt 0; TInt 0; TAtom "Nil"];
               TApp "anf_ctor" [TInt 2; TInt 1; TInt 2; TInt 0; TAtom "Cons"];
               TApp "anf_body" [TApp "constr" [TInt 5; TInt 1; TList [];
                 TApp "constr" [TInt 6; TInt 2; TList [TInt 5; TInt 5]; TApp "halt" [TInt 6]]]]] with
  | Ok (TApp "module" [TList [TApp "func" [TAtom "anf_main"; _; _; _; _];
                              TApp "func" [TAtom "anf_run"; _; _; _; TList [_; TApp "block" [_; _; TList is; TApp "rets" [_]]]];
                              TApp "data" [TAtom "anf_pool"; _; _; TList items]]], _) =>
      Some (hd (cst 0) (flat_map (fun i => match i with
                                          | TApp "let" [_; TAtom "l"; TApp "ext" [_]; TList [a]] => [a]
                                          | _ => [] end) is),
            map (fun i => match i with TApp "item" [_; TApp "const" [TInt w]] => w | _ => -1 end) items)
  | _ => None
  end = Some (TApp "const" [TInt 2], [3; 2048; 1; 1]).
Proof. vm_compute. reflexivity. Qed.

(** The stdlib's numbers and strings are represented ([roles]): the
    literal `S (S O)` is the immediate of 2, `5`, and the string
    `String (Ascii true false ... false) EmptyString` ("A", code 65)
    is a block of bytes in the pool: its header (arity 2, bytes), its
    length 1, and the byte. *)
Example lower_represented :
  let bits := [TInt 21; TInt 20; TInt 20; TInt 20; TInt 20; TInt 20; TInt 21; TInt 20] in
  match lower ([TApp "anf_ctor" [TInt 10; TInt 1; TInt 0; TInt 0; TAtom "O"; TAtom "nat"];
                TApp "anf_ctor" [TInt 11; TInt 1; TInt 1; TInt 0; TAtom "S"; TAtom "nat"];
                TApp "anf_ctor" [TInt 12; TInt 2; TInt 0; TInt 0; TAtom "false"; TAtom "bool"];
                TApp "anf_ctor" [TInt 13; TInt 2; TInt 0; TInt 1; TAtom "true"; TAtom "bool"];
                TApp "anf_ctor" [TInt 14; TInt 3; TInt 8; TInt 0; TAtom "Ascii"; TAtom "ascii"];
                TApp "anf_ctor" [TInt 15; TInt 4; TInt 0; TInt 0; TAtom "EmptyString"; TAtom "string"];
                TApp "anf_ctor" [TInt 16; TInt 4; TInt 2; TInt 0; TAtom "String"; TAtom "string"];
                TApp "anf_ctor" [TInt 17; TInt 5; TInt 2; TInt 0; TAtom "pair"; TAtom "prod"];
                TApp "anf_body" [
                  TApp "constr" [TInt 20; TInt 12; TList [];
                  TApp "constr" [TInt 21; TInt 13; TList [];
                  TApp "constr" [TInt 30; TInt 10; TList [];
                  TApp "constr" [TInt 31; TInt 11; TList [TInt 30];
                  TApp "constr" [TInt 32; TInt 11; TList [TInt 31];
                  TApp "constr" [TInt 40; TInt 14; TList bits;
                  TApp "constr" [TInt 41; TInt 15; TList [];
                  TApp "constr" [TInt 42; TInt 16; TList [TInt 40; TInt 41];
                  TApp "constr" [TInt 50; TInt 17; TList [TInt 32; TInt 42];
                  TApp "halt" [TInt 50]]]]]]]]]]]]) with
  | Ok (TApp "module" [TList [_; _; TApp "data" [_; _; _; TList items]]], _) =>
      Some (map (fun i => match i with TApp "item" [_; TApp "const" [TInt w]] => w | _ => -1 end) items)
  | _ => None
  end = Some [6; 2304; 1; 65; 2048; 5; 2].
Proof. vm_compute. reflexivity. Qed.

(** A function that conses its argument onto `Nil` when it is `Nil`,
    called but not in tail position, allocates in the nursery: its own
    IR function tests the nursery once, and the slow path collects
    (`anf_lower_reserve`). (Without the case, [simplify] would inline
    it.) *)
Example lower_cons :
  match lower [TApp "anf_ctor" [TInt 1; TInt 1; TInt 0; TInt 0; TAtom "Nil"];
               TApp "anf_ctor" [TInt 2; TInt 1; TInt 2; TInt 0; TAtom "Cons"];
               TApp "anf_body" [TApp "fun" [
                 TList [TApp "def" [TInt 7; TInt 1; TList [TInt 8];
                          TApp "case" [TInt 8; TList [
                            TApp "arm" [TInt 2; TApp "halt" [TInt 8]];
                            TApp "arm" [TInt 1;
                          TApp "constr" [TInt 5; TInt 1; TList [];
                            TApp "constr" [TInt 6; TInt 2; TList [TInt 8; TInt 5]; TApp "halt" [TInt 6]]]]]]]];
                 TApp "constr" [TInt 9; TInt 1; TList [];
                   TApp "letapp" [TInt 10; TInt 7; TInt 1; TList [TInt 9];
                     TApp "constr" [TInt 11; TInt 2; TList [TInt 10; TInt 9]; TApp "halt" [TInt 11]]]]]]] with
  | Ok (TApp "module" [TList [_; _; TApp "func" [_; _; _; _; TList blocks]]], _) =>
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
  end = Some (8%nat, 1%nat).
Proof. vm_compute. reflexivity. Qed.
