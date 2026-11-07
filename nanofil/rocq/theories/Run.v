(** Running a function of a module as `interp:run/5` does: prepare
    the module's initial memory, call the function, and take steps until
    an outcome, choosing each allocation's base as the interpreter does.

    ## Preparing a module

    `initial_memory/4` in filc mode places each item in order from
    address 65536: a data object at the next address aligned to 16 or
    its stricter Align, its size rounded up to 8, with a 16-byte gap
    after it; a function at the next 16-aligned address, 16 bytes,
    with the capability `fn(Name)`. An alias is its target's pointer. A
    weak declaration (`extern(weak)`) takes no space and stays
    undefined. Then each data object's items are written: bytes, and
    for a pointer item its symbol's capability in aux.

    ## The runtime

    A run takes its allocations' bases from a `Runtime` (Runtime.v):
    `Driver R` runs with R's choices. The gates run
    `Driver InterpRuntime` (Transport.v), whose `alloc` is
    `alloc_base/6`: the next address aligned for the request, starting
    at 2^32 (`stack_base/1`). That is one instance of `fresh`
    allocation, not part of the semantics: Semantics.v's `step_rel`
    allows any fresh base.

    ## The driver

    `run_steps` takes up to 2^p steps by halving p, so that its gas is
    a positive and never the limit in practice: the run's own fuel
    (blocks entered) ends every run first. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Runtime.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** `data_base/1`. *)
Definition data_base : Z := 65536.

(** `data_cap(Linkage, Base, Cap)`: the capability of data at Base. *)
Definition data_cap (lk : linkage) (base : Z) : option cap :=
  match lk with
  | LExport | LLocal | LWeak | LTls _ => Some (Obj base)
  | LRo _ | LInit _ _ => Some (Ro base)
  | LExternWeak | LOther _ => None
  end.

(** `item_size(Item, Size0, Size)`. *)
Definition item_size (it : data_item) : Z :=
  match it with
  | Item w _ => width_bytes w
  | Str cs => Z.of_nat (length cs)
  | Sym _ _ => 8
  | Zero n => n
  | ItemOther _ => 0
  end.

Definition items_size (its : list data_item) : Z :=
  fold_left (fun s it => s + item_size it) its 0.

(** `filc_layout(Item, A0-Globals0-Rs0, A-Globals-Rs)`. *)
Definition layout (st : option (Z * list (name * ptr) * list region)) (it : item)
  : option (Z * list (name * ptr) * list region) :=
  let* s := st in
  let '(a0, globals, rs) := s in
  match it with
  | IData _ LExternWeak _ [] => Some s
  | IData n lk al items =>
      let align := Z.max al 16 in
      let base := align_up a0 align in
      let end_ := base + (items_size items + 7) / 8 * 8 in
      let* c := data_cap lk base in
      Some (end_ + 16, put n (mkPtr base c) globals,
            mkRegion base end_ GlobalData Live :: rs)
  | IAlias _ _ _ => Some s
  | IFunc f =>
      let base := align_up a0 16 in
      Some (base + 16, put (fn_name f) (mkPtr base (Fn (fn_name f))) globals, rs)
  | IOutside n _ =>
      let base := align_up a0 16 in
      Some (base + 16, put n (mkPtr base (Fn n)) globals, rs)
  end.

(** `alias_global(Item, Globals0, Globals)`: an alias's address is its
    target's, the same pointer. *)
Definition alias_global (gs : option (list (name * ptr))) (it : item)
  : option (list (name * ptr)) :=
  let* globals := gs in
  match it with
  | IAlias n _ t => let* p := lookup t globals in Some (put n p globals)
  | _ => Some globals
  end.

(** `filc_item_contents(Globals, Item, At0-Bytes0-Aux0, At-Bytes-Aux)`. *)
Definition item_contents (globals : list (name * ptr)) (st : option (Z * mem))
    (it : data_item) : option (Z * mem) :=
  let* s := st in
  let (at_, m) := s in
  match it with
  | Sym sym off =>
      if negb (at_ mod 8 =? 0) then None else
      let p := match lookup sym globals with
               | Some p => p
               | None => mkPtr 0 (External sym)
               end in
      Some (at_ + 8, store_aux (store_bytes m at_ 8 ((ptr_addr p + off) mod 2 ^ 64))
                               at_ (ptr_cap p))
  | Item w n =>
      let size := width_bytes w in
      Some (at_ + size, store_bytes m at_ size (n mod 2 ^ (8 * size)))
  | Str cs =>
      Some (at_ + Z.of_nat (length cs),
            fst (fold_left (fun (mi : mem * Z) (c : Z) =>
                              let (m', i) := mi in (store_bytes m' (at_ + i) 1 c, i + 1))
                           cs (m, 0)))
  | Zero n => Some (at_ + n, m)
  | ItemOther _ => None
  end.

(** `filc_contents(Globals, Item, Bytes0-Aux0, Bytes-Aux)`. *)
Definition contents (globals : list (name * ptr)) (st : option mem) (it : item)
  : option mem :=
  let* m := st in
  match it with
  | IData _ LExternWeak _ [] => Some m
  | IData n _ _ items =>
      let* p := lookup n globals in
      let* r := fold_left (item_contents globals) items (Some (ptr_addr p, m)) in
      Some (snd r)
  | _ => Some m
  end.

Definition empty_mem : mem := mkMem (fun _ => 0) [] (fun _ => CNone).

(** `initial_memory(filc, M, Globals, Mem)`. *)
Definition initial_memory (md : module) : option (list (name * ptr) * mem) :=
  let* l := fold_left layout md (Some (data_base, [], [])) in
  let '(_, globals0, rs) := l in
  let* globals := fold_left alias_global md (Some globals0) in
  let* m := fold_left (contents globals) md
                      (Some (mkMem (m_bytes empty_mem) rs (m_aux empty_mem))) in
  Some (globals, m).

(** What a run ends with: an outcome, or stuck where the interpreter
    throws or fails, with the step that was stuck. *)
Inductive run_result : Type :=
| Finished (o : outcome)
| Halted (why : string).

(** ## The driver *)

Module Driver (R : Runtime).

(** One step, with the runtime's state beside the configuration. *)
Definition run_step (ge : genv) (s : config * R.state) : (config * R.state) + run_result :=
  let (c, rt) := s in
  match step ge c with
  | Next c' => inl (c', rt)
  | Done o => inr (Finished o)
  | Fresh q k => let (base, rt') := R.alloc rt q in inl (k base, rt')
  | Stuck why => inr (Halted why)
  end.

(** Up to 2^p steps (the halving makes the recursion depth p). *)
Fixpoint run_steps (ge : genv) (p : positive) (s : config * R.state)
  : (config * R.state) + run_result :=
  match p with
  | xH => run_step ge s
  | xO p' => match run_steps ge p' s with inl s' => run_steps ge p' s' | r => r end
  | xI p' =>
      match run_step ge s with
      | inl s1 => match run_steps ge p' s1 with inl s2 => run_steps ge p' s2 | r => r end
      | r => r
      end
  end.

(** `run(M, Fn, Args, Fuel, Outcome)`. *)
Definition run (md : module) (fn : name) (args : list word) (fuel : Z) : run_result :=
  match initial_memory md with
  | None => Halted "initial memory"
  | Some (globals, m) =>
      let ge := mkGenv md globals in
      match find_fn ge fn with
      | Some (Defined f) =>
          match call_frame f args with
          | Some fr =>
              match run_steps ge (2 ^ 60)%positive (mkConfig fr [] m fuel, R.start) with
              | inr r => r
              | inl _ => Halted "driver gas"
              end
          | None => Halted "call"
          end
      | Some (Outside n) => Halted "outside the core subset"
      | None => Halted "no such function"
      end
  end.

End Driver.
