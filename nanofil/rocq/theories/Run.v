(** Running a function of a module as `interp:run/5` does: prepare
    the module's initial memory, call the function, and take
    [[step|steps]] until an [[outcome]], choosing each allocation's
    base as a [[runtime]] does.

    A run takes its allocations' bases from a [Runtime] (Runtime.v):
    [Driver R] runs with R's choices, and the gates run
    [Driver InterpRuntime] (Transport.v), the [[interpreter]]'s
    allocator. That is one instance of [fresh] allocation, not part of
    the semantics: Semantics.v's [step_rel] allows any fresh base. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Runtime.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** As `data_base/1`: the address where the module's items start. *)
Definition data_base : Z := 65536.

(** As `data_cap/3`: the [[capability]] of data with the linkage lk at
    base, writable or read-only; a weak declaration or an unknown
    linkage has none. *)
Definition data_cap (lk : linkage) (base : Z) : option cap :=
  match lk with
  | LExport | LLocal | LWeak | LTls _ => Some (Obj base)
  | LRo _ | LInit _ _ => Some (Ro base)
  | LExternWeak | LOther _ => None
  end.

(** As `filc_layout/3`: the item it placed after those before it,
    updating the next address, the globals and the objects. A data object
    goes at the next address aligned to 16 or its stricter alignment,
    its size rounded up to 8, with a 16-byte gap after it; a function
    at the next 16-aligned address, 16 bytes, with the capability
    `fn(Name)`. A weak declaration (`extern(weak)`) takes no space and
    stays undefined; an alias waits for [alias_global]. *)
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

(** As `alias_global/3`: an alias's address is its target's, the same
    pointer. *)
Definition alias_global (gs : option (list (name * ptr))) (it : item)
  : option (list (name * ptr)) :=
  let* globals := gs in
  match it with
  | IAlias n _ t => let* p := lookup t globals in Some (put n p globals)
  | _ => Some globals
  end.

(** As `filc_item_contents/4`: one item of a data object written at the
    next address, and the address after it. A pointer item writes its
    symbol's address plus the offset, and the symbol's [[capability]]
    in the [[aux]]; a symbol the module does not define is an external
    one. *)
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

(** As `filc_contents/4`: a data object's items written in order from
    its address; other items write nothing. *)
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

(** The memory with no objects, every byte zero and no stored
    capability. *)
Definition empty_mem : mem := mkMem (fun _ => 0) [] (fun _ => CNone).

(** As `initial_memory/4` in filc mode: the module md's globals, each
    name with its pointer, and the memory with every item placed in
    order from [data_base] ([layout]), aliases bound ([alias_global]),
    and each data object's contents written ([contents]). *)
Definition initial_memory (md : module) : option (list (name * ptr) * mem) :=
  let* l := fold_left layout md (Some (data_base, [], [])) in
  let '(_, globals0, rs) := l in
  let* globals := fold_left alias_global md (Some globals0) in
  let* m := fold_left (contents globals) md
                      (Some (mkMem (m_bytes empty_mem) rs (m_aux empty_mem))) in
  Some (globals, m).

(** What a run ends with: an [[outcome]], or halted where the
    interpreter throws or fails, with the step that was stuck. *)
Inductive run_result : Type :=
| Finished (o : outcome)
| Halted (why : string).

(** ## The driver *)

(** Running under the [[runtime]] R: R's [alloc] chooses each
    allocation's base, and R's free is the genv's. *)
Module Driver (R : Runtime).

(** One step, with the runtime's state beside the configuration. Where
    R refuses an allocation the run ends with `trap(out_of_memory)`, at
    whichever allocation it is: a heap object, a named local or a
    variadic callee's argument snapshot (`alloc_res/6`,
    `inst_result/5`, `call_outcome/8`). *)
Definition run_step (ge : genv) (s : config * R.state) : (config * R.state) + run_result :=
  let (c, rt) := s in
  match step ge c with
  | Next c' => inl (c', rt)
  | Done o => inr (Finished o)
  | Fresh q k =>
      match R.alloc rt q with
      | Some (base, rt') => inl (k base, rt')
      | None => inr (Finished (Trap OutOfMemory))
      end
  | Stuck why => inr (Halted why)
  end.

(** Up to 2^p steps, by halving p, so that the recursion depth is p and
    the gas a positive. The gas is never the limit in practice: the
    run's own [[fuel]] (blocks entered) ends every run first. *)
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

(** As `run/5`: the run of the function fn of the module md on the
    words args, entering at most fuel blocks, from the module's initial
    memory and R's [start]. *)
Definition run (md : module) (fn : name) (args : list word) (fuel : Z) : run_result :=
  match initial_memory md with
  | None => Halted "initial memory"
  | Some (globals, m) =>
      let ge := mkGenv md globals R.free in
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
