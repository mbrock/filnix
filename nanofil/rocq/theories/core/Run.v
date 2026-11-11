(** To execute a compiled C function from a module, the runner must
    first lay out the module's functions and global data objects in
    memory, bind symbol aliases, write each global data object's initial
    bytes and pointer capabilities, and then step the entry function
    until it reaches an [[outcome]]. This module defines that
    initial-memory construction [initial_memory] and the parameterized
    execution functor [Driver].

    When a running program allocates a heap block or a stack frame, the
    operational semantics leaves the choice of the new object's
    [[fresh]] base address to the [[runtime]]. The functor [Driver]
    couples the step function with any [Runtime] implementation that
    supplies an allocator and `c: free`, and instantiating [Driver] with
    [InterpRuntime] produces the executable reference runner that we
    compare against the Prolog [[interpreter]]. *)

From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Ops Semantics Runtime.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## Initial memory layout

    Before the entry function starts, the runner must assign addresses
    and populate the module's global data objects. Three passes perform
    that work: [layout] places declarations, [alias_global] resolves
    symbol aliases, and [contents] writes the initial bytes and
    capabilities. *)

(** The constant [data_base] is the starting address `65536` where the
    module's functions and global data objects are placed. *)
Definition data_base : Z := 65536.

(** Given a data declaration's [linkage] and its base address,
    [data_cap] returns a writable [Obj] capability for ordinary or
    thread-local data, a read-only [Ro] capability for read-only data or
    initializer tables, and `None` for external weak declarations or
    unrecognized linkages. *)
Definition data_cap (lk : linkage) (base : Z) : option cap :=
  match lk with
  | LExport | LLocal | LWeak | LTls _ => Some (Obj base)
  | LRo _ | LInit _ _ => Some (Ro base)
  | LExternWeak | LOther _ => None
  end.

(** Given the running layout state and a top-level module [item],
    [layout] assigns an address to the item and updates the next
    available address, the global symbol map, and the region list.
    Global data objects are aligned to at least 16 bytes with their byte
    size rounded up to 8 bytes followed by a 16-byte gap, while
    functions occupy 16-byte-aligned 16-byte slots carrying a function
    capability [Fn]. External weak declarations and symbol aliases
    consume no address space during this pass. *)
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

(** After [layout] has assigned a pointer to every function and data
    object, [alias_global] binds each [IAlias] symbol in the global
    symbol map to the exact same pointer as its target symbol. *)
Definition alias_global (gs : option (list (name * ptr))) (it : item)
  : option (list (name * ptr)) :=
  let* globals := gs in
  match it with
  | IAlias n _ t => let* p := lookup t globals in Some (put n p globals)
  | _ => Some globals
  end.

(** Given the global symbol map, the current write address and memory
    state, and a single static initializer [data_item], [item_contents]
    writes the initializer into memory and advances the write address. A
    symbol pointer [Sym] writes the symbol's 8-byte address plus offset
    into primary memory and stores the symbol's [[capability]] into the
    shadow [[aux]] slot, using an [External] capability when the symbol
    is not defined in the module. *)
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

(** Given the global symbol map, a memory state, and a top-level module
    [item], [contents] writes the initializer list of a global data
    definition sequentially starting at its base address and leaves
    memory unchanged for functions, aliases, and external weak
    declarations. *)
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

(** The state [empty_mem] is the blank memory with zero at every byte
    address, no registered regions, and [CNone] at every shadow
    capability slot. *)
Definition empty_mem : mem := mkMem (fun _ => 0) [] (fun _ => CNone).

(** Given a compiled [module], [initial_memory] runs the three
    initialization passes in order—[layout], [alias_global], and
    [contents]—to produce the global symbol map paired with the module's
    initial memory state. *)
Definition initial_memory (md : module) : option (list (name * ptr) * mem) :=
  let* l := fold_left layout md (Some (data_base, [], [])) in
  let '(_, globals0, rs) := l in
  let* globals := fold_left alias_global md (Some globals0) in
  let* m := fold_left (contents globals) md
                      (Some (mkMem (m_bytes empty_mem) rs (m_aux empty_mem))) in
  Some (globals, m).

(** A [run_result] is the final result of executing a function: either a
    completed [Finished] run carrying its semantic [[outcome]], or a
    [Halted] diagnostic string when execution gets stuck or exhausts
    driver gas. *)
Inductive run_result : Type :=
| Finished (o : outcome)
| Halted (why : string).

(** ## The driver

    Once initial memory is ready, executing a function requires a
    [Runtime] to answer allocation requests and calls to `c: free`. The
    functor [Driver] pairs the operational configuration with the
    runtime's private state and steps the configuration to completion. *)

(** Given any [Runtime] module R, [Driver] uses [R.alloc] to choose
    the base address of each allocation and [R.free] to execute calls to
    `c: free`. *)
Module Driver (R : Runtime).

(** Given a global environment and a paired configuration and runtime
    state, [run_step] advances the program by one step. When [step]
    requests a [[fresh]] allocation via [Fresh], [run_step] calls
    [R.alloc] to obtain a base address, or ends the run with an
    [OutOfMemory] trap if the allocator refuses the request. *)
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

(** A positive budget p lets [run_steps] perform at most p machine
    steps, stopping early if the driver produces a final result.
    Recursion follows the budget's binary representation rather than a
    unary counter, avoiding a call chain whose depth grows with the step limit. *)
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

(** Given a compiled [module], a function name, a list of argument
    words, and a block-entry [[fuel]] bound, [run] builds the module's
    [initial_memory], creates the initial call frame for the function,
    and runs [run_steps] from `R.start` until the program finishes or
    halts. *)
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
