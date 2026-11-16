(** A change to the hi_atexit image can break process startup long
    before any proof notices: a unit can go missing, or a constructor
    can read a symbol that the image no longer defines. This file runs
    the linked program from `c: __libc_start_main` with one small,
    concrete argv, environ and auxv, and checks by computation that it
    prints "hello" and exits with status 0.

    ## Why the external answers are a test oracle

    The model's driver stops at every call to a libpizlo or system
    function, because the image does not define those functions. This
    file answers each such call with one fixed result: it sets and reads
    the thread cookie, zeroes cpuid's outputs, fills getrandom's buffer,
    writes a nonzero time for clock_gettime, records the bytes of each
    write, and returns 0 from the other calls. These answers are a test
    oracle chosen to let one run finish. They are not the startup
    contracts, they cover no other answers, and no proof may cite them.
    The proof that hi_atexit never panics uses the contracts of the
    startup world instead.

    ## The concrete start

    The run passes argc 1, argv {"hi", NULL}, environ {"HOME=/", NULL}
    and an auxv whose only entry gives a page size of 4096. The model
    keeps those arguments, and the constructor pointers in the order
    that libpizlo's loader would use, in the runner's table. This file
    fills that table in a copy of the image and appends the argument
    objects after every other item, so no symbol of the image moves. *)

From Glibc Require Import GlibcTactics.
From Stdlib Require Import String ZArith List Bool.
From Nanofil Require Import Term Syntax Values Memory Semantics Run Runtime.
From Glibc Require Import HiAtexitModule StartCtors.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** ## The started image *)

(** These objects hold the strings and the three arrays. *)
Definition hi_run_args : list item :=
  [IData (TAtom "hi_run#arg0") LLocal 1 [Str [104; 105; 0]];
   IData (TAtom "hi_run#env0") LLocal 1 [Str [72; 79; 77; 69; 61; 47; 0]];
   IData (TAtom "hi_run#argv") LLocal 8 [Sym (TAtom "hi_run#arg0") 0; Zero 8];
   IData (TAtom "hi_run#env") LLocal 8 [Sym (TAtom "hi_run#env0") 0; Zero 8];
   IData (TAtom "hi_run#auxv") LLocal 8 [Item Wl 6; Item Wl 4096; Item Wl 0; Item Wl 0]].

(** The filled runner table holds argc, argv, environ and the three
    constructors, with `c: _init_first` first. *)
Definition hi_run_table : item :=
  IData ctor_table_name (LRo (TAtom "local")) 8
    ([Item Wl 1; Sym (TAtom "hi_run#argv") 0; Sym (TAtom "hi_run#env") 0;
      Sym (TAtom "glibc_init_first#_init_first") 0; Sym (TAtom "glibc_stdfiles#_IO_stdfiles_init") 0;
      Sym (TAtom "glibc_vtables#check_stdfiles_vtables") 0])%list.

(** The started image replaces the runner's zero table by the filled
    one, which has the same size, and appends the argument objects. *)
Definition hi_run_module : module :=
  (firstn (length hi_module - 3) hi_module ++ [hi_run_table] ++
   skipn (length hi_module - 2) hi_module ++ hi_run_args)%list.

(** ## The oracle's answers *)

(** The oracle remembers the thread cookie that startup sets and every
    write that the program makes, newest first. *)
Record hi_run_os := mkRunOs { ro_cookie : ptr; ro_writes : list (Z * list Z) }.

(** cpuid writes each of its output words; the oracle writes zeros. *)
Definition hi_run_zero (m : mem) (xs : list word) : mem :=
  fold_left (fun m x => match x with WPtr p => store_bytes m (ptr_addr p) 4 0 | _ => m end) xs m.

(** A call that the image does not define either gets an answer, which
    is an optional result word, a memory and a new oracle state, or ends
    the process with an exit status. Any other call has no answer, and
    the run stops there. *)
Inductive hi_run_answer :=
| Answer (r : option word) (m : mem) (o : hi_run_os)
| Exit (status : Z).

(** The oracle answers each call by its name and arguments. *)
Definition hi_run_oracle (f : string) (xs : list word) (m : mem) (o : hi_run_os) : option hi_run_answer :=
  match f, xs with
  | "zmake_setjmp_save_sigmask", _ | "zregister_sys_errno_handler", _
  | "zregister_sys_dlerror_handler", _ | "zsys_futex_wake", _ => Some (Answer None m o)
  | "zthread_self_cookie", _ => Some (Answer (Some (WPtr (ro_cookie o))) m o)
  | "zthread_set_self_cookie", [WPtr p] => Some (Answer None m (mkRunOs p (ro_writes o)))
  | "zthread_self", _ => Some (Answer (Some (WPtr (mkPtr 0 CNone))) m o)
  | "zthread_self_id", _ => Some (Answer (Some (WInt 1)) m o)
  | "zcpuid", _ :: outs => Some (Answer None (hi_run_zero m outs) o)
  | "zcpuid_count", _ :: _ :: outs => Some (Answer None (hi_run_zero m outs) o)
  | "zxgetbv", _ => Some (Answer (Some (WInt 0)) m o)
  | "zsys_clock_gettime", [_; WPtr ts] =>
      Some (Answer (Some (WInt 0))
        (store_bytes (store_bytes m (ptr_addr ts) 8 1700000000) (ptr_addr ts + 8) 8 123456789) o)
  | "zsys_getrandom", [WPtr b; WInt len; _] =>
      Some (Answer (Some (WInt len)) (store_bytes m (ptr_addr b) len 6510615555426900570) o)
  | ("zsys_getrlimit" | "zsys_sigprocmask" | "zsys_ioctl" | "zsys_fstat" | "zsys_lseek" | "zsys_close"), _ =>
      Some (Answer (Some (WInt 0)) m o)
  | "zsys_write", [WInt fd; WPtr p; WInt k] =>
      Some (Answer (Some (WInt k)) m
        (mkRunOs (ro_cookie o)
           ((fd, map (fun i => m_bytes m (ptr_addr p + Z.of_nat i)) (seq 0 (Z.to_nat k))) :: ro_writes o)))
  | "zsys_exit_soft", [WInt c] => Some (Exit c)
  | _, _ => None
  end.

(** ## The run *)

(** A run is going, or it has exited with a status and its writes, or
    it has stopped because the model or the oracle has no next step. *)
Inductive hi_run_state :=
| Going (c : config) (rt : InterpRuntime.state) (o : hi_run_os)
| Exited (status : Z) (writes : list (Z * list Z))
| Stopped (c : config).

(** When the model is stuck at a direct call to a function that the
    image does not define, the oracle may answer it. The answer binds
    the call's result and moves past the call, as a returning call
    would. *)
Definition hi_run_external (ge : genv) (c : config) (rt : InterpRuntime.state) (o : hi_run_os)
    : hi_run_state :=
  let fr := c_frame c in
  match fr_at fr with
  | Exec l (Call r (Global (TAtom f)) args :: rest) j =>
      match find_fn ge (TAtom f), map_option (arg_x ge (fr_env fr)) args with
      | None, Some xs =>
          match hi_run_oracle f xs (c_mem c) o with
          | Some (Answer res m' o') =>
              let e' := match r, res with CResult d _, Some x => put d x (fr_env fr) | _, _ => fr_env fr end in
              Going (mkConfig (mkFrame (fr_fn fr) e' (fr_locals fr) (fr_doomed fr) (Exec l rest j))
                              (c_callers c) m' (c_fuel c)) rt o'
          | Some (Exit s) => Exited s (rev (ro_writes o))
          | None => Stopped c
          end
      | _, _ => Stopped c
      end
  | _ => Stopped c
  end.

(** One step runs the model, allocates with the interpreter's runtime,
    and asks the oracle only where the model is stuck. *)
Definition hi_run_step (ge : genv) (s : hi_run_state) : hi_run_state :=
  match s with
  | Going c rt o =>
      match step ge c with
      | Next c' => Going c' rt o
      | Fresh q k => match InterpRuntime.alloc rt q with
                     | Some (b, rt') => Going (k b) rt' o
                     | None => Stopped c
                     end
      | Done _ => Stopped c
      | Stuck _ => hi_run_external ge c rt o
      end
  | _ => s
  end.

(** A positive budget p allows at most p steps, as in [run_steps]. *)
Fixpoint hi_run_steps (ge : genv) (p : positive) (s : hi_run_state) : hi_run_state :=
  match p with
  | xH => hi_run_step ge s
  | xO p' => hi_run_steps ge p' (hi_run_steps ge p' s)
  | xI p' => hi_run_steps ge p' (hi_run_steps ge p' (hi_run_step ge s))
  end.

(** The run calls `c: __libc_start_main` with main, argc 1 and the three
    arrays, starting from the loader's memory for the started image and
    a null cookie. It returns the exit status and the writes, or nothing
    when the program has not exited after 100000 steps. *)
Definition hi_run_result : option (Z * list (Z * list Z)) :=
  match initial_memory hi_run_module with
  | None => None
  | Some (g, m) =>
      let ge := mkGenv hi_run_module g InterpRuntime.free in
      let ptr_of s := match lookup (TAtom s) g with Some p => p | None => mkPtr 0 CNone end in
      match find_fn ge (TAtom "__libc_start_main") with
      | Some (Defined f) =>
          match call_frame f [WPtr (ptr_of "main"); WInt 1; WPtr (ptr_of "hi_run#argv");
                              WPtr (ptr_of "hi_run#env"); WPtr (ptr_of "hi_run#auxv")] with
          | Some fr =>
              match hi_run_steps ge 100000 (Going (mkConfig fr [] m 1000000) InterpRuntime.start
                                                  (mkRunOs (mkPtr 0 CNone) [])) with
              | Exited s ws => Some (s, ws)
              | _ => None
              end
          | None => None
          end
      | _ => None
      end
  end.

(** Started this way, the program writes "hello" and a newline to
    standard output and exits with status 0. *)
Lemma hi_run_hello : hi_run_result = Some (0, [(1, [104; 101; 108; 108; 111; 10])]).
Proof. vm_cast_no_check (eq_refl (Some (0, [(1, [104; 101; 108; 108; 111; 10])]))). Qed.
