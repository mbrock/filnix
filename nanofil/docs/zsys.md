# Contracts at the zsys_ boundary

An exploration, not a campaign. Today the formal campaign trusts glibc
through a contract per libc function: Campaign 4 writes them in
[ExternalCalls.v](../rocq/theories/ExternalCalls.v), [Libc.v](../rocq/theories/Libc.v)
and their siblings ([libc-contracts.md](libc-contracts.md)), and
Campaign 3 uses them through `wp_external` ([logic.md](logic.md)). That
continues as it is, for Hello and the campaigns in flight.

This page looks one layer down. Fil-C's user glibc is Fil-C code: it
compiles with Fil-C and makes no system call itself. It calls libpizlo,
the runtime, whose `zsys_` functions are the pizlonated system calls,
next to a few dozen other entry points that are not system calls. If
nanofil compiles user glibc to IR, glibc becomes module code that the
logic proves like Hello's own, and only libpizlo's entry points need
contracts. The page counts that primitive set, measures what Hello
reaches through glibc, sketches how such contracts fit Machine.v,
ExternalMachine.v and the Iris logic, and reports how much of user glibc
nanofil compiles today.

Everything here is read against the staging pin, mbrock/fil-c at
[`18b6663a2785`](https://github.com/mbrock/fil-c/commit/18b6663a2785c8eba6cc2a544a7711e19fc448c7),
as [runtime-axioms.md](runtime-axioms.md) is:

```sh
nix build -o /tmp/filc-ref .#lib.x86_64-linux.filc-staging-ref-src
nix build -o /tmp/libc --impure --expr '
  let f = builtins.getFlake (toString ./.);
      pkgs = import f.inputs.nixpkgs { system = "x86_64-linux"; };
  in (import ./lib/sources.nix {
        inherit pkgs; variant = "staging"; }).user-glibc-src'
```

User glibc is `projects/user-glibc-2.44` in the second tree. The
prototypes are `filc/include/pizlonated_syscalls.h` in the first, and
the implementations are `libpas/src/libpas/filc_runtime.c` (native) and
`filc/src/runtime.c` (Fil-C).

## The primitive set

`pizlonated_syscalls.h` declares **337** `zsys_` functions. They are
not all alike:

| Kind | Count | Examples |
| --- | ---: | --- |
| native wrappers of one system call | 312 | `zsys_read`, `zsys_openat`, `zsys_mmap` |
| loader calls | 4 | `zsys_dlopen`, `zsys_dlsym` |
| Fil-C code in libpizlo | 21 | `zsys_close`, `zsys_fork`, `zsys_syscall` |

A native wrapper has one shape. It checks the capabilities of its
pointer arguments (`filc_check_write(buf, size)` in `zsys_read`, a
Fil-C panic if the check fails), leaves the Fil-C world (`filc_exit`,
so the collector may run), makes the system call, comes back
(`filc_enter`) and, on failure, reports errno through
`filc_set_errno`. That last step calls back into user glibc: libc's
startup registers its `errno_handler` with `zregister_sys_errno_handler`
(`csu/libc-start.c`), and libpizlo calls it with the error number.

Some are system calls only in name, and their contracts would say more
than the kernel's manual page does:

- `zsys_exit_soft` and `zsys_exit_hard` end the process through the
  native libc's `exit(3)` and `_Exit(2)`.
- `zsys_mmap` allocates a fresh collector object for the mapping,
  refuses `PROT_EXEC`, and returns a capability for it; `zsys_munmap`
  and `zsys_mremap` change such objects.
- The futex calls take an absolute timeout and return the error number
  instead of setting errno.
- `zsys_sigaction`, `zsys_sigprocmask` (really `pthread_sigmask`),
  `zsys_raise` and `zsys_abort` go through the runtime's signal
  deferral.
- Twelve come in pairs, a native `_impl` and a Fil-C wrapper that keeps
  libpizlo's own bookkeeping: `zsys_close` clears its descriptor
  table entry around `zsys_close_impl`. `zsys_syscall` dispatches a raw
  syscall number to the others.
- `zsys_isatty`, `zsys_getcwd`, the `keyctl` family and
  `zsys_raw_sched_getaffinity` package a call differently from the
  kernel.

Beyond `zsys_`, `stdfil.h` and `pizlonated_runtime.h` declare about
150 more libpizlo functions. User glibc's `libc.a` calls **45** of them:
threads (`zthread_create2`, `zthread_exit`), `zlongjmp` and the
unwinder (`_Unwind_ForcedUnwind`), fibers for `ucontext`, the collector
(`zgc_realloc`, `zgc_aligned_alloc`), checked copies (`zmemmove`,
`zmemset`), the dynamic call `zcall`, pointer tables, the errno and
dlerror handler registration, x87 control words and `cpuid`, and
diagnostics (`zerror`, `zprintf`). `libc.a` names **272** of the 337
`zsys_` functions, plus `zsys_brk`, which this header no longer
declares.

Under all of these lies the runtime the compiler calls: checks,
allocation, barriers, pollchecks (`filc_*`, about 45 names in `libc.a`).
nanofil's checked IR and Campaign 2's axioms already model that layer;
it is not part of this boundary.

## What Hello reaches

Hello calls 33 libc functions (`hello_externals`). The tool
[survey/glibc/reach.py](../survey/glibc/reach.py) builds a function
graph from `libc.a`'s relocations and follows it from those 33 names
down to the libpizlo names no member of `libc.a` defines.

It over-approximates. A function whose address is stored in anything
reached counts as called: libio's vtables put every stream kind's
methods behind `fclose`. It reads the static `libc.a`, not `libc.so`,
and it does not follow `dlopen`.

**468** glibc symbols, in 245 of `libc.a`'s 1,960 members, reach
**21** `zsys_` functions and **12** other libpizlo names:

- `zsys_`: `read`, `write`, `writev`, `open`, `close`, `lseek`,
  `fstat`, `fstatat`, `ioctl`, `getdents`, `getcwd`, `mmap`, `munmap`,
  `futex_wait`, `futex_wake`, `futex_timedwait`, `getrlimit`,
  `sysinfo`, `wait4`, `exit_soft`, `exit_hard`.
- Others: `zmemmove`, `zmemset`, `zgc_realloc`, `zcall`, `zlongjmp`,
  `zget_jmp_buf_impl_frame`, `_Unwind_ForcedUnwind`, `_Unwind_GetCFA`,
  `__gcc_personality_v0`, `zerror`, `zerrorf`, `zprintf`.

Per call, the picture splits in two:

| Hello's calls | glibc symbols | libpizlo names |
| --- | ---: | --- |
| `strlen`, `strcmp`, `strncmp`, `strrchr`, `memcmp`, `memchr`, `mbsinit`, `__ctype_b_loc`, `__ctype_get_mb_cur_max`, `__errno_location`, `__fpending`, `malloc`, `free`, `iswprint` | 1 to 3 | none |
| `memset`, `memcpy`, `realloc` | 1 or 2 | `zmemset`, `zmemmove`, `zgc_realloc` |
| `_exit` | 1 | `zsys_exit_hard` |
| `abort` | 1 | `zerror` |
| `ferror` | 4 | futex wait and wake |
| `atexit` | 33 | 8, futex and mmap |
| `fclose`, `fputs`, `printf`, `fprintf`, `wprintf`, `mbrtowc`, `mbrtoc32`, `error`, `exit`, `getopt_long`, `setlocale` | 356 to 415 | 27 to 29 |

The first fourteen are plain Fil-C code that calls nothing in
libpizlo. `malloc` and `free` are the runtime's allocation and free:
user glibc's `malloc` is `zgc_alloc`, which the compiler turns into the
runtime's allocation. The last eleven share one core of about 357
symbols. Shortest paths (`reach.py --why`) show where it comes from:

- `fclose` checks the stream's vtable (`_IO_vtable_check`) and so
  reaches every vtable, among them popen's, whose close waits with
  `zsys_wait4`.
- `_IO_un_link` runs a cleanup handler that can unwind a cancelled
  thread (`__pthread_unwind`), which reaches `_Unwind_ForcedUnwind` and
  `zlongjmp`.
- `setlocale` finds locales in the archive (`zsys_open`, `zsys_mmap`)
  and in directories (`zsys_getdents`), and takes the locale lock, a
  rwlock that can wait on a futex.

Hello's proof would show most of this core unreachable, as it does
`abort` and quotearg today: no popen stream exists, no other thread
cancels, and the selected locale profile reads no file. The over-approximation
is a list of the invariants that proof needs, not of the contracts.

## How the contracts would fit

### Machine and ExternalMachine

No new dispatch is needed. `external_site` in
[ExternalMachine.v](../rocq/theories/ExternalMachine.v) already takes
any direct call of a name the module does not define, that is not
global data and not `free`, to the registry. Link glibc's IR into the
module, as [link.pl](../rocq/link.pl) links Hello's objects, and
`printf` becomes a function `find_fn` finds. What is left unresolved is
exactly libpizlo's names, so the registry maps `zsys_read` and its kin
to contracts.

The `contract` record of [ExternalCalls.v](../rocq/theories/ExternalCalls.v)
fits a native wrapper field by field. For `zsys_read(fd, buf, size)`:

| Field | `zsys_read` |
| --- | --- |
| `contract_abi` | an int, a pointer and a size; returns a long |
| `contract_pre` | `buf` writable for `size` bytes, the check `filc_check_write` makes; `fd` not libpizlo's log descriptor |
| `contract_writes` | the span `buf`, `size` |
| `contract_prefix`, `contract_post` | at most `size` bytes of the descriptor's input in `buf`, the count returned; or -1 and an error number |
| `contract_panics` | the capability check, outside the premise |

`zmemmove` and `zmemset` are the checked copies whose contracts already
exist: `copy_contract` and `memset_contract` describe them as well as
glibc's `memcpy` and `memset`, which here only forward to them.
`zsys_mmap` is an allocation step, a `fresh` object made through the
request the contract names, like `malloc`'s. `zgc_realloc` is Campaign
4's `realloc` contract.

### The world gets smaller

The `world` a contract speaks of changes from libc's state to the
operating system's. Today `libc_world` holds the locale, stdio's
buffers and registrations, the stream inventory and getopt's state, and
an observation is `StreamBytes`, bytes stdio accepted. At the zsys_
layer all of that is memory of the module: the `FILE` objects, the
locale tables, `optind`, the exit handler list. The logic owns it
through points-to facts and module invariants, as Hello's proof owns
closeout's static. The world keeps only what no Fil-C code holds:
descriptors and their offsets, file contents and input, the working
directory, and the observations, bytes written to a descriptor and the
process exit.

### Three things the boundary does not have yet

1. **errno is a callback.** A failing wrapper calls libc's
   `errno_handler`, Fil-C code, from inside the primitive. An external
   call is one atomic step today. The callback frames Campaign 4 built
   for exit handlers (Linked.v, milestone 6c) are the precedent; a
   lighter way is to prove `errno_handler`'s triple once and let the
   contracts name its effect, a store into the thread's errno cell.
2. **The syscall stubs call through `zcall`.** Each `syscalls.list`
   entry becomes a function whose whole body returns what `zcall` of the
   `zsys_` function on `zargs` returns: it passes its own argument
   buffer, untyped, to the primitive. nanofil compiles it to IR (below),
   but `zargs` and `zreturn` speak of the frame's argument and return
   buffers, which the machine has no memory for. The choices are to
   model them in Machine.v, to give each stub a contract generated from
   its `syscalls.list` signature, or to generate typed stubs in
   `make-syscalls.sh` for both compilers.
3. **Threads, unwinding and the loader** are reachable only through
   paths the single-thread premise rules out: futex waits with no other
   thread, cancellation, `dlopen` of gconv modules. They can stay
   without contracts, so reaching one is a failure the proof must rule
   out, as `abort` is now. A futex wake with no waiter and a wait on a
   value that changed can have small contracts; a wait that would block
   is a stall, which the logic already treats as no failure.

### The Iris logic

`wp_external` in [Logic.v](../rocq/theories/Logic.v) stays the rule for
a call of a primitive. glibc's functions get triples proven over their
IR, as `mbszero_spec` and `rpl_mbsrtowcs_spec` are over Hello's.

The contracts Campaign 4 has written do not go to waste: they become
the specifications those proofs establish. A lemma of the form "the
module's `strlen` implements `strlen_contract`" would let a proof use
`wp_external` at `strlen` and have the call discharged by glibc's own
code. That lemma can be proved one function at a time, starting with
the fourteen that reach no primitive, without changing the registry
Hello's proof uses. It is the incremental path from today's boundary to
this one.

## What stays trusted

- libpizlo: each wrapper's checks and its native code, the native libc
  beneath it (`exit(3)`, `_Exit`, the loader), and the kernel, through
  the contracts.
- The runtime facts of Campaign 2, as now.
- Startup before the first modeled instruction: the launcher and
  `ld.so`. More of `__libc_start_main` becomes Fil-C code that could be
  proved.
- **Which compiler built glibc.** The proof would be about nanofil's
  IR of glibc. Programs run with filcc's `libc.so`. Either nanofil
  builds the libc a proved program runs with, which is further off than
  compiling glibc to IR, or filcc's build is trusted to agree with
  nanofil's. This is the main new trust question.

What leaves the trusted base is the semantics of the 33 (or 56)
functions Campaign 4 writes by hand: formatting, conversion, getopt,
stdio buffering, the shutdown lifecycle. What grows is the proof: up to
468 glibc symbols for Hello, among them all of `vfprintf`, against 21
functions of Hello's own.

## The experiment: user glibc in nanofil IR

[survey/glibc/capture.nix](../survey/glibc/capture.nix) rebuilds the
staging toolchain's own user glibc with one change: a CC wrapper that
keeps each C translation unit's preprocessed source and its command.
[survey/glibc/run.py](../survey/glibc/run.py) then runs `nanofil cc-ir`
on each shared-library unit (`.os`, 3,114 of them) and records the
result. It passes each unit the environment and options nanofil-cc
would derive from its command (glibc's `-fgnu89-inline` is
`NANOFIL_STD=gnu89`), and the capture preprocesses as nanofil-cc does,
without `__SIZEOF_INT128__` and `__BITINT_MAXWIDTH__`. Neither is part
of any check. The capture builds in about six minutes and the run takes
about five at 6 jobs:

```sh
nix build -f nanofil/survey/glibc/capture.nix -o /tmp/glibc-pp
nanofil/bin/nanofil --save-state /tmp/nanofil.state
export NANOFIL_STATE=/tmp/nanofil.state
python3 nanofil/survey/glibc/run.py /tmp/glibc-pp /tmp/glibc-nf
uv run --with pyelftools python3 nanofil/survey/glibc/reach.py \
  "$(nix build --print-out-paths \
      .#filcc-staging.components.filc-glibc)/lib/libc.a" \
  strlen printf setlocale --units /tmp/glibc-nf/units.tsv
```

The units fail in layers, since nanofil reports one error per unit. Two
opt-in rewrites of the captured text let earlier runs see past the
largest layers, and neither is needed now: `--drop-filc-asm` deletes
the `.filc_*` module asm statements, and `--int128-padding` reads three
unused `__int128_t` padding members as aligned bytes of the same size.

### Results, 2026-11-10

| nanofil | As captured | `--int128-padding` |
| --- | ---: | ---: |
| first survey | 255 | 2,365 with `--drop-filc-asm` |
| three small fixes | 313 | 2,477 with `--drop-filc-asm` |
| `.filc_*` directives, gnu89 | 2,111 (68%) | 2,749 (88%) |
| sign builtins, float asm, forward enums | 2,206 (71%) | 2,866 (92%) |
| declarator attributes, `__int128_t`, no `_BitInt`, alias coalescing | 2,900 (93%) | |
| `address_space` refused only where used | 2,902 (93%) | |
| `packed` members | 2,975 (96%) | |
| `sqrt` and `trunc` | 2,979 (96%) | |
| aliases of thread-local data | 2,982 (96%) | |
| `__alignof__` of an expression | 2,986 (96%) | |
| `__label__`, `#pragma weak` in a body, `rdtsc`, `cvtpd2ps` | 2,991 (96%) | |
| `_Complex float` and `double` | **3,041 (98%)** | |

The last three rows are a new capture, preprocessed without
`__BITINT_MAXWIDTH__`, so `math_uint128.h` takes its portable path. No
unit timed out (120 s); most take under a second.

With both rewrites, before the `.filc_*` directives, by library:

| Library | Units | To IR |
| --- | ---: | ---: |
| libc | 2,057 | 1,911 |
| libm | 672 | 201 |
| iconvdata | 256 | 256 |
| libthread_db | 41 | 40 |
| libnsl | 38 | 38 |
| the other 12 | 50 | 31 |

Of the 245 `libc.a` members that define a function Hello reaches, 244
compile (232 before the declarator-attribute row). Only `atexit` is
missing: it is built into `libc_nonshared.a`, not captured as a shared
unit.

### What stops the rest

First errors (one error per unit, so a fix can uncover the next layer):

| Cause | Units | Where |
| --- | ---: | --- |
| `_Complex long double` returns | 20 | libm's `l` complex functions |
| a product of two complex values | 2 | `cpow`, `cpowf` |
| x87 and MXCSR | 51 | `fnclex`, `frndint`, `__builtin_ia32_ldmxcsr` in libm's fenv |

- **x87 and MXCSR.** Fil-C's own glibc keeps a few x87 instructions
  (`fnclex`, `frndint`, `fnstsw`) as inline asm, which FilPizlonator's
  `validateSafeInlineAsm` accepts, and reads MXCSR through
  `__builtin_ia32_stmxcsr`, a checked memory access. nanofil's IR has
  only the fixed-register instructions of `asm_fixed`.

### Fixes made along the way

Each frontend fix has a test that fails without it:

- `mode(unwind_word)` is DImode on x86-64, as filcc makes it (8 bytes,
  8-aligned, signedness kept). nanofil refused it, and nptl's `pthread.h`
  declares `_Unwind_Word` so. A `doc/3` example in `c_types.pl`.
- `__builtin_mempcpy` and `__builtin_stpcpy` are calls of `mempcpy`
  and `stpcpy`, like the other library builtins (33 units). A `doc/3`
  example.
- An alias may name another alias of the unit, as every generated
  syscall stub does (`weak_alias (__chdir, chdir)`, then
  `strong_alias (chdir, __GI_chdir)`); it is the definition at the end
  of the chain, and a cycle is refused as clang refuses it.
  `tests/c/prog/alias.c` covers it.

- `__builtin_fabs`, `__builtin_copysign` and their `f` and `l` forms
  edit the sign bit through the float's bits (`sign_builtin/3`, with
  `doc/3` examples), and `__builtin_trap` is `unreachable`. glibc's own
  `fabs` and `copysign` are these builtins, so a call would recurse.
  `tests/c/prog/sign-builtins.c`.
- An empty asm statement may pin a float in an SSE or x87 register
  (`=x`, `+x`, `x`, `=t`, `=f` and ties to them), as `math_opt_barrier`
  and `math_force_eval` do. `tests/c/prog/asm-empty.c`.
- A function declared to return an enum before the enum is defined, as
  `nss_files.h` declares `_nss_files_*` before `nss.h` defines `enum
  nss_status`, agrees with its later declarations: their reflected
  types name the same enum. `tests/c/prog/enum-forward.c` fails without
  the fix, as a conflicting declaration, and with the earlier
  declaration's placeholder type kept, as `-2` read back as 4294967294.
- A declaration attribute among a pointer's qualifiers, as glibc writes
  `int *__attribute__((weak, __const__)) __h_errno_location (void)` and
  malloc's hooks, is the declaration's, as clang applies it
  (`ProcessDeclAttributes`): `weak`, `section`, `alias`, `weakref`,
  `constructor`, `destructor`, `gnu_inline` and `common`. In a member
  it is still refused. `tests/c/prog/attr-slide.c`, which fails to link
  if the attributes are dropped.
- `packed` on a member gives it alignment 1 unless `aligned` asks for
  more, whatever the struct's packing, as GCC does: glibc's `struct
  __res_state`, inside `struct pthread`, ends in `__glibc_extension_index
  __attribute__((packed))`, which reached 76 units (all of nptl and
  what touches `THREAD_SELF`). `tests/c/prog/packed-member.c` checks
  offsets, sizes and alignments by hand and against filcc.
- `sqrt` is an IR operation at `s`, `d` and `x` (`ieee_sqrt/3`, rounded
  to nearest even; `sqrtss`, `sqrtsd` and `fsqrt`; NFB opcode 0x31),
  and under `-fno-math-errno`, which glibc builds libm with
  (nanofil-cc and run.py pass it on as `NANOFIL_MATH_ERRNO=0`),
  `__builtin_sqrt`, `sqrtf` and `sqrtl` are it. Otherwise they stay calls of libm, as clang keeps them when
  `errno` must be set. `__builtin_trunc` and `truncf` are built from
  existing operations: a float whose magnitude is below 2^52 (2^23) goes
  through a 64-bit (32-bit) integer and takes back its sign, so `-0.5`
  gives `-0`; a larger one, an infinity or a NaN is `x + 0`. glibc's own
  `sqrt` and `trunc` are these builtins, and read as calls the IR of
  `e_sqrt` recursed: `__ieee754_sqrt` called `sqrt`, whose wrapper calls
  `__ieee754_sqrt`. `tests/float/sqrt.ir` (difftest, plain and `-O`)
  and `tests/c/prog/sqrt-trunc.c` against filcc.
- An alias may name thread-local data (`tls(export)` or `tls(local)`),
  as `errno.c` defines `__libc_errno` for `errno`, `herrno.c`
  `__libc_h_errno` and `res_libc.c` `__libc_resp`. Every global of a
  Fil-C module is reached through its getter, so the alias's getter,
  which calls the target's, reaches this thread's instance, and the
  interpreter gives the alias the target's pointer, as for any alias.
  Rocq's `valid_alias` takes the same linkage. `tests/c/prog/tls-alias.c`,
  two threads against filcc. (clang cannot compile an alias of a static
  thread-local, so the `tls(local)` getter was checked by hand.)
- GNU `__alignof__` of an expression, as glibc's `strcoll_l` and
  `strxfrm_l` assert `__alignof__ (table[0])`: a named object's
  alignment is its declaration's, with its `aligned` and `_Alignas`
  requests, and any other operand's is its type's (`expr_alignment/3`).
  nanofil's types keep no typedef and its members no attributes, so an
  operand whose type is some aligned typedef's (`__alignof__ (*p)` of an
  `A *p`, where clang gives the typedef's alignment) and a member are
  refused rather than answered wrong. `tests/c/prog/alignof-expr.c`
  against filcc; `tests/c/reject/alignof-typedef-expr.c` and
  `alignof-member-expr.c`.
- GNU local labels: `__label__ a, b;` at the start of a block declares
  labels of that block alone, as `strptime_l`'s `get_alt_number` macro
  declares `do_normal` in a statement expression it expands in many
  cases. The parser renames them in the block (label statements,
  `goto`, `&&label` and asm goto labels) to names made from the
  declaration's place in the tokens, so expansions on one line differ
  and an inner declaration shadows an outer one.
  `tests/c/prog/local-label.c` against filcc.
- `#pragma weak` inside a function body, as `td_ta_map_lwp2thr` writes
  `#pragma weak ps_get_thread_area` in a case, applies to the file-scope
  name, as GCC and clang apply it: the lexer moves it to the end of the
  unit. `tests/c/prog/pragma-weak-body.c` against filcc. (clang ignores
  a `#pragma weak` that follows a definition; nanofil, at any scope,
  makes the definition weak. glibc does not rely on either.)
- `_Complex float` and `_Complex double` are structs of their two
  parts (`complex_type/2`), laid out, copied, passed and returned as
  clang compiles them, which is the code of `struct { F re, im; }`:
  `__real__` and `__imag__` are their members, lvalues too; `1.0iF` is an
  imaginary constant; a real converts to a complex with imaginary part
  +0, a complex to a real through its real part and to `_Bool` through
  both; `==`, `!=`, `+`, `-`, unary `-` and `~` (GNU's conjugate) work
  part by part, and `*` and `/` with one real operand, which stays real
  (Annex G.5.1: `z + 2` keeps `z`'s `-0` imaginary part); a complex
  initializes as a scalar does, so `{ 1, 2.0i }` fills two elements.
  Refused: a product or quotient of two complex values (decision 11),
  `_Complex long double` returns (decision 10), integer complex types
  and static complex initializers, which glibc does not use.
  `tests/c/prog/complex.c` against clang, with `lib/complex.c` across the
  call boundary (`long double` complex arguments included); four reject
  tests. 50 of the 72 complex units compile.
- A label defined twice in a function is the C diagnostic "redefinition
  of label" at the second definition, as clang's, not an internal
  `domain_error`. `tests/c/reject/label-redefined.c`.
- `__builtin_ia32_rdtsc` is `asm_fixed(rdtsc)`, edx:eax as one
  `unsigned long long`, and `__builtin_ia32_cvtpd2ps` rounds two
  doubles to float and zeroes the upper two elements.
  `tests/c/prog/ia32-rdtsc-cvt.c` against filcc, a tie included.
- An `address_space` type is refused only where it is used, as a
  vector type is: filcc cannot compile an access through another
  address space either, and glibc's `rseq-internal.h` casts to
  `address_space(257)` only in a static inline function that
  `dl-support` and its neighbours never call.
  `tests/c/prog/address-space-unused.c`, `tests/c/reject/address-space.c`.
- `__int128_t` and `__uint128_t`, clang's predefined typedefs, are
  `__int128`, which nanofil refuses where it is used, and
  `__BITINT_MAXWIDTH__` is not defined, as `__SIZEOF_INT128__` is not:
  nanofil has no `_BitInt`, and glibc's `math_uint128.h` takes its
  portable path. `tests/c/prog/int128-portable.c`.
- A `.filc_alias` that names an existing alias of the same symbol, with
  the same weakness, is that alias, as FilPizlonator coalesces them:
  glibc's versioned functions (`pthread_rwlock_rdlock`) write both a C
  alias and the directive. `tests/c/prog/filc-asm.c`.
- The `.filc_*` module asm directives, which glibc's `hidden_proto`,
  `hidden_def` and alias macros expand to: `.filc_rename name,
  __GI_name` renames a symbol everywhere, `.filc_alias` and
  `.filc_weak_alias` define an alias (replacing a declaration of the
  same name), and `.filc_weak` and `.filc_globl` set linkage. They are
  applied in source order, as FilPizlonator's `compileModuleAsm` does,
  and an offset other than `+ 0` is refused. `tests/c/prog/filc-asm.c`
  covers them against filcc.

Every generated syscall stub now compiles: its body, a `zcall` of the
`zsys_` function on `zargs`, is ordinary IR that calls libpizlo.

## Decisions this raises

1. **Teach nanofil the `.filc_*` directives.** Done (above).
2. **`__int128`.** Settled without a layout: nanofil still refuses
   `__int128` where it is used, and glibc compiles around it.
3. **`packed` on a member.** Done (above).
4. **What the proofs trust about glibc's compiler** (above). Decided
   for now: it is [glibc-ir.md](glibc-ir.md)'s assumption G1, written
   down and decided again before Hello uses glibc's IR.
5. **The boundary itself.** Recommended: keep Campaign 4's per-function
   contracts for Hello, and treat this page's direction as a later
   campaign whose first step is "module `strlen` implements
   `strlen_contract`" for the leaf functions that reach no primitive.
6. **An alias of thread-local data.** Done (above).
7. **IR operations for `sqrt` and `trunc`.** Done (above): `sqrt` is
   an IR operation, and `trunc` is built in the frontend.
8. **x87 and MXCSR** (51 libm units, the floating-point environment).
   FilPizlonator accepts a list of x87 control instructions and treats
   `stmxcsr` and `ldmxcsr` as checked memory accesses. Recommended:
   later; the interpreter has no floating-point environment to model.
9. **`_Complex`.** Done for `float` and `double` (above); what is
   left is 10 and 11.
10. **`_Complex long double` returns** (20 libm units, the `l` variants).
   FilPizlonator returns one through the call buffer, its parts at
   offsets 128 and 144, 16 bytes each with their aux words zeroed, where
   a struct of two `long double`s takes a hidden result pointer. The
   IR's returns are at most two words (`tuple([K1, K2])`), so this is an
   IR change, a two-`x` return the Fil-C backend writes to both slots,
   with the interpreter and Rocq's validator. Its arguments, through
   memory, already match. Recommended: when libm's `l` functions matter.
11. **Multiplying or dividing two complex values** (`cpow`, `cpowf`).
   clang calls compiler-rt's `__muldc3`, `__mulsc3`, `__divdc3` and
   `__divsc3`, which in Fil-C are native code (`libyolort.a`) that IR
   cannot call. Recommended: compile compiler-rt's `muldc3.c` and its
   kin with nanofil into ordinary IR the frontend calls, or leave the two
   units out.
