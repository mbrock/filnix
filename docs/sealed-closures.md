# Sealed closures

> **Status:** proof of concept, **staging toolchain only**
> (`pkgsFilcStaging`, `filcc-staging`). It is two patches that only
> staging applies: a runtime patch,
> [`patches/fil-c/sealed-closures.patch`](../patches/fil-c/sealed-closures.patch)
> (`runtime/libpizlo.nix`), and a compiler patch,
> [`patches/fil-c/noinline-callee-users.patch`](../patches/fil-c/noinline-callee-users.patch)
> (`compiler/filc0.nix`). Neither is in upstream Fil-C, and the release
> toolchain has neither.

## The question

Can a Fil-C program hand out a callable interface without handing out the
state behind it? The goal is to load several Fil-C code chunks into one
address space, have them call each other through closures, and share
ordinary objects freely, while none of them can inspect another's private
state.

Upstream Fil-C has closures, but no seal:

```c
void* zclosure_new(void* function, void* data);
void* zclosure_get_data(void* closure);             // any caller
void  zclosure_set_data(void* closure, void* data); // any caller
void* zcallee_closure_data(void);                   // the running body
```

`zclosure_get_data` and `zclosure_set_data` check only that their argument
is a closure. Whoever holds a closure pointer can read its data, swap it,
or make a new closure of the same code with other data
(`zclosure_new(closure, forged)` copies the code, not the data). So a
closure hides nothing from its callers.

## The API

```c
void* zclosure_new_sealed(void* function, void* data);
```

A sealed closure is called like any closure, and its body reads its data
with `zcallee_closure_data()` as usual. Everything else that would reach
the data through the closure is a Fil-C safety error:

| Operation on a sealed closure | Result |
| --- | --- |
| call it | runs; the body sees its data |
| `zcallee_closure_data()` in the body | the data |
| `zclosure_get_data(c)`, also `zclosure_get_data(zcallee())` in the body | panic: `closure ... is sealed` |
| `zclosure_set_data(c, d)` | panic: `closure ... is sealed` |
| `zclosure_new(c, d)`, `zclosure_new_sealed(c, d)` | panic: `cannot make a closure from sealed closure` |
| read memory through `(int*)c` | panic: function objects have no readable bytes |

The seal is set when the closure is created and cannot be removed. Ordinary
closures behave exactly as before. You can seal an existing ordinary
closure by wrapping it: `zclosure_new_sealed(open, data)` makes a sealed
closure that runs `open`'s code with `data`.

## Example: a counter nobody else can read

```c
#include <stdfil.h>
#include <stdlib.h>

struct counter { long count; };

static long bump(long by)   /* static: only this file can name it */
{
    struct counter* c = zcallee_closure_data();
    return c->count += by;
}

long (*make_counter(void))(long)
{
    return zclosure_new_sealed(bump, calloc(1, sizeof(struct counter)));
}
```

Another module that receives `make_counter()`'s result can call it as
often as it likes. It cannot read `count`, set it, or point `bump` at a
`struct counter` of its own.

## How it works

A closure is a Fil-C function object whose payload is a `filc_closure`:

```text
offset  0  fast_entrypoint      \
offset  8  generic_entrypoint    > filc_function, copied from the function
offset 16  signature            /
offset 24  closure_flags        <- was padding; now holds FILC_CLOSURE_FLAG_SEALED
offset 32  data_ptr             (a flight pointer: address and capability)
```

Plain functions are readonly function objects. A function object that is
not readonly is a closure, and the runtime and the compiler both use that
flag to recognize closures. The compiler's `filc_closure` type already left
the word at offset 24 as padding so that `data_ptr` is 16-byte aligned.
The patch names that word `closure_flags`. `zclosure_new` writes 0 there and
`zclosure_new_sealed` writes the seal; `data_ptr` stays at offset 32, which
a runtime assertion now checks. Closures are only created in
`closure_new`, so the word is always initialized. It is written before the
closure pointer is returned and never changes afterwards.

- `zclosure_get_data` and `zclosure_set_data` refuse a closure whose flag
  is set.
- `closure_new` refuses to copy the code of a sealed closure, so its
  function cannot be rebound to forged data.
- The compiler lowers `zcallee_closure_data()` inline: it checks that the
  callee is a closure and loads `data_ptr` from the closure it was called
  through. It never looks at the flag, so a sealed body pays nothing
  extra to read its data. Only the running body reaches that path, because
  the callee is whatever the current function was called through.

That last point needed a compiler change. The inliner runs before
FilPizlonator lowers `zcallee_closure_data()`, so a body called directly
from another function could be inlined into it, and the read would then
use *that* function's callee. If that function was reachable (exported,
say), anyone could run `zclosure_new(that_function, forged)()` and the
sealed body's code would run on forged data, without touching the sealed
closure. On unpatched staging the `inline` probe below prints `LEAK 7` at
`-O2`. The compiler patch adds a pass at the start of the Fil-C pipeline
that marks every function calling `zcallee()` or `zcallee_closure_data()`
`noinline` (dropping `always_inline`). A direct call then goes through the
callee's own readonly function object, and the read panics with "not a
closure". Upstream's own `zcalleedirect` tests mark their functions
`noinline` for the same reason.

Nothing else can read a function object's payload: function objects have
no size, so every load or store through a function pointer fails its
bounds check. Pointers cannot be forged from integers. The GC marks
`data_ptr` as before and ignores the flag.

## What the seal does not do

The seal protects one path: from a closure pointer to its data. A module
that relies on it for isolation must keep the other paths closed itself:

- **The data must stay private.** If any other pointer to the data
  escapes (returned, stored in a shared object, or passed to a callback),
  the holder of that pointer has full access. Sealing hides the data from
  the closure's callers, not from everyone.
- **The function must stay private.** If other code can name `bump`
  (because it is not `static`, or is reachable through `dlsym` or an
  exported pointer), it can call `zclosure_new(bump, forged)` and run
  `bump` on data of its choosing. Keep body functions `static` or hidden.
  In C++, inline functions, templates and lambdas' `operator()` have
  linkonce linkage that another library can name; use `static` or an
  anonymous namespace. An unsealed closure of the body that the module
  itself hands out has the same effect.
- **The body must protect its own invariants.** Callers can re-enter it
  from callbacks it makes, from signal handlers or several threads, or cut
  it off midway with `longjmp`, exceptions or fiber switches.
- **The body can still leak.** `zcallee()` inside the body returns the
  sealed closure itself, which is harmless, but if the body returns or
  stores its data, the data is gone.
- **It is not a process sandbox.** All chunks share syscalls, file
  descriptors, threads, signals, `exit`, and the GC. Staging refuses only
  writable opens of `/proc/<pid>/mem`, and that check can be raced (see the
  JIT cache discussion in [upstream-updates.md](upstream-updates.md)), so
  code that can call the operating system may read the process's memory
  around the language's guarantees. A chunk that must not be able to do that needs a
  syscall-level restriction (seccomp, or a runtime that refuses those
  opens) in addition to sealing.
- **Exported globals are reachable.** Non-`static` globals can be named
  with `extern` or found with `dlsym`, sealed closures or not.
- **Every chunk must be ordinary Fil-C.** One chunk built with
  `-yolo-assembler` (`zunsafe_call`) or native assembly breaks the
  guarantee for all of them. Whole-program LTO across chunks is untested.
- **Small facts still show.** `zis_readonly(f)` tells a closure from a
  plain function, and panic messages print the closure's address. Neither
  gives a pointer to the data.

Within those limits, Fil-C's existing guarantees do the rest: pointers
cannot be forged or carried out of bounds, so a chunk can only reach
objects it was given a pointer to.

## The pattern for mutually distrusting chunks

1. Each chunk keeps its state in `static` storage or in objects only it
   points to.
2. It exports sealed closures over that state, built from `static`
   functions.
3. Objects meant to be shared are passed as ordinary pointers and used
   directly by both sides.
4. Per-instance handles can be sealed closures (as in the counter) or
   integers from a private `zexact_ptrtable`, which only the owner can
   decode.

## Tests

`checks.x86_64-linux.staging-sealed-closures`
([`tests/sealed-closures.nix`](../tests/sealed-closures.nix)) builds two
programs at `-O0` and `-O2` with the staging toolchain:

- [`sealed.c`](../tests/sealed-closures/sealed.c): sealed counters keep
  separate state across 1000 calls and repeated GC cycles; a sealed body's
  `zcallee()` is itself; ordinary closures can still be read, written and
  rebound; and sealing an ordinary closure by wrapping it works.
- [`probe.c`](../tests/sealed-closures/probe.c): one mode per way to reach
  the data (`get`, `set`, `rebind`, `rebind-sealed`, `get-self`, `read`,
  `inline` for an exported function that calls the body directly, and
  `plain` for a plain function). Each must end with a Fil-C safety
  error carrying the expected message, without printing `LEAK`.

```sh
nix build -L .#checks.x86_64-linux.staging-sealed-closures
```

## Upstreaming

The runtime change is small (one new entry point, two checks, a header
comment) and breaks no ABI: existing closures get a zero flag word where
they had padding. The compiler change is a short module pass; it also
changes what an inlined `zcallee()` returns in ordinary programs, which
was arguably wrong before. Both were reviewed for soundness; the review
found the inlining bypass, and found no path through calls from runtime
APIs (signals, threads, fibers, `zcall`, unwinding), `dlsym`, GC marking
or reads of the function object. It suggested also restricting
`filc_allocate_special_with_existing_payload` to DL handles, so no other
path can make a non-readonly function object whose flag word is
uninitialized. Upstream would also want a test in
`filc/tests` per probe mode, matching the existing `closure*` tests, and
`zclosure_new_sealed` added next to `zclosure_new` in FilPizlonator's list
of runtime functions known to return. Without it, calls are only optimized
less.
