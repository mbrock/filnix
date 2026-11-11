# libnanofil (`nanofil/anf/lib/`)

libnanofil is nanofil's Gallina backend as a Fil-C shared library. It
is the in-process half of milestone M4 of
[lambda-anf.md](../../docs/lambda-anf.md). The library holds the
program that [../backend](../backend/README.md) builds as a command,
which reads IR text and compiles it with the backend's three compilers.
CertiRocq compiles that Gallina to λANF,
[AnfLower.v](../lower/AnfLower.v) lowers it to nanofil IR, and
`nanofil-backend compile-allocated` compiles the IR to a Fil-C program
over the arena of [nanofil/anf](../). A Fil-C program links the
library, hands it the IR text of a module and gets back the assembly
that `nanofil-backend COMMAND FILE.ir` would print, without starting a
process.

## The interface

[nanofil.h](nanofil.h) declares one function:

```c
int nanofil_compile_ir(int command, const char *ir, size_t ir_len,
                       char **out, size_t *out_len);
```

The command is `NANOFIL_COMPILE`, `NANOFIL_COMPILE_PROMOTED` or
`NANOFIL_COMPILE_ALLOCATED`. The function returns the status that
`nanofil-backend` exits with: 0 when `*out` holds the assembly, 1 when
the module is refused or the text cannot be read, and 3 when the module
is outside the compiler. It returns -1 when the arena or the output
cannot be allocated, and then `*out` is NULL. For statuses 1 and 3,
`*out` holds the reason without the `nanofil-backend: ` prefix that the
command prints. The command also prints the lines it compiled before it
refused the module, but the library leaves them out. A NUL byte follows
the text, and the caller frees it with `free()`.

The shared object exports this function and nothing else. Fil-C's
linker reads the names in a version script as C names, so
`{ global: nanofil_*; local: *; };` exports exactly
`pizlonated_nanofil_compile_ir`.

## The arena's lifetime

The library follows the decision of M1 in
[lambda-anf.md](../../docs/lambda-anf.md): it keeps one arena for the
whole process and resets it between uses instead of making one per
call. The first call makes the arena and runs the program's entry
`anf_main`, which gives the closure of `Drive.v`'s `run`. That call then
collects once with the closure as a root, so the closure moves to the
major heap, and it records the length of the major heap as the mark.

Every call starts by rewinding to that mark with `anf_arena_rewind`
(new in [../anf_arena.c](../anf_arena.c)). The rewind empties the
nursery and cuts the major heap back to the entry's constants and the
closure. When the major heap has grown more than `ANF_RELEASE` words
past the mark (2^22 words, 16 MiB, by default), the rewind also gives
those pages back to the kernel with `MADV_DONTNEED`. The call then
copies the text into the arena as pieces of 1 MB, applies `run` to the
command and the pieces, and copies each chunk of the stream into one
malloc'd buffer. A mutex serializes the calls, so any thread may call
the library, but only one compiles at a time.

`ANF_SLAB`, `ANF_NURSERY` and `ANF_ROOTS` size the arena as they do
for `driver.c`.

## Files

- `nanofil.h` declares the interface.
- `libnanofil.c` keeps the arena and the mutex and calls `run`.
- `test_lib.c` is the gate's driver. It loads the library with the
  fixtures and compiles each of them with all three commands, in rounds
  that alternate their order. `--time N FILE COMMAND` times the first
  compile and the best of N after it.
- `run.sh` is the gate.

## Running the gate

The gate is a Nix check that runs only when someone asks for it. It
builds CertiRocq and compiles the lowered backend, which takes about 5
minutes and 1.4 GB, so no workflow runs it:

```sh
nix build -L .#checks.x86_64-linux.nanofil-anf-lib
```

It also runs by hand from the repository's root, as the gate of
[../backend](../backend/README.md) does. The script reuses a
`backend.s` that is already in `ANF_WORK`:

```sh
nix build -o /tmp/filcc .#filcc-staging
nix-shell nanofil/anf/lower/shell.nix --run \
  'python3 nanofil/tests/watch.py --label lib-gate --timeout 5400 -- nanofil/anf/lib/run.sh'
```

The gate compiles every IR fixture of `tests/filc` and
`rocq/backend/tests` with the three commands, three times over in one
process and one arena. Each compile must return the status that the
OCaml build of `nanofil-backend` exits with and give the same reason.
When the status is 0, the output must be the same assembly. The gate
runs once with the default nursery and once with a nursery of 4,096
words under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`.
`ANF_BENCH="rx.ir lvm.ir"` also times those files.

## Results

All 477 compiles (53 fixtures, three commands, three rounds) give what
`nanofil-backend` gives, with both nurseries. To check that the gate
can fail, a rewind to word 1 instead of the mark was planted. It still
passed with the default nursery but trapped with the small one, so the
small nursery is the mode that catches an arena bug.

On rx.ir (PCRE2 10.49 compiled to IR, 367 KB), `compile` takes 0.90 s
in the library and `compile-allocated` takes 1.22 s, which is 1.37 s on
the first call. For the 36
regular expressions of
[experiments/regex-nanofil](../../../experiments/regex-nanofil), each
compiled alone to between 3 and 26 KB of IR, `compile-allocated` takes
from 7 to 124 ms per pattern in the library once it is warm. A new
OCaml `nanofil-backend` process takes from 7 to 48 ms for the same
pattern, so the library is between 1 and 2.6 times slower.

## The stack

The lowered program recurses as deeply as the Gallina does. The
fixtures run on the usual 8 MB stack. rx.ir overflows a stack of
512 KB and runs on 1 MB. Fil-C's `zthread_create2` calls
`pthread_create` without attributes, so `pthread_attr_setstacksize` has
no effect: a thread's stack follows `ulimit -s`, and a caller that
compiles large modules on a thread must raise that limit before the
thread starts.
