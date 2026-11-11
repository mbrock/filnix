# libnanofil (`nanofil/anf/lib/`)

libnanofil is nanofil's Gallina backend as a Fil-C shared library, and
it is the in-process half of milestone M4 of
[lambda-anf.md](../../docs/lambda-anf.md). A Fil-C program links it,
hands it a module of IR text or the bytecode of a PCRE2 pattern, and
gets back assembly or a shared object without starting a process. The
program can then load that shared object into itself.

The library holds the program that [../backend](../backend/README.md)
builds as a command. That program reads IR text, compiles it with the
backend's three compilers, and assembles and links the result. It also
turns a pattern's bytecode into IR with the regex compiler of
[../rx](../rx/Rx.v). CertiRocq compiles this Gallina to λANF,
AnfLower.v lowers that to nanofil IR, and `nanofil-backend
compile-allocated` compiles the IR to a Fil-C program over the arena
of [nanofil/anf](../).

## The interface

[nanofil.h](nanofil.h) declares three functions:

```c
int nanofil_compile_ir(int command, const char *ir, size_t ir_len,
                       char **out, size_t *out_len);
int nanofil_compile_regex(const char *terms, size_t terms_len,
                          char **out, size_t *out_len);
void *nanofil_load(const void *image, size_t len);
```

The command is `NANOFIL_COMPILE`, `NANOFIL_COMPILE_PROMOTED` or
`NANOFIL_COMPILE_ALLOCATED` for assembly text, or
`NANOFIL_SHARED_ALLOCATED` for the bytes of a shared object. For a
shared object, the library assembles the lines of `compile-allocated`
with [Encode.v](../../rocq/backend/Encode.v) and links them with
[Elf.v](../../rocq/backend/Elf.v), as `nanofil-backend shared-allocated`
does. `NANOFIL_OBJECT_ALLOCATED` gives the object as the gate's text.
The function returns the status that
`nanofil-backend` exits with: 0 when `*out` holds the output, 1 when
the module is refused or the text cannot be read, and 3 when the module
is outside the compiler. It returns -1 when the arena or the output
cannot be allocated, and then `*out` is NULL. For statuses 1 and 3,
`*out` holds the reason without the `nanofil-backend: ` prefix that the
command prints. The command also prints the lines it compiled before it
refused the module, but the library leaves them out. A NUL byte follows
the text, and the caller frees it with `free()`.

`nanofil_compile_regex` compiles regular expressions. A program gives
it what `pcre2_compile` made of its patterns, as
[pcre2_rx_terms.h](../../../experiments/regex-nanofil/pcre2_rx_terms.h)
writes it: the names of PCRE2's opcodes and the bytecode of each
pattern. The library turns each pattern into one IR function,
`rx_NAME`, with [Rx.v](../rx/Rx.v), the Gallina port of rx.pl. It
compiles the module of those functions with `compile-allocated` and
assembles and links it. The result is the shared object that rxc makes
with rx.pl, `nanofil-backend`, `as` and `ld`, made without leaving the
process.

The call returns 1 when rx.pl would not compile a pattern,
and `*out` is then the comment that rx.pl prints, such as
`% m: unsupported: 'Ref'`. It also returns 1 when the terms cannot be
read and when a function has more than 620 blocks. A compile's time
grows faster than the function: up to 609 blocks the functions of
PCRE2's tests take at most 5 seconds, and the next ones, of 830 to
1,029 blocks, take 6 to 13 seconds. So a larger pattern is left to
PCRE2's interpreter, as rxc leaves a pattern that takes more than 10
seconds.

`nanofil_load` writes a shared object to an anonymous file made by
`memfd_create` and opens it with `dlopen(RTLD_NOW | RTLD_LOCAL)` by a
`/proc/self/fd` path. No file is written to disk, and the mapping keeps
the anonymous file alive once its descriptor is closed. The caller
looks up the module's functions with `dlsym` and closes the handle with
`dlclose`. Under Fil-C, `dlsym(h, "f")` finds the getter
`pizlonated_f`, as for any shared object built by filcc.

Fil-C does not unload a shared object. Its `dlclose` returns 0 and
leaves the object in place, and the runtime's sources say that
unloading would first need the collector to allocate globals. This has
two consequences. Every image that a process loads stays in memory
until the process exits, which is 13 to 140 KB for one pattern. And
`dlopen` returns an object that is already loaded when it is asked for
a name that the object has, without opening the file. A closed
descriptor's number is used again, so when a second image was opened
as `/proc/self/fd/3`, it got the first image's object. In the PCRE2
hook that ran one pattern's function on another pattern's match data,
and the function's own Fil-C bounds check stopped it. Now each image is
opened under a name that no earlier image had. The library writes the
number of the load into the directory part of the path, `/.` for a 0
bit and `//` for a 1, and the kernel reads that as `/proc/self/fd`
itself. The names run `/proc/self/fd/3`, `/proc/self/fd///3`,
`/proc/self/fd/.///3` and so on.

The loaded code is native code. Nothing at load time checks that it
came from nanofil, so the same trust holds as for any other library the
program loads. Its safety comes from the backend, which inserts and
validates the Fil-C checks of every access before it emits a line.
libnanofil adds no new way to run code: the Fil-C runtime refuses
`mmap` with `PROT_EXEC`, and `dlopen` maps a shared object as it maps
any other.

The library exports these functions and nothing else. Fil-C's
linker reads the names in a version script as C names, so
`{ global: nanofil_*; local: *; };` exports exactly the
`pizlonated_nanofil_*` getters.

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
the library, but only one compiles at a time. Each call runs on a fiber
of its own, as the last section says.

`ANF_SLAB`, `ANF_NURSERY` and `ANF_ROOTS` size the arena as they do
for `driver.c`.

## Files

- `nanofil.h` declares the interface.
- `libnanofil.c` keeps the arena and the mutex, calls `run`, and
  loads shared objects.
- `test_lib.c` is the gate's driver. It loads the library with the
  fixtures and compiles each of them with the five IR commands, in
  rounds that alternate their order. `--regex` does the same with
  files of pattern terms. `--load` loads each one's shared object,
  closes every other one, and requires a new handle for each, which
  fails when an image is given an earlier image's object.
  `--time N FILE COMMAND` times the first compile and the best of N
  after it.
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
`rocq/backend/tests` with the five IR commands, three times over in one
process and one arena. Each compile must return the status that the
OCaml build of `nanofil-backend` exits with and give the same reason.
When the status is 0, the output must be the same assembly, object
text or shared object. The regex command then compiles each file of
[../rx/tests](../rx/tests), three times over too. Its reference is what
[rxc](../../../experiments/regex-nanofil/rxc) does with the OCaml
extraction of Rx.v in rx.pl's place, which [../rx/run.sh](../rx/run.sh)
holds to rx.pl. The gate runs once with the default nursery and once
with a nursery of 4,096 words under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`.
Then `nanofil_load` loads every shared object whose imports the Fil-C
runtime defines. `ANF_BENCH="rx.ir lvm.ir"` also times those files.

## Results

All 795 compiles of the IR fixtures (53 fixtures, five commands, three
rounds) and all 57 of the regex files (19 files, three rounds) give
what their references give, with both nurseries, and the 28 shared
objects load. Each check was shown to fail on a planted bug: a rewind
to word 1 instead of the mark trapped with the small nursery, and
opening each image as `/proc/self/fd/N` made `--load` report an
earlier image's handle.

On rx.ir (PCRE2 10.49 compiled to IR, 367 KB), the library takes
0.93 s for `compile`, 1.24 s for `compile-allocated` and 1.45 s for
`shared-allocated`, whose shared object is 144 KB. rx.pl makes 1,362
functions of up to 128 blocks of PCRE2's own tests. Each was compiled
alone in a new process, where the first call also makes the arena, and
the regex command took a median of 18 ms and at most 150 ms.

## The stack

The lowered program recurses as deeply as the Gallina does.
AnfLower.v turns a tail call into a jump only within a cluster
([../lower](../lower/README.md)), so some loops over lists make a
native call per element. Two of them were rewritten to run in constant
stack: Encode.v's loop over the lines, which called itself through its
own closure because `step` was inlined into it, and Drive.v's cutting
of a shared object into parts with the stdlib's `firstn` and `map`.
Others remain. Order.v's merges cons after their recursive call and take
about 288 bytes a level. A function of 412 blocks recurses 28,968 deep
in `merge_steps` and needs between 8 and 9 MB, and one of 609 blocks
compiles on 16 MB.

A thread's stack under Fil-C is fixed by the stack limit when the
process starts. Fil-C's `zthread_create2` calls `pthread_create`
without attributes, so `pthread_attr_setstacksize` has no effect, and
a `setrlimit` in the process leaves the threads created after it at the
old size too. A thread gets `ulimit -s` of the shell that started the
process, or 2 MB when that is unlimited.

So the library runs each compile on a fiber. Fil-C's `makecontext`
allocates a stack of the size it is given, gives the fiber its own
stack limit, and the collector scans the fiber. A compile too deep for
its fiber stops with Fil-C's stack overflow error, as it would on a
thread. Each call makes its fiber under the library's mutex, because a
Fil-C fiber belongs to the thread that made it. The fiber's stack is
64 MB plus 16 bytes for each byte of the input, or `ANF_FIBER_MB`
megabytes when that is set. Fil-C's `makecontext` reads only
`uc_stack.ss_size`, so the library passes no buffer of its own. The
kernel backs only the pages a compile touches, so the size costs
address space but not time: PCRE2's tests compile in the same time on
fibers of 2, 64 and 256 MB. The runtime frees a fiber's stack when the
collector reclaims its context, so finished fibers hold address space
until the next collection. The gate runs its processes on a 512 KB
stack, on which rx.ir and the regex fixture of 412 blocks overflow
without the fiber, and they compile to the OCaml build's bytes on it.
