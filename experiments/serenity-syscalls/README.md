# Typed syscalls for a pizlonated SerenityOS userland

This experiment tests one piece of running SerenityOS's userland under Fil-C on
Serenity's own kernel: how pizlonated code makes system calls. Serenity's
LibSystem casts every syscall argument to `uintptr_t`, which drops Fil-C
capabilities, so a pizlonated LibC cannot use it. The design under test keeps
LibC's call sites as they are and changes what `syscall(SC_foo, ...)` means
when compiling with Fil-C:

- `syscall(SC_foo, args...)` becomes a direct call of a native,
  `zsys_serenity_foo(args...)`, declared with the argument types the kernel
  declares for `sys$foo` in `Kernel/Tasks/Process.h`. The compiler checks every
  call site against the kernel, and pointers reach libpizlo with their
  capabilities.
- Each `SC_foo_params` struct in `Kernel/API/Syscall.h` is described once, field
  by field, by an X-macro `F(kind, type, name, extent, default...)`. The same
  description expands into the struct itself, into libpizlo's trusted
  marshaller for that struct, and into a layout check.
- All checking of memory happens in libpizlo. The pizlonated header only
  supplies types.

Everything here was run against SerenityOS at
[`1a00c247`](https://github.com/SerenityOS/serenity/commit/1a00c247b06730267fd6b0dc9f700a435c3e66b4)
and filnix's `filcc` (clang 20.1.8, Fil-C 0.687). Code that is not pizlonated,
such as libpizlo's core and Serenity itself, builds with Nixpkgs' clang 23.1.3,
which has Serenity's driver upstream. `./check.sh` reproduces all of it from a
fresh clone in a few minutes; most of the time goes to building libpizlo.

## What is here

| file | what it does |
|---|---|
| `gen.py` | reads Serenity's `Syscall.h` and `Process.h` and writes `generated/` |
| `generated/SyscallParams.h` | the field X-macros for all 49 params structs |
| `generated/SyscallSignatures.h` | one row per syscall, with typed and annotated arguments |
| `generated/Syscall.h.diff` | the real header rewritten to use the X-macros |
| `generated/layout_check.cpp` | static assertions that the rewrite changes no layout |
| `LibSystem/syscall.h` | upstream's header plus the Fil-C half: natives, `Native<SC_foo>`, `serenity_syscall<F>`, the `syscall` macro |
| `runtime/filc_serenity_marshal.h` | the trusted marshaller, written once over the X-macros; compiles as C and C++ |
| `runtime/marshal_check.cpp` | compiles the marshaller against Serenity's headers |
| `runtime/filc_serenity_spike.c`, `runtime/addsig.rb`, `libpizlo-spike.nix` | a libpizlo with seven `zsys_serenity_*` natives whose kernel trap is emulated with Linux calls |
| `demo/` | a pizlonated program that calls those natives as Serenity's LibC does, seven attacks, five compile-time mistakes |
| `libpizlo/libpas-serenity.patch` | platform edits that let libpizlo's core compile for Serenity |
| `libpizlo/split_zsys.py` | moves libpizlo's Linux syscall layer out of `filc_runtime.c` into its own backend file |
| `libpizlo/libpizlo-split.nix`, `libpizlo/syscall_smoke.c` | builds the split libpizlo for Linux and compares it with the stock one |
| `libpizlo/serenity-core.sh` | compiles the split core for `x86_64-pc-serenity` and sorts what it still needs |
| `toolchain/serenity-clang23.sh` | builds a Serenity cross toolchain from Nixpkgs' clang 23, then Serenity itself, and boots it in QEMU |
| `toolchain/smoke.sh` | the script the booted system runs on its serial console |
| `check.sh` | runs all of the above from a fresh clone, except the toolchain script |

## Results

### Coverage

All 158 syscalls in `ENUMERATE_SYSCALLS` have a typed `sys$` declaration in
`Process.h`, so the signature table is generated rather than written by hand.
The syscalls fall into these classes:

| class | syscalls | how the runtime handles them |
|---|---|---|
| scalars only | 50 | pass through |
| raw pointers (`read`, `write`, `fstat`, ...) | 38 | check each pointer against its extent argument |
| one params struct | 40 | generic marshaller from the field X-macro |
| variadic (`ioctl`, `fcntl`, `prctl`, `archctl`) | 4 | per-request code, as `zsys_ioctl` on Linux |
| runtime-owned | 26 | libpizlo implements them itself |

A syscall is runtime-owned when it hands the kernel code, a stack or an address
range, or when it changes state that libpizlo manages. The memory-mapping calls,
thread creation and exit, signal handlers, fork and exec, futexes and ptrace are
in this class; `RUNTIME_OWNED` in `gen.py` lists all 26 with a reason for each.
On Linux, libpizlo also implements the corresponding calls itself.

### Step 1: the X-macro in the real header

`generated/Syscall.h.diff` replaces all 49 hand-written params structs with
expansions of `SyscallParams.h`.
`layout_check.cpp` makes 465 static assertions against the unmodified header:
size, alignment, every field's offset and type, and every default member
initializer. They all hold under real Fil-C. A negative control that changes one
field type and one default fails at the expected assertions. The patched header
compiles all 29 LibC and LibCore files that make syscalls, and the kernel's
syscall fuzzer, with the same result as the original header.

### Step 2: buffer and length annotations

Raw-pointer syscalls get their extents
mechanically from `Process.h`. A byte pointer followed by a `size_t` is a buffer
bounded by that argument, `iovec` plus `int` is an iovec array, and
`getgroups`'s `size_t` before `gid_t*` is an element count. Params fields need
35 hand annotations, recorded in `gen.py`'s `FIELD_OVERRIDES`, such as
`poll`'s `fds[nfds]`, the 0x80-entry keymaps and `accept4`'s `addr` bounded by
`*addrlen`. The extent is a C expression over the runtime's copy (`p->nfds`), so
the marshaller can use it directly.

### Call sites the typed macro rejects

The typed `syscall` macro compiles 26 of the 29 LibC and LibCore files
unchanged. It rejects
three call sites, and two of them are real upstream bugs:

- `setregid()` in `LibC/unistd.cpp:800` calls `SC_setresgid` with two
  arguments. `sys$setresgid` takes three, so the kernel reads a garbage `sgid`
  from an unset register. A non-root caller gets a spurious `EPERM` unless the
  garbage is a valid gid, and root gets its saved gid set to garbage. The call
  should probably be `SC_setregid`.
- `LibC/stdlib.cpp:1167` calls `SC_getrandom` without its `flags` argument. The
  kernel ignores `flags`, so this one is harmless.
- `pthread_create` passes a four-argument entry function to `SC_create_thread`,
  whose kernel declaration says `void* (*)(void*)`. The kernel really calls the
  entry with four registers. Under Fil-C, `create_thread` is runtime-owned
  anyway.

`Tests/Kernel/fuzz-syscalls.cpp` computes syscall numbers at run time and fails
to compile, as the design intends. It and `Utilities/syscall.cpp` need the
explicit dynamic path, which this spike only declares.

### The trusted marshaller

`filc_serenity_marshal.h` expands each
field list into a function that checks the struct is readable, copies it,
reloads every pointer field with `filc_load_ptr_at` to get its capability,
checks that capability against the field's extent, and then calls the kernel
with the copy. It compiles for all 43 generic params structs against Serenity's
own headers. The other six fail to compile with a message naming the field:
`mmap`, `mremap` and `set_mmap_name` have address fields, `futex` has an atomic
word and a union whose meaning depends on the op, `create_thread` has code,
stack and TLS pointers, and `ptrace` has addresses in another process.

### Running under Fil-C

With the spike libpizlo, the demo's well-formed calls work:
`getpid`, `readlink` (string plus out-buffer), `stat` (out-pointer),
`open` + `read`, an `ENOENT` returned Serenity-style as `-2`, and `getsockname`
(in/out `addrlen`). Each of the seven attacks ends in a Fil-C safety error
inside the `zsys_serenity_*` native:

| attack | stopped in | error |
|---|---|---|
| `StringArgument` length 4096 on a 15-byte string | `zsys_serenity_open` | cannot read 4096 bytes when upper - ptr = 16 |
| `StringArgument` pointing at freed memory | `zsys_serenity_open` | cannot read pointer to free object |
| `MutableBufferArgument` size 4096 on 16 bytes | `zsys_serenity_readlink` | cannot write 4096 bytes |
| `statbuf` pointing at 16 bytes | `zsys_serenity_stat` | cannot write 144 bytes |
| params pointer rebuilt from an integer | `zsys_serenity_open` | cannot read pointer with null object |
| `addrlen` 4096 with a 16-byte `addr` | `zsys_serenity_getsockname` | cannot write 4096 bytes |
| `write` length 4096 on 16 bytes | `zsys_serenity_write` | cannot read 4096 bytes |

These are the known gap from the prototype, raw buffer arguments, now closed for
`write` and `read`.

The five compile-time mistakes are all rejected at the call site: the wrong
params struct, a missing length argument, a syscall number that is not a
constant, an integer where the kernel takes a buffer, and a syscall with no
native.

## What the design runs into

- Checking only the length is not enough when the kernel reads it again. The
  kernel reads `*addrlen` itself, so if the runtime only checked `addr` against
  `*addrlen`, another thread could raise `*addrlen` in between. The marshaller
  therefore copies every in/out word into runtime memory, checks against the
  copy, passes the copy to the kernel and copies it back afterwards. Strings and
  string lists are copied for the same reason. Buffers bounded by a scalar the
  runtime has already copied, such as `read`'s or `poll`'s, can be passed
  through.
- Pointer fields have to be reloaded on the runtime side. Pizlonated `memcpy`
  keeps capabilities, because `zmemmove` copies each word's capability slot as
  well. The marshaller, however, copies the struct into native memory on
  libpizlo's stack, which has no capability slots, so the copy holds bare
  addresses. The runtime therefore reloads each pointer field from the
  program's struct with `filc_load_ptr_at` to get its capability. The capability
  slots alone would show which words hold pointers, but not how many bytes the
  kernel will touch through each one. That extent comes only from the field
  list, which is the main reason the X-macro has to be shared with libpizlo.
- libpizlo is C, and `Syscall.h` is C++. The descriptor parses as both only
  because C++-only types are spelled through macros (`SC_MUTABLE_BUFFER(T, S)`,
  `SC_USERSPACE(T)`, `SC_THREAD_ENTRY`). The marshaller also needs complete
  pointee types (`struct stat`, `struct pollfd`, `siginfo`), so libpizlo's
  Serenity build needs Serenity's POSIX headers. Writing the Serenity zsys layer
  in C++ would remove the macro spellings.
- Four LibC wrappers lose capabilities before the syscall. `ioctl`, `fcntl`,
  `prctl` and `archctl` read their variadic argument with
  `va_arg(ap, uintptr_t)`. That compiles, but a pointer argument has lost its
  capability by then, and no header can catch it. These four wrappers need
  `__FILC__` edits that forward the pointer, as Fil-C's glibc does with
  `zsys_ioctl`. They are the main exception to keeping call sites untouched.
- The prototype's `Signature` trait and `static_assert` are unnecessary. A plain
  call of a typed native gives the same checks with better errors. One mapping
  rule was needed: the kernel's `u8*` buffers become `void*`, because LibC
  passes `void*`.
- The function-like `syscall` macro also rewrites any later `syscall(`
  declaration, such as glibc's in `unistd.h`. Serenity's LibC headers declare
  no `syscall`, so on Serenity only code that includes LibSystem first is
  affected. The expansion has no leading `::`, so `::syscall(...)` in
  `LibCore/System.cpp` still works.
- The prototype's header-side `zcheck_readonly` is not used. Checks in the
  pizlonated header would be checks the program could skip, so the header
  carries only types.

## Step 3: keeping Fil-C's pizlonated glibc on top

libpizlo's syscall layer is `generate_pizlonated_forwarders.rb` (456 `addSig`
signatures) plus `filc_native_zsys_*` functions in `filc_runtime.c`. They check
`filc_ptr` arguments and then call yolo glibc's POSIX functions, passing flags
and structs straight through. A Serenity port can reuse that mechanism as is:
this spike adds its natives with `addSig` and an included C file.

Keeping pizlonated glibc on top and porting only the bottom does not work as a
shortcut. Pizlonated glibc compiles against Linux's ABI, and the zsys layer
passes that ABI through. Serenity's differs everywhere it matters: `O_CREAT` is
`1 << 3` on Serenity and 0100 on Linux, `struct stat` orders its fields
differently, and some errno numbers differ (`ELOOP` is 35 on Serenity and 40 on
Linux). libpizlo would also need a
Linux-to-Serenity translation of every flag and struct. On top of that,
`filc_runtime.c` includes Linux-only interfaces (epoll, eventfd, signalfd,
inotify, timerfd, personality, sys/io.h). The direct route is a pizlonated
Serenity LibC on top of `zsys_serenity_*`, where both sides share Serenity's
headers and nothing needs translating.

## libpizlo's core on Serenity

libpizlo's shared parts (the libpas allocator, the FUGC collector, capability
checks, threads and signal delivery) can stay one source for Linux and
Serenity. Only the syscall layer needs a Serenity backend, because it is shaped
like Linux.

`split_zsys.py` makes that boundary explicit. It moves all 313
`filc_native_zsys_*` functions out of `filc_runtime.c`, together with the 34
static helpers and struct types that only they use, into `filc_zsys_linux.c`.
That is 5,661 lines, and `filc_runtime.c` keeps the remaining 10,270.
`filc_runtime.c` then includes `filc_zsys_serenity.c` or `filc_zsys_linux.c` at
its end, so the moved code still sees every static it used before. On Linux the
split library builds under libpizlo's own `-W -Werror`, exports the same 318
`zsys` natives, and gives output identical to the stock library on
`syscall_smoke.c`. That program covers file I/O, fork and wait, pthreads, mmap,
poll, epoll with a pointer in its data, eventfd, signals, getrandom, clocks and
readdir. The spike's demo and attacks also behave the same on top of the split.

`libpas-serenity.patch` adds 135 lines across 9 files so the core compiles for
Serenity. The changes are:

- a `PAS_OS(SERENITY)` platform macro;
- guards around about 30 Linux-only headers;
- `memcmp` instead of `bcmp`, which Serenity's LibC lacks;
- `NSIG - 1` for the highest signal, because Serenity has no `_NSIG`;
- Serenity's highest auxv key, `AT_EXE_SIZE`;
- the kernel's `get_stack_bounds()` in place of `pthread_getattr_np`;
- `SIGCANCEL` as the one signal Serenity's LibC reserves for itself;
- a 32-bit compare-and-swap for `pthread_t`.

The last change fixes a real bug, not a warning. Serenity's `pthread_t` is an
`int`, and libpas compared and swapped it as a pointer-sized word, which would
also overwrite the next four bytes.

With the patch and an empty Serenity backend, all 178 libpizlo objects compile
for `x86_64-pc-serenity` against Serenity's LibC headers at `-O3 -W -Werror`,
and link into one shared object. It has 407 undefined symbols:

- 313 are the `zsys` natives that the Serenity backend has to provide;
- 91 are functions Serenity's LibC already implements, such as pthreads,
  signals, mmap, `dlopen` and the `long double` math functions;
- 3 are compiler-rt's CPU feature symbols (`__cpu_model` and two others).

So the core needs nothing from the lower libc that Serenity lacks. Linking it
with `--no-undefined` against the `libc.so` and `libsystem.so` that the clang 23
toolchain builds confirms this: exactly the 313 natives stay unresolved, and
nothing else. What remains is the backend itself.

## A Serenity toolchain from Nixpkgs clang 23

Serenity's `Toolchain/BuildClang.sh` builds a whole LLVM at a pinned commit of
LLVM main (24.0.0git) with six patches. Clang has had a SerenityOS driver
upstream since LLVM commit `934f795064`, which is in release 23 and not in 22,
so the cross compiler no longer needs patching. Clang 23 defines `__serenity__`
and `__unix__` for `x86_64-pc-serenity`, and links with `ld.lld` against
`/usr/lib/Loader.so`, `crt0.o` and `-lc`. Clang 20, 21 and 22 parse the triple
but know nothing else about it; for linking they fall back to `/usr/bin/gcc`.

`toolchain/serenity-clang23.sh` takes clang, lld and the LLVM tools for 23.1.3
from Nixpkgs' binary cache and lays them out as `Toolchain/Local/clang`, where
Serenity's CMake toolchain file looks. It builds only the Serenity target's
runtimes, which Nixpkgs does not have:

- compiler-rt's builtins and crt files from 23.1.3, to match the compiler;
- libunwind, libc++abi and libc++ from the LLVM commit Serenity pins, with
  Serenity's libc++ patch (0005). The patch does not apply cleanly to 23.1.3's
  locale code, and libc++ supports being built by the latest released clang.

Serenity's other five LLVM patches are not needed. Two build LLVM to run on
Serenity, one adds `/usr/local` to the driver's search paths, one enables
profiling and one is for RISC-V.

The script has to work around four things:

- Clang finds libc++ headers, runtime libraries and `ld.lld` relative to its
  own binary, which lives in the Nix store. The wrappers run clang through a
  symlink in `Toolchain/Local/clang/bin` with `-no-canonical-prefixes`, and give
  it a writable copy of its resource directory.
- Serenity's LibC links `libc++.a` into `libc.so`, so the runtimes have to be
  built with `-fPIC`; otherwise `ld.lld` rejects local-exec TLS relocations.
- Serenity's top-level `CMakeLists.txt` refuses any compiler but the exact LLVM
  commit it pins. The script edits the expected version to 23.1.3.
- The disk image script loop-mounts the image as root, and `sudo` drops `PATH`,
  so the script runs it under `sudo env PATH=...`.

The runtimes take about a minute on 16 cores. With them, Serenity builds all
6,076 targets of its default build, kernel included, without a failure. The
disk image boots headless in QEMU without KVM, in about four seconds of guest
time. In self-test mode it runs `smoke.sh`, which ran `true`, `echo`, `cat`,
`ls`, `expr`, LibJS and the AK `TestVector` and `TestString` programs, all
passing, and then shut the machine down.

Fil-C's clang is still LLVM 20 and has no Serenity target. The Fil-C parts of
the spike therefore compile with `-c` and set `__serenity__` themselves. A
Fil-C on LLVM 23 would bring the driver along; until then, a backport of
`934f795064` is the smaller change.

## Notes for the driver work (step 4)

- Fil-C's driver adds `-internal-isystem /usr/include` for its Linux target even
  with `-nostdinc`, so `check.sh` shadows `<features.h>` with an empty file. An
  `x86_64-pc-serenity` triple needs the driver to stop doing that.
- The driver already has `--filc-os-include`, `--filc-include` and
  `--filc-stdfil-include`, which a Serenity toolchain would point at Serenity's
  Kernel/API, yolo LibC and libpizlo headers.
- Serenity's userland compiles with Fil-C's clang and Fil-C's libc++ headers in
  place of glibc, given `-fno-exceptions -fno-rtti` and a generated
  `AK/Debug.h`.

## Next steps

1. Write the four variadic wrappers' `__FILC__` paths and per-request handlers
   for `ioctl` and `fcntl`, then the 26 runtime-owned syscalls, starting with
   `mmap`, `exit`, `futex`, `create_thread` and `sigaction`, which a static
   `true` needs.
2. Generate the raw-pointer natives from `SyscallSignatures.h` as the params
   natives are generated now, so that no native is written by hand except the
   runtime-owned ones. Add `zsys_serenity_dynamic`, dispatching on the same
   table and returning `ENOSYS` for unknown numbers.
3. Report the `setregid` bug upstream.
4. Write `filc_zsys_serenity.c`, starting with the natives a static `true`
   needs. Then build libpizlo with the clang 23 toolchain against a normally
   compiled Serenity LibC under a renamed library file. Its symbols keep their
   ordinary names, since the compiler already prefixes the pizlonated side with
   `pizlonated_`. Add the `x86_64-pc-serenity` triple to the filcc driver, and
   try a static `true`, `echo` and `cat` in QEMU.
