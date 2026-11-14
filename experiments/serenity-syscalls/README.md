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
and filnix's `filcc` (clang 20.1.8, Fil-C 0.687). `./check.sh` reproduces all of
it from a fresh clone in a few minutes; most of the time goes to building
libpizlo.

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
| `check.sh` | runs all of the above from a fresh clone |

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
4. Build libpizlo against Serenity's Kernel/API and a yolo Serenity LibC with
   prefixed symbols, add the `x86_64-pc-serenity` triple to the filcc driver,
   and try a static `true`, `echo` and `cat` in QEMU.
