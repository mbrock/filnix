# Proving GNU Hello Over Userland glibc

Proving that GNU Hello never panics sounds like a small exercise until you ask where the proof stops trusting the C library. If you treat glibc as a set of axioms and assume that printing, option parsing, memory allocation, locales, and process exit behave like simple textbook specifications, the main program is only a few dozen lines of glue.

In this campaign, we instead compiled Fil-C's userland glibc 2.44 into checked intermediate representation and verified the C library code down to [the runtime system-call wrappers](../rocq/glibc/zsys/OsWorld.v). Verifying real glibc code rather than an idealized specification forces the proof to account for every low-level detail of how the library actually works. The sixteen items below are concrete surprises that turned up while proving userland glibc for GNU Hello.

## Fil-C's glibc memcmp casts pointers to long int and panics at -O0

For buffers shorter than 16 bytes, `string/memcmp.c` compares one byte at a time. At 16 bytes or more, it calls static word-comparison helpers and passes both buffer pointers as `long int`. Fil-C drops a pointer's capability when the pointer crosses a function call as an integer, so casting that integer back to a word pointer and reading through it inside the helper immediately panics with a null-capability error. Stock `filcc` at `-O2` only survived because LLVM happened to inline both static helpers before lowering capabilities, whereas `filcc -O0` and `nanofil` keep the call boundary and trap on every 16-byte comparison.

Changing the parameter type from `long int` to `uintptr_t` traps the same way because the helper still rebuilds a pointer from an integer. Our [string-pointer patch](../survey/glibc/patches/filc-glibc-string-pointers.patch) gives the helpers word-pointer parameters and keeps integer alignment arithmetic inside each function. For the unpatched code, [MemcmpLogic.v](../rocq/glibc/string/MemcmpLogic.v) proves `memcmp` for lengths below 16, which suffices for GNU Hello because `set_program_name` only compares the seven-byte string `"/.libs/"`.

## strlen, strcmp, and memcmp read whole aligned 8-byte words

The word-at-a-time string functions in glibc round their input pointer down to an 8-byte boundary, load full 8-byte words through the word containing the NUL terminator, and mask off the leading bytes in registers; `memcmp` rounds an unaligned first pointer down to an 8-byte boundary the same way. A textbook byte-span string predicate is therefore false for glibc's `strlen` whenever a caller passes an unaligned interior pointer. GNU Hello does exactly that when `set_program_name` advances `argv[0]` by seven bytes past `"/.libs/"` and when `getopt_long` points `optarg` eleven bytes into `"--greeting=hi"`, causing `strlen` to read three bytes before `optarg` and up to seven slack bytes after the NUL.

Borrowing a string suffix with full ownership is also unsound when functions read whole words. Full ownership of the suffix's first 8-byte word would let a callee overwrite the caller's prefix bytes in that shared word. Every string proof instead uses the fractional 8-byte word windows defined in [WordString.v](../rocq/glibc/string/WordString.v).

## __isatty_nostatus sets errno to ENOTTY on the first buffered write

On the first buffered write to standard output, glibc allocates the stream buffer and calls `__isatty_nostatus` to decide between line buffering and an 8,192-byte block buffer. In upstream Linux glibc, `__isatty_nostatus` issues a raw inline kernel system call that never touches `errno`.

In Fil-C's userland glibc, `__isatty_nostatus` instead calls the runtime's `zsys_ioctl` wrapper with `TCGETS2` and neither saves nor restores `errno`. When standard output is redirected to a pipe or a regular file, that terminal query fails and writes `ENOTTY` into `errno`. As a result, the buffered output proof in [LibioDoAlloc.v](../rocq/glibc/libio/LibioDoAlloc.v) cannot promise that a successful write leaves `errno` unchanged.

## getopt panics if resumed after changing only optind

Our first specification for `getopt_long` in [the Hello library boundary](../rocq/glibc/hello/HelloGlibcDebts.v) required only that the public index `optind` lie between `0` and `argc`, without tying `optind` to the parser's private 56-byte state structure. That specification fails when resuming a clustered short option like `"-tg"` where `-t` takes no argument and `-g` requires one: the first call returns `'t'` with `optind` equal to `1` and leaves the private cursor pointing at `"g"`. On the second call, the scanner copies `optind` into its private state, consumes `'g'`, sees the end of the cluster, and increments its index before checking whether `'g'` needs an argument.

The scanner then tests whether the index equals `argc` rather than whether it is at least `argc`. If the caller set `optind` to `argc` between calls, the pre-increment advances the index past `argc` and reads one slot past the end of `argv`. That out-of-bounds read causes a Fil-C safety panic in `getopt.c`, which [the getopt session invariant](../rocq/glibc/getopt/GetoptState.v) rules out by tying the saved cursor to the current index. Right after our worker thread ran a small C test reproducing that panic, the model provider's safety filter stopped the thread as suspected exploit work, and a second model had to finish the proof.

## The locale-archive loader trusts offsets from the mapped file

GNU Hello calls `setlocale` at the start of `main`, which maps `/usr/lib/locale/locale-archive` into memory and parses its header tables in `locale/loadarchive.c`. Auditing the loader for the proof uncovered five bugs when the archive or category file is truncated or corrupt: the hash-table probe loop stops only when it finds an empty slot and spins forever if every slot in the table is occupied and none matches; string and record offsets from the file header are added to the mapping base and dereferenced without checking that they fit in the mapping or that strings are NUL-terminated; and the bounds check on each category record adds two 32-bit unsigned fields in 32-bit arithmetic so `0xffffff00 + 0x100` wraps to zero and passes.

A fifth bug in `locale/loadlocale.c` checks `idx > filesize` instead of `idx + 4 <= filesize` before reading a four-byte word at the end of a mapped locale file. Under Fil-C, those unchecked offsets trigger out-of-bounds capability traps, which are fixed by [the archive validation patch](../survey/glibc/patches/filc-glibc-loadarchive-validate.patch) and [the locale validation patch](../survey/glibc/patches/filc-glibc-loadlocale-validate.patch) in commit [4546ffb6](https://github.com/mbrock/filnix/commit/4546ffb60b62bba3b9d4b07e2963b4ae508b1338).

## The fatal-error path calls exit while holding stderr's lock

When GNU Hello hits an invalid option or a write failure, it calls glibc's `error` function with a nonzero status. We first assumed that a fatal error exited the process directly, but `misc/error.c` finishes by calling normal `exit` rather than `_exit`. A fatal diagnostic therefore still runs every registered `atexit` handler, including `close_stdout`, and requires the error path to carry the full exit-handler state in [HelloGlibcMainTail.v](../rocq/glibc/hello/HelloGlibcMainTail.v) and commit [61c85131](https://github.com/mbrock/filnix/commit/61c85131648ebc5bd730560b97aecaacf754825f).

Before formatting its message, `error` also disables thread cancellation by writing `1` to offset `792` of the thread descriptor and acquires `stderr`'s lock. It then calls `exit` before unlocking `stderr` or restoring the cancellation flag. Our initial cleanup proof had assumed that every stream lock is free at exit and that cancellation is zero, so [CancelState.v](../rocq/glibc/stdio/CancelState.v) proves the exact cancellation state transitions for fatal diagnostics.

## fclose dereferences NULL unless stdfiles.c's constructor runs first

Static initializers in `libio/stdfiles.c` link `_IO_list_all` through `stderr`, `stdout`, and `stdin` using each stream's forward `_chain` field at byte offset `104`, but leave every stream's backward link pointer `_prevchain` at offset `184` as `NULL`. Before `main` starts, the constructor `_IO_stdfiles_init` walks that list and sets `stdout`'s backward link to the address of `stderr._chain` at `stderr + 104`, which is an interior pointer into the middle of `stderr`'s `FILE` structure.

If `main` runs without that constructor, `close_stdout` calls `fclose`, which enters `_IO_un_link`, reads `NULL` from `_prevchain`, and dereferences it. Because `stdout`'s backward link points inside `stderr`, three separate stream predicates cannot own the three standard streams independently. [LibioStdfiles.v](../rocq/glibc/libio/LibioStdfiles.v) therefore factors the forward and backward link fields into a shared list invariant.

## The ioctl contract had its request number one digit off

Our first contract for `zsys_ioctl` converted the hexadecimal constant `TCGETS2` (`0x802C542A`) to decimal as `2150389802` instead of `2150388778`, off by `1024` in the thousands place. Caught during cold soundness review, that single wrong digit simultaneously rejected every real terminal query from `__isatty_nostatus` and trusted an unrelated ioctl request code.

The same review found a subtlety in how the Fil-C runtime wraps `ioctl`. Because the Linux `ioctl` interface does not encode how many bytes a kernel request writes, the runtime checks read access to the end of the caller's object, copies up to 128 bytes into a guard-page buffer, and copies that entire range back if any byte changed. In `__isatty_nostatus`, the 44-byte `kernel_termios` structure lives in a 48-byte rounded stack allocation, so `zsys_ioctl` can overwrite all 48 bytes as modeled in [OsIoctl.v](../rocq/glibc/zsys/OsIoctl.v).

## zmemmove and zmemset return nothing natively

Standard C `memmove` and `memset` return the destination pointer, and our first OS registry reused the standard `memmove` and `memset` contracts directly for `libpizlo`'s `zmemmove` and `zmemset`. In `filc_runtime.c`, however, both runtime functions are declared as returning `void`.

When a C program calls a `void` runtime function through a pointer-returning function pointer in native Fil-C, the runtime does not trigger a return-size panic; it silently leaves a null pointer with no capability in the return register, as tested in [zsys-mem.c](../rocq/glibc/zsys/zsys-mem.c). [OsRegistry.v](../rocq/glibc/zsys/OsRegistry.v) wraps both contracts in `void_only` so that any call site binding a return value is rejected.

## An assumed spec had a FILE field at byte 72 instead of 80

When closing a stream, glibc calls `_IO_unsave_markers` to free any saved pushback buffer or stream markers. Before verifying `_IO_unsave_markers` itself, we wrote an assumed specification for it in [LibioCloseItMid.v](../rocq/glibc/libio/LibioCloseItMid.v) that took ownership of the pointer field at byte offset `72`, which is `_IO_save_base`, alongside offset `96`, which is `_IO_markers`.

When we later stepped through the compiled instructions of `_IO_unsave_markers` in [LibioGenLeaves.v](../rocq/glibc/libio/LibioGenLeaves.v), the proof stopped on the very first load. The macro `_IO_have_backup` actually checks whether `_IO_backup_base` is non-null, and `_IO_backup_base` sits at byte offset `80` rather than `72`, which was fixed in commit [ec452b78](https://github.com/mbrock/filnix/commit/ec452b78f72c3055bf0830c6f4dee08b63d50faf).

## glibc's malloc checks a tcache before calling zgc_alloc

In Fil-C's userland glibc, `__libc_malloc2` immediately calls `zgc_alloc` and `__libc_free` immediately calls `zgc_free`. You would expect `malloc` to compile to a one-line wrapper, yet `__GI___libc_malloc` is 31 basic blocks and 195 instructions because it runs `ptmalloc`'s per-thread cache prelude before calling `__libc_malloc2`. We initially assumed `mp_.tcache_max_bytes` at offset `120` was zero in initial memory, skipping that branch, but in the actual data image it is `1041`, so every allocation up to 1,024 bytes computes a bin index and dereferences the thread-local `tcache` pointer.

That lookup only falls through to `zgc_alloc` because `tcache` starts out pointing to a read-only zeroed global structure. Because `free` returns right after calling `zgc_free`, it never populates the per-thread cache, which [the allocator proof](../rocq/glibc/stdlib/AllocLogic.v) captures as an invariant. Meanwhile, our first attempt to lower `zgc_free` to `free` in the compiler frontend turned `malloc.c`'s own definition of `free` into infinite self-recursion.

## printf's character count can wrap at 64 bits and must return EOVERFLOW

In glibc 2.44, `__printf_buffer_done` computes the total characters written by adding the 64-bit unsigned buffer offset `ptr - base` to the 64-bit unsigned counter `written`. Because `printf` returns a signed 32-bit `int`, it must set `errno` to `EOVERFLOW` (`75`) and return `-1` whenever the mathematical sum exceeds `INT_MAX` (`2^31 - 1`).

In 64-bit unsigned arithmetic, two large unsigned counts can wrap past `2^64` into a small positive 32-bit integer, so checking only the narrowed 32-bit sum would miss wrapped overflows. The compiled function in [PrintfCountBits.v](../rocq/glibc/stdio/PrintfCountBits.v) and [PrintfBufferOverflow.v](../rocq/glibc/stdio/PrintfBufferOverflow.v) pairs a 32-bit sign-extension test with a 64-bit unsigned carry check, which commit [6290c522](https://github.com/mbrock/filnix/commit/6290c522e85453c0b35c384fa26e7828aa2f2e8c) proves catches every mathematical sum of `2^31` or more.

## puts flips stdout's mode to -1 and can leave zero pending bytes

When closing a stream, glibc flushes any pending output buffer and resets the stream's state. We first proved `fclose` on standard output assuming the stream was unoriented and its heap buffer held at least one pending byte. Composing `puts` with `close_stdout` broke both assumptions, because `puts` sets the stream's mode to `-1` for narrow byte output. On a line-buffered terminal, the trailing newline also flushes the buffer immediately and leaves zero pending bytes when `fclose` runs, as proved in [LibioPutsMode.v](../rocq/glibc/libio/LibioPutsMode.v).

A second surprise hit on the error path of `puts`. A safety proof cannot assume that writing to standard output succeeds, and if `puts` returns `EOF`, `main` still exits and runs `close_stdout`. We had to trace every early-return branch in [the stream flush proof](../rocq/glibc/libio/LibioXsputnFlush.v) to show that for any non-empty string, `stdout`'s buffer is allocated before any write failure can occur.

## atexit registers a zero-argument function that exit calls with two arguments

When GNU Hello registers `close_stdout` with `atexit`, glibc forwards the zero-argument function pointer to `__cxa_atexit` with a null argument and a null dynamic-object handle, storing the entry with flavor `ef_cxa` in a 32-slot static array. During `exit`, `__run_exit_handlers` pops each `ef_cxa` entry and invokes it through an indirect call passing two arguments: the registered `void *` pointer and the 32-bit exit status.

GNU Hello's `close_stdout` takes zero parameters rather than two. The composition proof in [AtexitLogic.v](../rocq/glibc/stdlib/AtexitLogic.v) and [ExitRunLoop.v](../rocq/glibc/libio/ExitRunLoop.v) goes through only because Fil-C's function-call semantics silently drops extra arguments beyond a function's parameter list instead of trapping on argument count.

## __libc_single_threaded is 0 in the raw ELF loader image

In glibc, stream locks and cleanup paths read `__libc_single_threaded` to decide whether the process has only one thread and can skip atomic synchronization. When [HiAtexitInitial.v](../rocq/glibc/hi_atexit/HiAtexitInitial.v) computed the initial memory of the 32 linked glibc units, however, byte `73808` turned out to be `0` in the static ELF image. Glibc starts out marked multi-threaded and only flips that flag to `1` dynamically inside `__libc_early_init` after allocating the 2,560-byte thread descriptor, as modeled in [HiAtexitPrepare.v](../rocq/glibc/hi_atexit/HiAtexitPrepare.v).

Even after `__libc_single_threaded` is set to `1`, 37 functions in GNU Hello's glibc closure still execute hardware atomic compare-and-swap instructions unconditionally. Modeling `raw_cas` in commit [1bf0e00b](https://github.com/mbrock/filnix/commit/1bf0e00b) also exposed a Fil-C shadow-memory quirk: an integer compare-and-swap on a pointer slot overwrites the 8 primary address bytes while leaving the old pointer capability in shadow memory.

## iofclose.c exports fclose only via .symver, and weak aliases differ in Fil-C

Linking `hi_atexit` against `libio/iofclose.os` initially left `fclose` unresolved even though `iofclose.os` was in the link: in shared `.os` builds, `iofclose.c` defines `_IO_new_fclose`, aliases `__new_fclose` to it, and exports `fclose` solely via an inline-assembly `.symver __new_fclose, fclose@@GLIBC_2.2.5` directive that the compiler frontend had ignored.

Teaching [link.pl](../rocq/scripts/link.pl) about symbol versions and weak overrides in commit [14ea0ca5](https://github.com/mbrock/filnix/commit/14ea0ca5af8f645f40cc04d0e04877f43095585a) then uncovered an ABI difference between host ELF and Fil-C. Suppose object A defines a weak function `f` returning `11` and a strong alias `g` targeting `f`, while object B defines a strong `f` returning `23`. Calling `f` and `g` in standard `gcc` or `clang` prints `23 11`, whereas `filcc` prints `23 23` because Fil-C's alias getter for `g` jumps through the PLT to the winning strong getter for `f`.
