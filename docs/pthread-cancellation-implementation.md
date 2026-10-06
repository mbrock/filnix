# Fil-C cancellation implementation checkpoint

The patches implement a **bounded set of deferred cancellation points** and
are currently enabled only by the experimental **staging** toolchain
(`e4427dbc5b7715b8fc079fc60c412a755f9680b9`). The ordinary Fil-C 0.686 release
(`163fae598eaf249b74065b0156f3a7e7ba8c0e5a`) does **not** apply them.
`runtime/libpizlo.nix` and `runtime/filc-glibc.nix` are the authoritative switches.
Staging has additional compiler changes; selecting it is not equivalent to
adding cancellation to the release. See [upstream updates](upstream-updates.md).

This is an experimental implementation, not complete POSIX cancellation.
Arbitrary asynchronous cancellation and unwinding out of an application signal
handler remain open. The [comparison report](pthread-cancellation.md) and
[design proposal](pthread-cancellation-design.md) explain the compatibility
choices. Three patches supply the implementation:

| Patch | Responsibility |
| --- | --- |
| `patches/libpizlo-cancellation.patch` | Atomic native thread state, private notification, x86-64 syscall gate, checked typed wrappers, result conversion and cleanup frame identities. |
| `patches/glibc-filc-cancellation.patch` | Public pthread state/cleanup behavior, selected cancellation points, cancellable NPTL waits and Fil-C forced unwind; removes the native-libgcc preflight. |
| `patches/libpizlo-cancellation-aarch64.patch` | Applied after the runtime patch on ARM64: `svc` gate, signal-context PC redirect and replacements for absent legacy Linux syscalls. |

The patches live outside `ports/patch/`; application patch refreshes do not
replace them. Runtime headers installed by libpizlo feed later compiler stages.
Rebasing requires coherent headers, ABI and signal-number review. Changes to
these semantics or adoption into the release require the compiler/runtime
soundness review specified by `AGENTS.md`, plus targeted regressions. Package
build success is not a memory-safety argument.

## Cancellation semantics and campaign failures

`pthread_cancel` requests cancellation; it does not establish that the target
has stopped. Deferred cancellation acts at cancellation points while enabled.
Disabling cancellation retains the pending request. Cleanup handlers run in
reverse registration order, followed by thread-specific-data destructors; a
join observes `PTHREAD_CANCELED` after cancellation terminates the thread.
Asynchronous cancellation permits delivery outside cancellation points, with
severe restrictions on what operations can safely be interrupted. See the
[POSIX thread-cancellation rules](https://pubs.opengroup.org/onlinepubs/9799919799/functions/V2_chap02.html#tag_16_09_05).

The latest release campaign failed at `libgcc_s.so.6661 must be installed for
pthread_cancel to work`: PipeWire's loop cancellation test and LTTng-UST's
shutdown path both reached that preflight. Eight roots depend on the failing
PipeWire and two on LTTng-UST. Installing native libgcc or deleting only the
preflight does not implement Fil-C cancellation. Correct delivery must preserve
capabilities, runtime thread state, syscall side effects and cleanup ordering.
The patches address those boundaries in staging; the campaign remains a release
campaign and has not silently adopted them.

Campaign cancellation itself is a separate mechanism: the native observer
records its stop/limit request, signals the isolated Nix worker, drains its event
pipe and reaps it before recording completion, escalating to SIGKILL after two
seconds. A worker being stopped is not proof that a previously dispatched remote
builder stopped, and the viewer never retries interrupted roots automatically.
This does not depend on the Fil-C pthread patches.

## State and syscall boundary

The native thread object owns one atomic cancellation word. Typed `zthread_*`
operations update enabled/type/request/exiting state; user glibc keeps its
separate TCB lifetime and setxid bookkeeping. A request is persistent. Disabling
cancellation blocks the private notification before publishing the disabled
state, so a sender that saw the old state cannot interrupt a subsequent disabled
poll. Cleanup commits disabled, deferred and exiting together. The exiting bit
prevents repeated cancellation; it does not silently override subsequent valid
state/type setter calls. A regression test changes the type while disabled in
cleanup and verifies the returned old values.

A native architecture-specific assembly helper (x86-64, with the ARM64 follow-on) owns the final pending check and actual syscall
instruction. Its end label immediately follows `syscall`/`svc`. The private signal
handler redirects a PC inside this window to a normal return carrying a separate
cancellation outcome. It never enters Fil-C cleanup or forced unwinding itself.
A notification outside the window is blocked in that interrupted context and
requeued, preserving wakeup across a nested non-cancelling signal handler.

The typed native wrapper validates capabilities before entering the gate. It
returns to Fil-C and completes output conversion before user glibc acts on the
cancellation outcome. Positive results, EOF and successful resource acquisition
are not followed by an unconditional cancellation check. Linux `close` is an
explicit exception to post-`EINTR` cancellation: once issued it returns the result
and never retries the descriptor number. Its Fil-C descriptor backing-table lock
and association update remain part of the operation.

The private native signal is 34 for this yolo-glibc baseline. User glibc reserves
32–36 and exposes `SIGRTMIN == 37`; the private notification is omitted from
application-visible masks. This numbering must be re-audited on a core rebase.

## Covered entry points

| Public operation | Native boundary / result handling |
| --- | --- |
| `read`, `write`, `readv`, `writev` | Checked buffers/iovecs; positive partial counts win. |
| `pread`, `pwrite` and their 64-bit aliases | Typed offset and buffer validation. |
| `open`, `openat` and their 64-bit aliases | Typed `openat` gate; pending requests precede creation/acquisition. |
| `close` | Checked descriptor table handling; no post-execution cancellation/retry. |
| `accept`, `accept4` | Returned descriptor and address length are preserved. |
| `sendmsg`, `recvmsg` | Checked message/iovec/control buffers; receive lengths and flags copied back before return. |
| `poll`, `epoll_wait`, `pause` | Interruptible native gates; epoll data capabilities decoded before returning. |
| `clock_nanosleep`, `nanosleep` | Native gate with glibc's positive-errno clock API convention. |
| `pthread_cond_wait` and timed/clock variants | Entry check plus cancellable futex; retain glibc's mutex reacquisition and waiter accounting. |
| `sem_wait` and timed/clock variants | Existing entry/fast-path semantics plus cancellable futex. |
| Blocking pthread join variants | Cancellable futex with cleanup of the joining-thread registration. |
| `pthread_testcancel` and cancellation state/type setters | Native authoritative state; enabled/pending async transitions act before returning. |

The table describes implementation paths, not a claim that every variant has a
separate test. The counted behavioral cases below identify the executed coverage.
Ordinary internal `zsys_*` and noncancellable libc variants retain their original
behavior. In particular, mutex acquisition is not made a cancellation point.

## Cleanup integration

The first integrated wait tests exposed an upstream assertion in `unwind.c`:
Fil-C assumed its legacy pthread cleanup list was empty. NPTL condition waits,
semaphore waits and joins still use that list.

Cleanup buffers can be on Fil-C's GC heap, so their addresses do not identify
stack position. Each legacy registration now records its owning Fil-C call-frame
identity using `zget_call_frame(1)`. The returned identity has no dereferenceable
capability. Forced unwinding runs that frame's legacy handlers before leaving it,
stops at the modern cleanup scope's saved list head, and unlinks each handler
before calling it. This preserves internal waiter cleanup, C++ destructors,
outer pthread cleanup handlers and then TSD destruction in the tested paths.

This follows glibc's compatibility-list ordering while replacing its native
stack-buffer-address test with Fil-C frame identities. See
[glibc's unwind implementation](https://github.com/bminor/glibc/blob/04e750e75b73957cf1c791535a3f4319534a52fc/nptl/unwind.c).
It does not add general legacy-cleanup support to arbitrary application
`longjmp` or cross-fiber unwinding.

## Executed checks

The historical x86-64 implementation checkpoint used core
`b6dd63481f796f8bff8502165c7dfc61091dbbd6` with both glibc forks at 2.44.
It passed:

- **200 native gate scenarios**: pending, blocked, disabled and exiting reads;
  nested signal handling; partial writes; completed-read result handling;
  pending close; descriptor reuse after close; interrupted polling.
- **13 deterministic instruction positions**: ptrace injects a request and its
  signal at every instruction from the final check through the first instruction
  after the syscall. That last position must preserve the completed read.
- **1,376 integrated Fil-C scenario runs**: 128 pause/state/signal cases each
  through C and C++, plus 28 semantic cases repeated 20 times each through C and
  C++ destructor frames. These include real blocked waits observed through
  `/proc`, cleanup ordering/state, condition mutex ownership and notification
  races, joinability after cancelled join, partial-write byte counts, pending
  file creation, pending descriptor acceptance/reception, SCM_RIGHTS copyback,
  epoll pointer capabilities and sleep cancellation.

The final Nix check outputs are
`j7wjvrc5dc69y508bgaj6f6s75a11xwx-filc-cancellation-check` and
`27am55zvngnf4ajccmr6vyq0md4vm3a2-filc-cancellation-native-check`.
These are test counts, not independent proofs of all schedules or APIs.

```sh
nix build -L .#checks.x86_64-linux.staging-cancellation-native \
  .#checks.x86_64-linux.staging-cancellation --cores 4 --max-jobs 2
```

On October 6, 2026, both current staging checks were rebuilt, rather than merely
accepted from cache, and passed. The native check executes 200 behavioral runs
and 13 ptrace instruction positions. The integrated check executes pause tests
and all 28 semantic scenarios through C and C++ at O0 and O2; each semantic
executable itself repeats its scenario 20 times. This verifies the staging
candidate, not the ordinary release, a rebase of the patches onto 0.686, ARM64,
or end-to-end success for today's PipeWire/LTTng package versions.

The six existing differential cases also ran on the historical candidate. The nested
handler finishes before cleanup; cleanup completes before the rescue write;
pending semaphore/close operations preserve the token/descriptor; disabled read
and poll remain blocked until normal input arrives. The unpatched 2.44 Filnix
baseline aborts in all six at its `libgcc_s.so.6661` preflight. Fil-C implements
forced unwind in its own runtime; the candidate removes that inappropriate
native-libgcc preflight. See the recorded
[implementation observations](pthread-cancellation-implementation-results.txt).

The shared toolchain also passed the PipeWire core profile's **48 test groups**,
SDL3's **23**, SDL2 compatibility's **13**, and WirePlumber's **52**. Installed
runtime checks verify the exact shared libc, start a private PipeWire daemon,
create/destroy a virtual sink, discover it through both SDL APIs and WirePlumber,
and shut down cleanly. CAVA produces eight silent raw-output bars and exits
through its normal signal handling. No sound hardware or host session is used.
The former private-libc wrapper and pause-only patches have been removed; the
explicit consumer feature profiles and their application patches are retained.
This does not replace the full Nixpkgs PipeWire package with the core profile.

Application check outputs:

- `64qf1smhr06v9fr1n150jxhh2zrkxf5j-pipewire-shared-libc-runtime-check`
- `6ii5qsv0c3p80gdynjhxj3kipzl29lrk-pipewire-consumers-runtime-check`
- `vz25hxn44p7624vvh7mgpr87galdidd9-cava-runtime-check`

The GnuTLS TLS/certificate/slow check derivation and ICU consumer check also
passed with the new toolchain, as did GTK3's installed Broadway runtime check
(`ymq64i8p9yg4ba512293ypxlpbw9wml5-filc-gtk3-runtime-check-x86_64-unknown-linux-gnufilc0`).
Existing GnuTLS test exclusions remain explicit
in its port; no cancellation tests were removed to obtain these results.

## Remaining work and release limits

- Asynchronous cancellation in an arbitrary computation loop is not delivered.
  Existing compiler GC poll origins are not general unwind continuations.
  Simply declaring them catchable would not create the required C++ cleanup
  paths. Async state transitions and async cancellation while in a covered wait
  are tested, but are not full asynchronous cancellation support.
- A signal handler that itself calls a cancellation point can still encounter
  Fil-C's callback/unwind restrictions. The tested nested handler deliberately
  calls no cancellation point.
- `recv`/`recvfrom`, `send`/`sendto`, `connect`, `ppoll`, `select`/`pselect`,
  `epoll_pwait`, waitpid/waitid, signal waits and other unlisted operations have
  not been wired to the new boundary. The old generic `SYSCALL_CANCEL` path's
  empty C markers do not implement a real instruction window.
- Broader buffered-I/O, process/fork, robust/PI mutex, fiber, alternate-stack and
  cancellation-versus-timeout interactions need more coverage. The covered
  tests do not establish POSIX conformance of these surrounding subsystems.
- Linux close behavior is the explicit design choice. This does not implement
  POSIX Issue 8's newer `EINTR`/`EINPROGRESS` descriptor contract.

A campaign using this checkpoint is evidence about the packages and tests it
actually runs. It is not evidence that pthread cancellation is completely solved.

## Campaign checkpoint

Campaign `3eaf2f72-7c12-4bf2-9934-9646ea9dab4d`, **Fil-C b6dd634 · shared
cancellation**, started on 2026-09-14 at source `f07cf499adf233bb7dd85ea95e1b63f63a89776a`.
It reuses the first campaign's explicit 13,772-attribute inventory and pinned
Nixpkgs, with fresh evaluation against the updated toolchain. The first
campaign remains paused with its history intact. Both cache publishers follow
the new campaign while retaining their existing destination receipts.
