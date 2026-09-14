# Fil-C cancellation implementation checkpoint

This implements a **bounded set of deferred cancellation points** on Fil-C
`b6dd63481f796f8bff8502165c7dfc61091dbbd6`, with both glibc forks updated to 2.44.
It is an experimental Filnix patch, not a complete POSIX cancellation
implementation. In particular, arbitrary asynchronous cancellation and
cancellation that unwinds out of an application signal handler remain open.

The [comparison report](pthread-cancellation.md) and
[design proposal](pthread-cancellation-design.md) explain the compatibility
choices. The implementation is in two maintained patches:

- `patches/libpizlo-cancellation.patch`: native thread state, signal handling,
  typed syscall gates, result conversion and cleanup frame identities.
- `patches/glibc-filc-cancellation.patch`: pthread state and cleanup semantics,
  the selected public cancellation points and cancellable NPTL futex waits.

These patches are outside `ports/patch/`; refreshing upstream application ports
cannot overwrite them. Apply them to the core source pin, regenerate against a
clean upstream checkout when rebasing, and rerun the gates below. Runtime headers
installed by libpizlo are used by later compiler stages, so a new runtime entry
point cannot silently compile against unpatched headers.

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

A native x86-64 assembly helper owns the final pending check and actual syscall
instruction. Its end label immediately follows `syscall`. The private signal
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

On this x86-64 server, the shared candidate passed:

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
nix build -L .#checks.x86_64-linux.cancellation-native \
  .#checks.x86_64-linux.cancellation --cores 30 --max-jobs 2
nix build -L .#checks.x86_64-linux.pipewire-runtime --cores 12 --max-jobs 2
```

The six existing differential cases also ran on the candidate. The nested
handler finishes before cleanup; cleanup completes before the rescue write;
pending semaphore/close operations preserve the token/descriptor; disabled read
and poll remain blocked until normal input arrives. The unpatched 2.44 Filnix
baseline aborts in all six at its `libgcc_s.so.6661` preflight. Fil-C implements
forced unwind in its own runtime; the candidate removes that inappropriate
native-libgcc preflight. See the recorded
[implementation observations](pthread-cancellation-implementation-results.txt).

PipeWire application validation is a separate gate. Its former private-libc
wrapper and pause-only patches have been removed from the candidate tree; the
PipeWire core profile and explicit consumers now use the shared toolchain.

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
