# Proposed cancellation semantics for Fil-C glibc

The recommendation is to preserve the application-facing behavior of modern
glibc, implement deferred cancellation at Fil-C's native syscall boundary, and
start cleanup only after returning to an unwind-capable Fil-C frame. A completed
operation must keep its result; an interruptible wait must not lose its wakeup.

This is a design proposal, dated September 14, 2026, following the
[comparison report](pthread-cancellation.md). It is not an implemented fix or a
claim that Fil-C passes the proposed tests. The existing results cover native
libcs; the private Filnix `pause()` fix covers a much smaller problem.

The source baseline is upstream Fil-C
[`b6dd63481f79`](https://github.com/pizlonator/fil-c/commit/b6dd63481f796f8bff8502165c7dfc61091dbbd6),
whose user glibc is 2.44. Its HEAD was rechecked during this review. Filnix's
shared 2.40 toolchain and the private PipeWire libc remain separate from this
proposal. Implementing the proposal will require runtime changes, not just a
patch to user glibc.

## The contract

Cancellation is a persistent request. The notification signal is only a way to
make the target inspect that request; consuming a signal must not consume the
request. A request becomes effective when the target commits to cancellation.

For **enabled, deferred cancellation**, use these rules:

| Situation | Proposed behavior |
| --- | --- |
| Request pending before entering a cancellation point | Cancel before doing the operation, including its successful fast path. |
| Request arrives between the final check and entering a wait | Cancel without entering a new wait. |
| Request arrives during an interruptible wait | Wake it and cancel, unless completion or a timeout wins the race. |
| The syscall returns bytes, an acquired resource, or another completed result | Finish conversion and return the result. Leave a racing request pending. |
| The syscall returns an interruption error | Apply the operation's interruption policy; `EINTR` alone does not prove cancellation is safe. |
| Execution is outside a cancellation point | Leave the request pending, including at ordinary GC poll checks. |
| An application signal handler runs without calling a cancellation point | Let it finish. Retain any wakeup needed by the interrupted wait. |

“Before doing the operation” is our stronger, predictable choice for an already
pending request. POSIX requires acting before the cancellation-point function
returns; it does not generally require rolling back all side effects. A request
that races with completion may remain pending. In particular, cancellation is
not a transaction that can undo a file creation, network effect, or consumed
input. See [POSIX cancellation][posix-cancel] and the report's
[standards discussion](pthread-cancellation.md#what-posix-requiresand-what-its-issue-numbers-mean).

The contract concerns valid API use and defined interruption behavior. Fil-C
must still enforce memory safety for invalid inputs; cancellation support must
not introduce an unchecked syscall interface.

### State changes and cleanup

- New threads start enabled and deferred. Requests remain pending while disabled.
- Re-enabling deferred cancellation leaves a pending request for the next
  cancellation point. Selecting asynchronous cancellation while enabled and
  pending, or re-enabling while asynchronous and pending, acts before the setter
  returns, matching the inspected glibc paths.
- A request made while cancellation is disabled must not itself interrupt a
  blocked `read()` or `poll()`. A notification already in flight during a state
  transition needs an explicit masking/acknowledgment protocol; ignoring it in
  a handler is insufficient for non-restarting syscalls.
- Committing cancellation sets disabled, deferred, and exiting together, then
  begins cleanup. Further requests cannot start another unwind.
- Preserve pthread cleanup callbacks in LIFO order, the existing glibc/Fil-C
  forced-unwind integration with C++ destructors, and then TSD destructors.
  The join result is `PTHREAD_CANCELED`. Ordinary `pthread_exit(value)` uses the
  same cleanup-state transition but retains `value`.

The current 2.44 port's [`__do_cancel`][filc-pthreadp] already sets disabled,
deferred, and exiting before unwinding. Preserve that behavior when changing
where cancellation state lives. The older private 2.40 implementation is not
the source of truth for these details.

Do not expose a private cancellation outcome as application `ECANCELED` or
manufactured `EINTR`. Cancellable POSIX calls terminate the thread when the
request is acted upon. They return their normal result/error when it is not.

### Which calls are cancellation points

Keep a reviewed mapping of glibc entry points to cancellable runtime operations.
Both public calls and libc's internal noncancellable variants must be covered.
It is incorrect to make every `zsys_*` call or every futex wait cancellable.
Mutex acquisition and libc's internal locking must retain their existing rules.

For compatibility, retain glibc's cancellation checks on the successful
`sem_wait()` fast path even though POSIX Issue 8 now allows a different choice.
Do the same audit for other user-space fast paths: a syscall-only fix cannot
implement all libc cancellation points.

Condition waits and joins keep their higher-level protocols. Canceling a
condition waiter must reacquire its mutex before application cleanup and must
not consume a notification that another eligible waiter should receive. A
canceled join must not consume the target's joinable result. Wiring in a
cancellable futex must preserve these rules, including timeout/signal races.

## Returning results is part of the operation

For ordinary Linux I/O, a positive partial byte count wins over a racing
deferred request. So do a returned descriptor, EOF, and other completed results.
There is no unconditional `pthread_testcancel()` after a successful syscall.

Fil-C must extend that rule through the entire return path. In the inspected
[runtime][filc-runtime], `accept()` copies back the address length after
`filc_enter()`. `recvmsg()` copies back lengths and flags after re-entry, and may
have received descriptors through `SCM_RIGHTS`. Canceling between native return
and that work can lose information or ownership even though the kernel syscall
was handled correctly.

Once the bridge chooses normal completion, it must:

1. Preserve the kernel result and errno.
2. Complete output conversion and release runtime temporary storage correctly.
3. Return through the user-libc wrapper without another deferred-cancellation
   check that discards this result.

This protection concerns internal delivery of **deferred** cancellation. It does
not promise transactional resource safety under arbitrary asynchronous
cancellation or an application handler's nonlocal jump. Composite libc calls
such as buffered I/O still need their own internal resource cleanup and reviewed
cancellation boundaries; a raw-syscall result rule does not prove them correct.

### Make `close()` an explicit exception

Choose the following Linux/glibc-oriented policy:

- Pending on entry: cancel before touching the descriptor.
- Interrupted before syscall execution: cancel before touching the descriptor.
- Once the Linux close has executed: return its result, even if a cancellation
  request is now pending. Never turn its `EINTR` into cancellation and never
  retry the descriptor number internally.

Linux [explicitly prevents restarting close][linux-close] because the descriptor
table entry has already been cleared. Another thread may already have reused
that number. Neither a second close nor cancellation cleanup may assume it
still identifies the old file.

This deliberately differs from glibc's generic post-`EINTR` cancellation path,
and resembles musl's exception for close. The generic path's own comment
[acknowledges its side-effect assumption][filc-cancellation]. Preserve Linux
error reporting for now; do not silently translate close errors as part of the
cancellation change. This does **not** claim conformance to POSIX Issue 8's
newer `EINTR`/`EINPROGRESS` descriptor-state contract, described in the
[comparison report](pthread-cancellation.md). That is a separate ABI decision.

Each additional syscall needs this same review. For example, an interrupted
`connect()` may leave a connection attempt in progress. “Cancelable interruption”
means the documented interrupted-call effects are acceptable; it must not be
used as a synonym for “nothing happened.”

## Implementation responsibilities

### One authoritative cancellation state

Put the authoritative cancellation control in the native Fil-C thread object,
accessible through typed `zthread_*` operations. User glibc implements pthread
API semantics and cleanup using those operations. Keep any retained glibc state
fields as explicitly managed ABI bookkeeping, not a second independently
writable pending/enabled/type state.

The native control needs request, enabled/type, and exiting state, plus the
current operation's cancellation context. State updates must not lose a
concurrent request. Commit-to-cancel must be a single target-side transition.
Native thread identity must remain valid while sending a wakeup; use the runtime
thread lifetime protocol rather than an unprotected saved kernel TID.

An internal delivery-inhibited scope is distinct from the application's
`PTHREAD_CANCEL_DISABLE` state. It must not change what the public setters
report. If scopes can nest through callbacks, store their nesting and restore
it on every normal and supported nonlocal exit. Fil-C already restores special
signal-deferral depth in `longjmp`; a new cancellation scope needs an equivalent
audit, including fiber switches. A stale scope must never disable cancellation
forever or refer to a dead stack frame.
Cancellation inhibition must leave GC poll checks and runtime stop/check
handshakes operational; do not overload the runtime's entered/exited state.

### A native bridge with a real instruction window

Implement a small Linux x86-64 assembly helper **inside the trusted runtime**,
after each typed wrapper has validated its arguments. Its labels must delimit
the actual final pending check and syscall instruction. The end label belongs
immediately after that instruction, before result processing.

The helper has two distinct outcomes: a normal kernel result, or an internal
instruction to cancel. The latter is separate from the Linux errno range. A
signal handler may redirect the saved PC to a helper landing point that returns
that outcome normally. It must not initiate glibc forced unwinding there.

The selected protocol must cover these paths:

| Native observation | Bridge action |
| --- | --- |
| Final check sees an enabled request | Return cancellation outcome without issuing the syscall. |
| Notification interrupts the instruction window before execution, or at a kernel restart PC | Redirect to the cancellation return path. |
| Saved PC is after the syscall | Preserve the kernel result; apply the operation's reviewed error policy on normal return. |
| PC is outside the window and an outer wait may resume | Retain/re-arm the notification; do not unwind the current callback. |

For non-restarting interruptions such as polling, the C part of the bridge also
has to classify `EINTR` using the operation policy and pending state. Positive
results and close's post-execution errors cannot go through that generic check.

The helper must be used instead of calling a native host-libc cancellation
wrapper and trying to interpret PCs inside that other libc. Host pthread
cancellation and Fil-C cancellation are separate mechanisms. Public Fil-C code
continues to use validated, typed operations, not raw syscall numbers or native
control pointers.

The empty [`__syscall_cancel_arch_start/end` C functions][filc-syscall] in the
current user-glibc port cannot implement this protocol. Their addresses do not
bound the native syscall instruction. Extending those placeholders or adding
pre/post checks around `FILC_SYSCALL` would leave the central races unresolved.

### A cancellation notification must survive nested handlers

The native notification handler needs the real `ucontext` before the ordinary
Fil-C signal trampoline discards it. Use an internal notification path with
runtime-owned signal reservation, mask handling, and lifecycle checks. Public
signal APIs must not be able to replace or permanently block that path.

Use musl's deferred mask-and-requeue protocol as the first prototype, adapting
it to return the bridge's cancellation outcome instead of calling its libc
exit routine. In the inspected [musl handler][musl-cancel], an out-of-window
notification blocks itself in the interrupted context and requeues a signal.
The outer signal return can then restore an unblocked mask and deliver it at
the resumed syscall. This is a specific mechanism to test, not evidence that
the unchanged musl code can be dropped into Fil-C.

The important nested-handler sequence is:

1. An empty-pipe read is blocked in the native helper.
2. An application signal interrupts it and its handler runs without a
   cancellation point.
3. A cancellation notification arrives inside that handler. Record/retain it;
   do not cancel the handler just because an outer read is active.
4. When the handler returns, pending cancellation is reconsidered at the
   interrupted read. It must not restart an empty wait without another wakeup.

The report observed native glibc 2.41/2.44 needing a rescue byte in this case.
That is a behavior to fix, not a compatibility requirement. An implementation
must also preserve a completed outer result if the handler interrupted the
post-syscall path instead.

Fil-C's entered/exited flag, queued `siginfo_t`, or a single `in_syscall` boolean
cannot establish which of these situations occurred. Native callbacks can
re-enter Fil-C while an outer operation is suspended. The implementation must
retain the actual interruption context and maintain its lifetime correctly.
Requeueing must not cause a signal storm; masking must not strand the next wait.
Test nested masks, deferred application-signal callbacks, and supported
`siglongjmp()` exits before claiming this protocol works in Fil-C.

### Return normally before starting cleanup

For the cancellation outcome, the runtime first restores its entered state,
finishes native-frame and temporary-root bookkeeping, and returns normally to
the typed libc bridge. That bridge commits cancellation and calls glibc's
existing forced-unwind machinery from an ordinary supported call site.

Do not run application cleanup from the native signal handler, a native syscall
frame, or an arbitrary poll check. Do not replace forced unwinding with a jump
straight to the thread entry point: that could bypass C++ destructors and libc
cleanup scopes. The existing narrow `pause()` trampoline is useful evidence
that the eventual unwind location matters; it is not the general bridge.

Normal completion, cancellation return, callback exits, and thread termination
all need balanced runtime bookkeeping. The native signal handler itself must
use only operations appropriate to that context; allocation, application
callbacks, and runtime locks are not part of the proposed notification path.

There is a further case beyond the report's non-cancellation-point handler:
an application handler can itself call a cancellation point. POSIX makes this
undefined when it interrupts async-cancel-unsafe code with cancellation pending,
but that does not make every such handler call undefined. Defined cases need
support too. The current `call_signal_handler` frame is not unwind-capable, so
returning from a nested `zsys` bridge to that handler is not enough to unwind
the complete stack safely.

Full deferred support therefore also needs a supported cancellation exit from
application callbacks, restoring native frames/masks and preserving cleanup for
the interrupted context. If interruption occurred at a compiler poll, that
context has the continuation problem discussed below. This is an explicit
remaining design/implementation gate, not something to suppress by declaring
all handlers noncancellable or jumping over their cleanup. The initial syscall
prototype can validate ordinary thread calls and handlers that do not cancel;
it must not claim to have solved cancellation from every defined handler.

## Asynchronous cancellation is a separate implementation milestone

Its intended application behavior remains glibc-compatible, including the
pending-request setter cases above and eventual cancellation of a pure compute
loop that never calls a cancellation point. The resource-delivery promises for
deferred cancellation do not make arbitrary application code async-cancel-safe.

Poll-based delivery could implement this in Fil-C, but existing GC poll checks
are not sufficient. The inspected [compiler][filc-compiler] inserts loop polls
with `getOrigin(DL)`, whose `CanCatch` defaults to false. The runtime's
`filc_pollcheck_slow()` exits and re-enters; its `forced_unwind()` requires
`can_catch` on the frames it visits. Merely setting a poll-request bit and calling
the unwinder will not supply the missing exception path and cleanup metadata.

Proper support needs compiler-generated cancellation continuations with correct
live values, exception/cleanup handling, and coverage of optimized loops. It
also needs an audit of runtime calls and state setters interrupted during
transitions. Removing the runtime assertion is not such an implementation.

Build and evaluate deferred cancellation first. Keep any interim build clearly
identified as an experimental implementation with incomplete asynchronous
support. Do not silently reinterpret `PTHREAD_CANCEL_ASYNCHRONOUS` as deferred
and describe it as a complete pthread implementation. Nor should async support
be expanded by reviving temporary asynchronous mode around ordinary syscalls.

## Acceptance criteria and implementation order

The first patch series should be an isolated runtime/user-libc pair, leaving
the campaign's shared toolchain alone. An ABI change in `zsys`/`zthread` needs a
matched pair; the existing private-libc replacement alone cannot supply it.
Keep hand-maintained changes separate from generated upstream port patches.

1. **Control and one real syscall.** Implement state transitions, notification,
   and the native helper for `read()`. Test pending-before-entry, a blocked wait,
   the check-to-sleep gap, partial/full completion, disabled cancellation, and
   the nested-handler case. Inspect disassembly of the actual built helper.
2. **Resource and conversion cases.** Add `open`/`accept`, `recvmsg`, writes,
   polling/sleeping, and close with explicit policies. Verify native-to-Fil-C
   result delivery under injected cancellation before adding more wrappers.
3. **Thread-library waits.** Wire cancellable futex paths separately from
   noncancellable paths; validate condition wait, join, and semaphore protocols.
   Audit the remaining mandatory and glibc-selected optional cancellation points.
4. **Callback continuations and async support.** Implement supported exits from
   application signal callbacks for defined cancellation cases. Develop/test
   compiler support for async delivery as its own change. These paths need
   cleanup evidence as well as safe control transfer.
5. **Applications and promotion.** Re-run PipeWire, then a small consumer cohort.
   Promote the matched toolchain only after the applicable semantic gates pass;
   application passes alone do not discharge the callback or async requirements.

The six existing [differential cases](../tests/pthread-cancel-differential.c)
give a concrete initial oracle:

| Case | Required observation for the proposal |
| --- | --- |
| 0: nested handler during read | Handler finishes; cleanup is not inside it; cancellation occurs before rescue, without the read returning. |
| 1: pending before available semaphore | No token acquired; operation does not return. |
| 2: pending before close | Descriptor remains open; operation does not return. |
| 3: pending before enabling async | Setter does not return; cleanup runs once. This needs explicit support even in a deferred-first prototype claiming this case. |
| 4/5: cancellation disabled during read/poll | No return, cleanup, or cancellation-induced `EINTR` before rescue. Re-enable deferred, then explicit testcancel cancels. |

These cases alone cannot establish correctness. Add the following gates:

| Gate | Evidence required |
| --- | --- |
| Completion and partial I/O | Bytes observed by the peer agree with returned counts; cancellation never hides a successful count. |
| Descriptor ownership | Under accept/open races, every acquired descriptor is returned or handled by a proven libc cleanup path; none are silently lost. Test descriptor zero too. |
| Fil-C copy-back | Race after native success in accept/recvmsg; address lengths, message flags, ancillary descriptors, result, and errno reach the caller consistently. |
| Close and descriptor reuse | Cancellation before execution leaves the original fd alone; cancellation after execution never closes a replacement using its number. Exercise the interruption-error path. |
| Condition wait and join | Cleanup sees the mutex owned; notifications are not stolen; a canceled join leaves the target joinable. Include timeout races and multiple waiters. |
| Cleanup state and C++ | Callbacks/destructors run exactly once, then TSD; cleanup starts disabled/deferred; repeated cancel requests do not recurse. |
| Nested signals and nonlocal exits | No cancellation of a handler that calls no cancellation point; no stranded request, stale scope, or leaked private mask after supported handler exits. |
| Cancellation inside a handler | Exercise defined handler cancellation-point calls over async-cancel-safe interrupted code, including a compiler poll context; preserve handler and interrupted-context cleanup through the native callback boundary. |
| API boundaries | Mandatory and selected optional fast paths cancel; noncancellable internal calls and ordinary deferred-mode poll checks do not. |
| Asynchronous compute | Cancel a call-free optimized loop through supported continuations, with correct cleanup and no unsupported-frame trap. |
| Runtime lifetime | Cancellation races with creation/exit/join and GC without targeting a reused TID, retaining dead roots, or corrupting frame state. |

Use controlled scheduling/injection at the final check, syscall return, and
copy-back stages, plus stress runs. Tests of a real interrupted close may need
a suitable blocking device/filesystem or a separate native harness; pretending
`close()` returned `EINTR` without actually releasing the fd does not test its
ownership semantics. Test hooks must not accidentally remove the instruction
window being tested.

The report's bounded rescue-based observations remain useful regression tests,
but timing out without a rescue is not a liveness proof. Record the source
revision, compiler, runtime/libc pair, kernel, and observation fields for every
run. A final `PTHREAD_CANCELED` after a rescue and explicit testcancel is not
evidence that the original wait was cancellable.

## Source checks made for this proposal

Alongside the existing report and its 600 native executions, this review read
the current upstream source directly. No new Fil-C runtime was built or tested
for this document.

| Source | Consequence |
| --- | --- |
| `filc_runtime.c`: `signal_pizlonator`, `call_signal_handler` | Native context is discarded; the Fil-C callback receives null context. Classify cancellation before this boundary. |
| `filc_runtime.h`: `FILC_SYSCALL`; `filc_runtime.c`: accept/recvmsg wrappers | Native host calls, re-entry, and output conversion are distinct stages. The cancellation bridge must cover them deliberately. |
| `filc_runtime.c`: `forced_unwind`, `filc_pollcheck_slow`; `FilPizlonator.cpp`: loop poll insertion | Existing loop poll sites are not forced-unwind continuations. Async delivery needs compiler work. |
| User glibc `read.c`, `close.c`, `futex-internal.c` | Several operations bypass ordinary glibc cancellation; cancelable/noncancelable futex paths currently converge. A libc-version bump does not wire them up. |
| User glibc `pthreadP.h`, `pthread_setcancelstate.c`, `pthread_setcanceltype.c` | Preserve existing cleanup-state and pending-async setter behavior when moving control into the runtime. |
| User glibc `syscall_cancel.c`, `nptl/cancellation.c` | Empty C markers do not create a native PC window; generic EINTR handling needs per-operation review. |
| musl `pthread_cancel.c`; Linux `fs/open.c` | Concrete starting points for deferred re-notification and the close exception, respectively. |

The native-source links below are pinned to the inspected revisions. Exact
comparison versions and the distinction between tested and source-only findings
remain in the [research notes](pthread-cancellation-notes.md).

[posix-cancel]: https://pubs.opengroup.org/onlinepubs/9799919799.2024edition/functions/V2_chap02.html#tag_16_09_05
[filc-runtime]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/libpas/src/libpas/filc_runtime.c
[filc-compiler]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp
[filc-pthreadp]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/projects/user-glibc-2.44/sysdeps/nptl/pthreadP.h
[filc-syscall]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/projects/user-glibc-2.44/sysdeps/unix/sysv/linux/syscall_cancel.c
[filc-cancellation]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/projects/user-glibc-2.44/nptl/cancellation.c
[musl-cancel]: https://github.com/ifduyue/musl/blob/5e9972eaef08ccf55dabe254ac829a30329793d3/src/thread/pthread_cancel.c
[linux-close]: https://github.com/torvalds/linux/blob/v6.1/fs/open.c#L1437-L1448
