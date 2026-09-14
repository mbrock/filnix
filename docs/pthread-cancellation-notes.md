# Thread cancellation: research notes

This is the detailed source audit and experiment record. Start with
[Thread cancellation: what Fil-C needs to get right](pthread-cancellation.md)
for the explanation; use these notes to check a finding or reproduce the tests.

Investigated **2026-09-14**. These are research findings and recommendations,
not an implementation plan.

If an application expects glibc's thread cancellation behavior, what must Fil-C
preserve—including glibc's bugs? This document compares glibc, musl, and
Cosmopolitan, with a look at FreeBSD's thread library, libthr. It follows the
PipeWire `pause()` cancellation experiment in this repository, which handles
one narrow case rather than cancellation in general.

**glibc compatibility depends on the version.** glibc changed its Linux syscall
cancellation mechanism in 2.41. The old mechanism could cancel unrelated signal
handlers and discard successful syscall results. The new mechanism avoids those
problems, but our tests found another: a cancellation request delivered during
a signal handler can leave the thread blocked when the handler returns. musl
and Cosmopolitan handle that case, but differ from glibc in other ways.

**Upstream Fil-C has already moved to glibc 2.44.** This checkout's older 2.40
pin is not current upstream. Fil-C's 2.44 port still replaces several glibc
syscall wrappers with `zsys_*` runtime calls. We cannot assume it behaves like
the native glibc 2.44 build tested here.

Memory safety does not solve these problems by itself. A canceled thread can
still leak a file descriptor, lose track of bytes it wrote, leave a lock held,
or skip a C++ destructor—all without an invalid memory access.

Contents:

- [Scope and evidence](#scope-and-evidence)
- [POSIX requirements](#posix-defines-cancellation-points-not-general-rollback)
- [Two syscall races and how libcs handle them](#two-races-around-a-syscall)
- [What the six tests found](#what-the-six-tests-found)
- [Descriptor ownership](#close-requires-an-explicit-ownership-policy)
- [Cleanup and condition variables](#cleanup-includes-more-than-pthread-callbacks)
- [FreeBSD's kernel-assisted design](#freebsd-uses-kernel-support-to-avoid-missed-wakeups)
- [Fil-C, including the upstream 2.44 upgrade](#fil-c-must-handle-cancellation-where-it-calls-native-code)
- [Reproduction](#reproducing-the-native-comparison)
- [What still needs testing](#what-still-needs-testing)

## Scope and evidence

The document distinguishes four kinds of claims:

- **Requirement:** what a named edition of POSIX requires.
- **Observation:** what happened when we ran the test program (the "probe").
- **Source finding:** what we learned by reading a particular source version,
  without necessarily running it.
- **Interpretation or proposal:** our explanation or recommendation, rather
  than a measured result.

### Builds we tested

All measurements used native Linux x86-64 on kernel `6.1.158+`. The same six
scenarios ran 20 times against each of these five builds: **600 executions**.

| Implementation | Tested build | Execution method |
| --- | --- | --- |
| glibc | Host 2.36 | Host compiler and dynamic loader |
| glibc | Debian `libc6` 2.41-12+deb13u4, amd64 | Extracted package and its own loader/library path |
| glibc | Debian `libc6` 2.44-1, amd64 | Extracted package and its own loader/library path |
| musl | 1.2.6 | Built from release source; statically linked probe |
| Cosmopolitan | 4.0.2 cosmocc distribution | Compiled with cosmocc; run through `ape-x86_64.elf` |

The glibc comparisons used the same probe executable with different loaders;
loader `--list` output was checked to confirm the selected libc. They did not
replace the host libc. The original compiler versions and archive checksums were
not retained, so the record identifies the tested libc versions but is not
enough to reconstruct the exact builds.

The [probe source](../tests/pthread-cancel-differential.c) and
[counted output](pthread-cancellation-results.txt) are checked in. Output is
grouped using `sort | uniq -c`, not listed in time order. We did not run FreeBSD,
test C++ unwinding, or run this comparison under Fil-C.

### Source versions we read

The source versions below are not necessarily the exact sources of the tested
binaries. In particular, we did not establish that the glibc snapshot matches
the Debian 2.44 package, and we did not build the later Cosmopolitan snapshot.
The glibc discussion concerns its Linux thread implementation, NPTL, not Hurd.

| Source | Revision |
| --- | --- |
| glibc | [04e750e75b73][glibc-rev], plus the 2.40-era mechanism and its replacement |
| musl | [5e9972eaef08][musl-rev], plus the 1.2.6 release used for execution |
| Cosmopolitan | [5907304049f3][cosmo-release] (4.0.2), [5ddb5c2adad7][cosmo-initial], and relevant paths rechecked at [3293fad0a9ea][cosmo-rev] |
| FreeBSD | [44b73821d1c0][freebsd-rev] |
| Fil-C, local pin | [4867f1179f1c][filc-rev], the repository's `coreRev` at the time; glibc 2.40 trees |
| Fil-C, newer upstream | [b6dd63481f79][filc-new-rev], verified `deluge`/HEAD during the follow-up; glibc 2.44 trees, selected cancellation/runtime paths inspected |
| Filnix baseline | [32bf7f5e1e22][filnix-baseline], including the isolated cancellation patches |

## POSIX defines cancellation points, not general rollback

Cancellation has two independent settings: **state** (enabled or disabled) and
**type** (deferred or asynchronous). With deferred cancellation, a thread acts
on a request only during designated calls, known as **cancellation points**.
Asynchronous cancellation allows it to act at any time. Disabling cancellation
prevents either type from taking effect until cancellation is enabled again.

New threads start enabled and deferred. A successful `pthread_cancel()` call
requests cancellation; it does not wait for the target to terminate. The request
can remain pending. `pthread_join()` waits for termination and lets the caller
check for the result `PTHREAD_CANCELED`.

[POSIX.1-2024 section 2.9.5][posix-cancel] defines these rules. This edition is
also called Issue 8.

### A request before the call differs from one during the call

> Whenever a thread has cancelability enabled and a cancellation request has
> been made with that thread as the target, and the thread then calls any
> function that is a cancellation point [...] the cancellation request shall
> be acted upon before the function returns.

This applies even when the function can complete without blocking, if POSIX
requires it to be a cancellation point. Cancellation must happen before the
function returns. That does not necessarily mean it happens before the function
has any side effects.

When a request arrives while the thread is suspended at a cancellation point,
the thread must be awakened and the request acted on. There is an exception:
if the awaited event occurs or the timeout expires before cancellation acts,
normal completion with the request still pending is also permitted.

### Cancellation side effects are modeled on EINTR

> The side-effects of acting upon a cancellation request while suspended
> during a call of a function are the same as the side-effects that may be
> seen in a single-threaded program when a call to a function is interrupted
> by a signal and the given function returns [EINTR].

Cancellation does not undo everything the operation did. The rules depend on
the function being interrupted. For example, discarding the result after an
operation allocated a descriptor or transferred some bytes is different from
interrupting it before it made any progress. All permitted side effects must
happen before cancellation cleanup begins.

Getting individual syscalls right is not enough for a multi-step library call.
If it allocates resources or consumes input before reaching another cancellation
point, it must arrange its own cleanup.

### Cleanup, signal handlers, and asynchronous cancellation

Issue 8 requires cancellation to be disabled and its type set to deferred while
cleanup runs. Cleanup callbacks run in reverse registration order, followed by
thread-specific-data destructors. A canceled condition-variable waiter must
reacquire its mutex before the first application cleanup handler. It must not
consume a condition signal that another waiter could receive.

Only `pthread_cancel()`, `pthread_setcancelstate()`, and
`pthread_setcanceltype()` are required to be async-cancel-safe. Canceling during
another function that is not async-cancel-safe is undefined behavior. General
asynchronous cancellation is therefore not made safe merely by using Fil-C.

There is also a specific signal-handler restriction: a handler that interrupts
async-cancel-unsafe code and calls a cancellation point while cancellation is
pending, without disabling it first, invokes undefined behavior. The nested
handler probe below deliberately calls **no cancellation points in the handler**.

### Standards editions change the comparison

Two changes are particularly important:

- **Semaphores:** Issue 8 moved `sem_wait()` and `sem_timedwait()` from mandatory
  to optional cancellation points. [Austin Group issue 1076][austin-sem] explains
  the desire to avoid cancellation checks on successful fast paths. The
  Cosmopolitan semaphore result below is not an Issue 8 violation, although it
  differs from the older mandatory-point contract and from glibc/musl behavior.
- **Closing descriptors:** Issue 7 left descriptor state after `close()` returned
  `EINTR` unspecified. [Issue 8][posix-close] distinguishes `EINTR` with the
  descriptor still open from `EINPROGRESS` with it closed, and adds
  `posix_close()`. Both closing functions are mandatory cancellation points.
  [Austin Group issue 614][austin-close] records the cancellation-related work.

A comparison must distinguish POSIX conformance to a particular edition from
compatibility with a libc's established behavior.

## Two races around a syscall

A naive implementation might look like this:

```c
/* Illustrative pseudocode, not a correct cancellation wrapper. */
test_for_pending_cancellation();
result = syscall(...);
test_for_pending_cancellation();
```

**A request can arrive after the first check but before the syscall.** If the
cancellation signal is handled in that gap, the syscall can then block with no
signal left to wake it. Remembering that cancellation is pending does not help
if the thread is asleep and cannot check again.

**A request can also arrive after the syscall succeeds but before the caller
gets the result.** The kernel may already have allocated a descriptor or
transferred bytes. Canceling at the second check can lose that information.
A cleanup handler cannot close a descriptor whose number it never received,
and cannot generally put consumed input back.

The desired distinction for ordinary restartable I/O is:

| When cancellation arrives | Intended behavior for ordinary restartable I/O |
| --- | --- |
| Before the final pending check | Act on cancellation |
| After that check, before syscall entry | Act on cancellation; do not sleep |
| While blocked, before making any progress | Interrupt and act on cancellation |
| After partial or complete progress | Return the result; leave cancellation pending |

Each syscall still has its own interruption rules. `close()`, discussed below,
needs special care.

### Older glibc used temporary asynchronous cancellation

The traditional Linux NPTL wrapper, still present in the glibc 2.40 base, enabled
asynchronous cancellation around a syscall and restored the previous type after
it returned. That avoided the gap before the syscall but allowed cancellation
after successful completion and inside an unrelated application signal handler.

[glibc bug 12683][glibc-bug12683], reported in 2011, documents both failures and
includes descriptor-leak and signal-handler reproducers. The mechanism was
replaced for **glibc 2.41** by [the cancellation rewrite][glibc-rewrite]. The
rewrite was merged in August 2024; its earlier author date is not its release
date. The 2.36 experiment below reproduces the handler failure, not the
descriptor-leak test from that report.

### musl checks which instruction was interrupted

[musl's assembly wrapper][musl-asm] places labels around the final pending check
and syscall instruction. Its essential structure is:

```asm
/* Schematic: register setup and the real test instructions are omitted. */
__cp_begin:
        check_pending_cancellation
        ...
        syscall
__cp_end:
        ret
```

The cancellation signal handler examines the interrupted program counter (PC).
From `__cp_begin` up to, but not including, `__cp_end`, it redirects execution
to code that cancels the thread. At or beyond `__cp_end`, it leaves the syscall
result intact.

Linux supplies the useful distinction: when restarting an interrupted syscall,
it positions the saved PC back at the syscall instruction. When returning a
completed or partial result, it resumes after that instruction. For syscalls
that return `EINTR` rather than restart, musl also checks pending cancellation in
the C wrapper, with special treatment for `close()`.

This requires architecture-specific code. The C checks shown above cannot make
the same distinction between an interrupted syscall and a completed one.

### Modern glibc and Cosmopolitan use the same broad technique

The inspected [glibc cancellation code][glibc-bridge] calls an
[architecture-specific wrapper][glibc-asm] with start/end markers. Its signal
handler can cancel when the saved PC falls inside those markers; the C path
also handles `EINTR` with a pending request. Unlike musl's deferred path, glibc
starts cancellation from the signal handler rather than only rewriting the PC
to run cancellation code after the handler returns.

Cosmopolitan's [systemfive wrapper][cosmo-asm] explicitly credits musl. Its
cancellable region also ends **immediately after `syscall`, before the
epilogue** (the instructions that finish the wrapper). Those remaining
instructions are outside the region where the handler can cancel a deferred
request.

The implementations still differ in what happens when another signal handler
interrupts the syscall.

## What the six tests found

The following outcomes occurred in 20/20 runs for each tested build. The two
newer glibc builds are combined in the table because their observations match,
not because we tested every version between them.

| Case | Scenario | glibc 2.36 | glibc 2.41 / 2.44 | musl 1.2.6 | Cosmopolitan 4.0.2 |
| --- | --- | --- | --- | --- | --- |
| 0 | Cancel inside an unrelated handler interrupting blocked `read()` | Cancels inside handler | Handler finishes; `read()` restarts and stays blocked | Cancels after handler finishes | Cancels after handler finishes |
| 1 | Pending cancellation before ready `sem_wait()` | Cancels; token untouched | Same | Same | Consumes token and returns |
| 2 | Pending cancellation before `close()` | Cancels; descriptor open | Same | Same | Closes descriptor and returns |
| 3 | Pending cancellation before switching to async type | Cancels before setter returns | Same | Same | Setter returns without canceling |
| 4 | Disabled cancellation during blocked `read()` | Remains blocked | Same | Same | Returns `EINTR` |
| 5 | Disabled cancellation during blocked `poll()` | Remains blocked | Same | Returns `EINTR` | Returns `EINTR` |

In cases 4 and 5, "returns `EINTR`" does **not** mean the thread was canceled
while cancellation was disabled. The worker records the operation's result,
reenables cancellation, and calls `pthread_testcancel()`. This distinction also
explains why cleanup can be recorded before the controller supplies rescue data.

### Case 0: glibc misses cancellation when another handler interrupts the syscall

The test first observes the worker blocked in an empty-pipe `read()`. The
controller sends `SIGUSR1`, whose application handler uses only lock-free atomic
operations. After the handler reports entry, the controller calls
`pthread_cancel(worker)`, waits 100 ms, releases the handler, and waits another
200 ms. It then records whether the worker is still blocked and writes a
"rescue" byte to the pipe so the test can finish even if cancellation failed.

```diagram
┌─────────────────────────────┐     ┌─────────────────────────────┐
│ Worker                      │     │ Controller                  │
├─────────────────────────────┤     ├─────────────────────────────┤
│ read(empty pipe) blocks      │◀────│ send SIGUSR1                │
│ application handler spins   │◀────│ pthread_cancel(worker)      │
│ cancellation signal handled │     │                             │
│ application handler returns │◀────│ release handler             │
│ original syscall resumes    │     │ inspect, then write rescue  │
└─────────────────────────────┘     └─────────────────────────────┘
```

The source explanation for glibc 2.41/2.44's observed restart is:

1. The cancellation signal interrupts the application handler, whose saved PC
   is outside the cancellable syscall wrapper. glibc correctly avoids canceling
   the application handler under deferred cancellation.
2. [The cancellation handler][glibc-cancel] does not requeue the signal in this
   situation. The pending request bit remains set.
3. The application handler returns. Its `SA_RESTART` flag causes Linux
   to resume the original `read()` at the syscall instruction, bypassing the
   earlier pending-bit check.
4. The empty-pipe read blocks again. In the experiment, it completes only after
   the rescue byte; the subsequent explicit `pthread_testcancel()` cancels.

The decisive pre-rescue fields in both newer glibc builds are:

```text
handler_returned=1 cleaned_before_rescue=0
blocked_before_rescue=1 returned_before_rescue=0
```

The inspected `pthread_cancel()` also avoids sending another signal when the
canceled bit is already set. Repeating the same request is therefore not a
reliable workaround according to the source; the probe sends only one request.

**We consider this missed wakeup a bug**, but it has not been confirmed by glibc
upstream. Whether it violates POSIX is less clear: the phrase "while suspended
at a cancellation point" leaves room to dispute what should happen when the
request arrives during another signal handler.

The bounded wait does not prove the thread would block forever. The source does
explain why no further cancellation signal is expected. The test also waits
100 ms rather than measuring when the internal cancellation signal arrives.
It synchronizes the application handler's entry and return, but cannot prove
that every run follows exactly the internal sequence above.

### musl and Cosmopolitan keep the cancellation signal pending

When the PC is outside the syscall region, [musl's cancellation handler][musl-cancel]
does two things:

1. It adds the cancellation signal to the saved signal mask, so the signal will
   stay blocked when this handler returns.
2. It sends the signal to the same thread again. Because it is blocked, it stays
   pending rather than immediately invoking the cancellation handler again.

The application handler can now finish. When it returns, it restores the mask
from before it started, unblocking the pending signal. The cancellation handler
gets another chance to inspect the PC, this time for the interrupted syscall
rather than the application handler. This can repeat through several nested
handlers.

Cosmopolitan uses a similar mask-and-requeue scheme. In case 0, both completed
the application handler and canceled before `read()` returned.

[Rich Felker's original design explanation][musl-design] describes this purpose:
delay cancellation until it is safe, without losing the signal needed to wake
the thread. Fil-C might achieve that more simply, but it still needs to solve
the same problem.

### Cases 4 and 5: disabled cancellation can still cause EINTR

musl sends its internal signal even when the target has cancellation disabled.
The handler then returns without canceling. `SA_RESTART` protects the tested
pipe `read()`, but Linux never restarts `poll()` after signal handling, so the
latter returns `EINTR`.

[Cosmopolitan's handler installation][cosmo-cancel] omits `SA_RESTART`; both
operations return `EINTR`. Its `poll()` uses `ppoll()` on this Linux path, which
the probe's wait detection accounts for. glibc avoids sending its cancellation
signal when cancellation is disabled, leaving both tested waits undisturbed.

This can surprise code written against glibc: cancellation is disabled, yet a
cancellation request interrupts the operation. The thread was not canceled,
and we have not established a POSIX violation here.

### Cases 1 and 3: fast paths and transitions differ

Cosmopolitan's [semaphore wait][cosmo-sem] attempts `sem_trywait()` before entering
its cancellation-point machinery. The probe begins with one token and shows
both return from `sem_wait()` and consumption of the token. As noted above,
Issue 8 permits optional semaphore cancellation points; this is not evidence of
an Issue 8 defect.

Its [cancel-type setter][cosmo-type] changes the type flag without checking the
pending request. In case 3, the worker requests its own cancellation in deferred
mode, switches to asynchronous mode, records that the setter returned, switches
back, and calls `pthread_testcancel()`. With glibc and musl, it is canceled before
it can record the setter's return. With Cosmopolitan, the setter returns.
POSIX allows some latitude in when asynchronous cancellation happens, so this
timing difference alone does not prove a violation. Nor does it prove that
Cosmopolitan could never deliver the request later.

## close requires an explicit ownership policy

Retrying `close(fd)` after the descriptor was already closed can close an
unrelated descriptor: another thread may have reused the same number. But if
cancellation prevented the close, assuming it happened can leak the descriptor.
A cleanup handler therefore needs to know whether the close took effect.

| Implementation | Inspected policy |
| --- | --- |
| musl | Tests cancellation before the syscall; excludes `SYS_close` from post-`EINTR` cancellation; maps Linux close's `EINTR` to success |
| glibc | Uses its cancellable syscall bridge; the inspected generic `EINTR` cancellation check has no musl-style `SYS_close` exclusion |
| Cosmopolitan | Ordinary `close()` and its syscall stub are not cancellation points |
| FreeBSD libthr | Deliberately performs `close()` before acting on cancellation |

Sources: [musl close][musl-close] and [cancellation wrapper][musl-cancel],
[glibc wrapper][glibc-bridge], [Cosmopolitan close][cosmo-close], and
[FreeBSD syscall wrappers][freebsd-syscalls]. The glibc wrapper comments on its
assumptions about `EINTR` and close. Those assumptions do not give applications
a portable way to know whether a descriptor is still open.

Case 2 makes cancellation pending **before calling close**; it does not try to
interrupt a close in progress. glibc and musl leave the descriptor open and
cancel. Cosmopolitan closes it and returns, leaving cancellation to the later
explicit `pthread_testcancel()`.

**Cosmopolitan's return conflicts with the mandatory cancellation-point rule:**
the request was pending before the call, but `close()` returned without acting
on it. This is separate from whether its descriptor-ownership policy is useful.
We did not run FreeBSD's different ordering or assess it against every standards
edition. We also did not test interrupted closes involving sockets, filesystems,
or delayed close errors.

## Cleanup includes more than pthread callbacks

### glibc unwinds C++ scopes; musl and Cosmopolitan do not

[glibc's exit code][glibc-unwind] uses `_Unwind_ForcedUnwind` to walk back through
stack frames and run their cleanup. With the appropriate compiler support, this
runs destructors for automatic C++ objects as well as pthread cleanup callbacks.
If a C++ catch-all swallows the forced unwind instead of rethrowing it, glibc
aborts the process.

[musl's exit path][musl-exit] iterates registered cancellation cleanup handlers,
then thread-specific-data destructors. [Cosmopolitan's path][cosmo-exit] invokes
thread finalization and ultimately uses `__builtin_longjmp()` to the worker's
exit destination. Neither supplies glibc's general forced unwind through
automatic C++ object scopes. Finalizing thread-local objects is not equivalent
to destroying automatic objects on abandoned stack frames.

These are **source findings**, not results from running C++ tests. Satisfying
POSIX's C cleanup rules does not necessarily preserve glibc's C++ behavior.
Replacing forced unwind with "call the registered C cleanup functions and exit"
would change what a glibc-targeted program can expect.

### A canceled condition waiter must not steal another waiter's signal

Canceling a condition-variable wait takes more than interrupting its futex
(kernel-assisted) wait. The library must decide whether cancellation, a timeout,
or a condition signal wins, update its waiter records, and reacquire the mutex
before application cleanup. "Signal" here means a condition-variable signal,
not a Unix signal such as `SIGUSR1`.

- [glibc][glibc-cond] records when a canceled waiter effectively consumed a
  signal and supplies a replacement. Its cleanup also includes a conservative
  extra futex wake. An old FIXME beside that code describes a problem the extra
  wake addresses; it does not by itself establish a remaining bug.
- [musl][musl-cond] uses masked cancellation while resolving the wait and
  reacquiring the mutex. If a signal was consumed, it suppresses cancellation
  for this return, leaving the request pending rather than stealing the signal.
- [Cosmopolitan][cosmo-cond] can use an nsync-backed path or a simpler futex
  fallback depending on configuration and mutex properties. The [nsync path][cosmo-nsync]
  has cleanup code that removes the waiter and reacquires the mutex. Reading
  only the fallback would miss the default path's behavior.

We did not stress-test whether cancellation loses condition signals. A Fil-C
implementation will need tests for this.

### Masked cancellation is a useful extension, not a POSIX substitute

musl and Cosmopolitan support `PTHREAD_CANCEL_MASKED`, in which an eligible
operation can report `ECANCELED` instead of terminating the thread. Reporting
the error also disables cancellation. If the caller ignores it, a later
operation will not necessarily stop the thread. How the error is reported
depends on the API; for example, a syscall-style interface returns `-1` and
sets `errno`, rather than returning the positive error number directly.

This lets library code handle cancellation itself, as in musl's condition-variable
wait. It does not replace the behavior expected by an unmodified POSIX or glibc
application.

## FreeBSD uses kernel support to avoid missed wakeups

FreeBSD libthr records whether a thread is at a cancellation point and uses the
kernel's `thr_wake()` operation to wake it. The kernel can remember a wakeup
even if the thread has not gone to sleep yet, and prevent its next relevant
interruptible sleep. That closes the gap between checking and sleeping without
relying only on assembly instruction addresses. The [signal-handling code][freebsd-signals]
explains when libthr must restore this remembered wakeup.

Two further differences are instructive:

1. For a deferred-cancelable thread, the application signal-handler wrapper
   temporarily disables cancellation, restores the prior state on return, and
   rechecks cancellation. It explicitly documents that a handler escaping via
   `longjmp()` may require the application to restore cancellation state.
2. Syscall wrappers select whether to honor cancellation at their exit according
   to the operation's result. `close()` deliberately closes before cancellation;
   descriptor-producing operations preserve successful results.

Sources: [libthr cancellation state][freebsd-cancel], [signal handling][freebsd-signals],
[syscall wrappers][freebsd-syscalls], and [kernel thread wakeup][freebsd-kernel].
These are source findings about FreeBSD, not test results or a design that can
be copied unchanged to Linux. Darwin, Bionic, and other libcs are not covered.

## Fil-C must handle cancellation where it calls native code

### Upstream has upgraded to 2.44; the local pin has not

At the investigated baseline, [the upstream manifest](../lib/filc-upstream.json)
selects `projects/user-glibc-2.40/` and `projects/yolo-glibc-2.40/`. Upstream
Fil-C's later `deluge` head, [b6dd63481f79][filc-new-rev], instead builds
`projects/user-glibc-2.44/` and `projects/yolo-glibc-2.44/`, as confirmed by the
[user][filc-new-build-user] and [yolo][filc-new-build-yolo] build scripts.

The upgrade [imported glibc 2.44][filc-new-import], [rebased the Fil-C
changes][filc-new-rebase], [switched the build][filc-new-switch], and [removed the
2.40 trees][filc-new-remove]. All four commits have a September 10, 2026 committer
date (UTC). The first three have author dates of September 6–7. These are Git
timestamps, not release or public push dates.

Keep three versions separate: this checkout's 2.40-based experiment, upstream
Fil-C's 2.44 port, and native glibc 2.44. Sharing the 2.44 version number does
not give the latter two the same cancellation behavior.

### The 2.44 port still bypasses native glibc's syscall cancellation checks

For example, upstream Fil-C's [user-libc read wrapper][filc-new-read] is:

```c
ssize_t
__libc_read (int fd, void *buf, size_t nbytes)
{
  return zsys_read (fd, buf, nbytes);
}
```

This does not enter native glibc's `SYSCALL_CANCEL` path. The retained
[`__futex_abstimed_wait_cancelable64()`][filc-new-futex] likewise delegates to
`__futex_abstimed_wait64()`, which calls `zsys_futex_timedwait()` without adding
the glibc cancellation checks.

The port also retains a [generic cancellation wrapper][filc-new-bridge], but
replaces native glibc's assembly labels with separate empty C functions:

```c
void
__syscall_cancel_arch_start (void)
{
}

void
__syscall_cancel_arch_end (void)
{
}
```

It calls those functions before its pending-bit check and after its syscall
operation. But **calling a function is not the same as placing an assembly
label**. Native glibc needs addresses that mark one stretch of instructions,
from just before the pending check to immediately after the syscall. The
addresses of two separate empty functions do not mark that stretch.

The [2.44 user-libc signal handler][filc-new-cancel] still invokes
`cancellation_pc_check(ctx)` in its deferred path. Meanwhile, the newer runtime's
[signal trampoline and callback][filc-new-runtime] still discard the native
context and pass a null context to the user handler. Its
[`FILC_SYSCALL` macro][filc-new-syscall] also retains the exit/call/reenter shape
discussed below.

These are **source findings; we did not run Fil-C 2.44**. Neither the version
number nor the presence of the marker symbols establishes that it handles
cancellation like native glibc. That still needs testing. This documentation
change does not update Filnix's dependency pin.

### The pause experiment only handles a narrow case

At the [investigated baseline][filnix-baseline], the
[isolated test derivation](../tests/pipewire-cancellation.nix) applies the
[signal-reservation patch](../patches/glibc-filc-cancellation-signals.patch) and
[pause cancellation patch](../patches/glibc-filc-pause-cancel.patch) to a private
2.40-based libc without changing the shared Fil-C toolchain. These patches have
not been ported or tested against upstream Fil-C's new 2.44 sources as part of
this investigation.

The pause patch blocks cancellation during setup, establishes a supported
`siglongjmp()` destination, and atomically unblocks the signal while waiting
through `sigsuspend()`. It then starts forced unwind from an ordinary libc frame
rather than the native signal callback. It temporarily uses asynchronous
cancelability while that destination is live.

The existing [C probe](../tests/pthread-cancel.c) and
[C++ frame](../tests/pthread-cancel-cxx.cc) exercise cooperative, pending,
racing, blocked, disabled, and signal-only pause scenarios, including cleanup
and mask checks. Those tests are distinct from the native differential probe
in this document and were not rerun as part of this investigation. Their
coverage does not establish general syscall result preservation or the nested
handler case above.

### Fil-C's user signal handler cannot see the original instruction pointer

At the local Fil-C pin, the runtime works as follows. We rechecked the signal
context and syscall behavior in the newer upstream snapshot too.

- [`signal_pizlonator()`][filc-signal] discards the native `ucontext`. Signals
  received while Fil-C code is running can be delayed until a runtime poll check.
- [`call_signal_handler()`][filc-callback] copies the signal information and
  passes a null third argument to the user handler. The user-libc callback
  therefore cannot inspect the original native PC as musl's handler does.
- [`FILC_SYSCALL`][filc-syscall] exits the runtime, calls native code, captures
  the result and errno, and reenters before returning the result. Some wrappers
  must also convert results or copy output data back to Fil-C memory.
- [Forced unwinding][filc-unwind] checks whether each stack frame supports it.
  Being able to escape a callback with `siglongjmp()` does not mean it is safe
  to force-unwind through that callback or a runtime poll check.

Copying musl's PC check into Fil-C's user libc would not be enough: the PC is
not available there. Jumping out of the signal callback can also lose a result
that the native syscall already produced but the Fil-C caller has not received.

`pause()` cannot produce a descriptor or transfer bytes, so its escape mechanism
does not have to preserve those results. `open()`, `accept()`, and `read()` do.
The pause patch's temporary use of asynchronous cancellation also needs checking
when application signal handlers are nested, not just when they return normally.

### Requirements for a general implementation

The implementation should distinguish a **pending request**, its **notification**,
and the decision to **act on it**. Losing a notification must not strand a
pending request in a blocking operation, and receiving a notification must not
automatically discard an already committed result.

A likely place to make that decision is the runtime code that calls native
syscalls. It controls both the kernel call and the work needed to return its
result to Fil-C. We have not chosen an interface or implementation, but it
needs to:

1. Handle requests that are already pending when a cancellation-point call begins.
2. Avoid missed wakeups between checking for cancellation and sleeping, even
   when signal handlers interrupt the call or the kernel restarts it.
3. Return completed and partial results to the caller, or arrange cleanup for
   any resources the caller will never receive.
4. Finish any required result conversion, output copying, or cleanup before
   leaving a syscall wrapper.
5. Return to a Fil-C/libc frame that supports forced unwinding before starting it.
6. Reacquire mutexes, avoid stealing condition signals, and run cleanup callbacks
   and C++ destructors in the required order.
7. Respect disabled cancellation and document unsupported asynchronous cases.

Several compatibility choices remain:

| Dimension | Decision to make |
| --- | --- |
| Version | With upstream now based on 2.44, which native glibc 2.44 behaviors are the target, and which older 2.40 application expectations still matter? |
| Cancellation points | Which mandatory, optional, and glibc-extension points must be observable? |
| Successful operations | When completion races with cancellation, which wins, and who must clean up any resources? |
| Signals | What happens after nested handlers, mask changes, and jumps out of handlers? |
| Cleanup | Which C++ and glibc unwind guarantees must be preserved beyond POSIX callbacks? |
| Known defects | Does an actual application depend on a particular defect, or can it be fixed intentionally? |

**Recommendation:** preserve the behavior applications rely on, and keep tests
that show where Fil-C differs from known glibc bugs. Before reproducing a leak
or missed wakeup, establish whether an application actually depends on it.
This is a recommendation, not a settled project policy.

## Reproducing the native comparison

Run from the repository root on Linux x86-64. The probe requires permission to
read `/proc/self/task/TID/syscall`. Keep assertions enabled: they perform setup
and reject runs that never reach the intended kernel wait. The probe reports
what happened; it does not assign a universal pass/fail result to each libc.
It is not wired into the Nix checks.

With the corresponding toolchains already installed, compile the desired
variants into a temporary directory:

```sh
build_dir="$(mktemp -d)"
cc -O2 -Wall -Wextra -pthread \
  tests/pthread-cancel-differential.c -o "$build_dir/probe-glibc"

musl-gcc -O2 -Wall -Wextra -static -pthread \
  tests/pthread-cancel-differential.c -o "$build_dir/probe-musl"

cosmocc -O2 -Wall -Wextra -pthread \
  -DSYS_read=0 -DSYS_poll=7 -DSYS_ppoll=271 \
  tests/pthread-cancel-differential.c -o "$build_dir/probe-cosmo"
```

The three numerical definitions are Linux x86-64 syscall identifiers used only
to recognize the syscalls reported by `/proc`. Cosmopolitan's public headers
omit those macros. They do not change which syscall the libc wrapper issues,
and they are not portable to other architectures.

Run a single case by its table number:

```sh
"$build_dir/probe-glibc" 0
"$build_dir/probe-musl" 0
ape-x86_64.elf "$build_dir/probe-cosmo" 0
```

To test an extracted glibc without modifying the system installation, use the
loader and library directory from the same package. Adapt the directory layout
to the package:

```sh
libdir=/path/to/extracted/usr/lib/x86_64-linux-gnu
"$libdir/ld-linux-x86-64.so.2" --library-path "$libdir" \
  --list "$build_dir/probe-glibc"
"$libdir/ld-linux-x86-64.so.2" --library-path "$libdir" \
  "$build_dir/probe-glibc" 0
```

The following Bash function produces the counted format used in the checked-in
record. `pipefail` matters: an assertion failure must not be hidden by successful
`sort` or `uniq` commands. Use a fresh output path rather than overwriting the
historical evidence.

```bash
set -euo pipefail
run_cases() {
  local label="$1" case_id iteration
  shift
  for case_id in 0 1 2 3 4 5; do
    printf '=== %s case=%s (20 runs) ===\n' "$label" "$case_id"
    for iteration in {1..20}; do
      "$@" "$case_id"
    done | sort | uniq -c
  done
}

run_cases "$(getconf GNU_LIBC_VERSION)" "$build_dir/probe-glibc" \
  > "$build_dir/glibc-results.txt"
# Similarly pass the musl executable, an APE loader plus executable,
# or an extracted glibc loader plus its options and executable.
```

For future records, capture kernel/architecture, compiler versions, package
versions and hashes, build flags, and loader resolution alongside the output.

### Read the observations, not just the final canceled status

Each process has an eight-second watchdog. For blocking scenarios, the
controller verifies syscall entry, issues cancellation, observes before rescue,
then writes one byte so a missed wakeup does not leave the experiment hanging.
The worker includes a later explicit `pthread_testcancel()`.

Consequently, **`canceled=1` alone proves nothing about timely cancellation**.
Interpret these fields together:

- `cleaned_inside_handler`: case 0's cleanup marker before handler release.
- `handler_returned`: the handler reached its final atomic store; it did not
  get canceled before reaching that point.
- `blocked_before_rescue` and `returned_before_rescue`: whether the operation
  was still waiting or had returned before the controller supplied data.
- `operation_returned`: whether execution continued after the tested operation,
  including after rescue. It is not that operation's numeric return value.
- `errno`: the operation's recorded error in cases 0, 4, and 5; zero on success.
- `semaphore_count` and `fd_open`: independently observed token and descriptor
  state after joining the worker.

The tests arrange specific sequences of events. Repeating them checks whether
the outcomes are consistent; it does not tell us how often they occur in real
applications or cover every possible timing.

## What still needs testing

Future tests should check what cancellation leaves behind, not just whether
the thread stops:

| Test | Distinguishing observation |
| --- | --- |
| Cancel after `accept()` or `open()` allocates a descriptor | Every allocated descriptor is either returned to the caller or closed; none are lost before the caller receives them |
| Cancel after a partial write | Read the bytes at the other end and compare with the returned count; no bytes written without the caller knowing |
| Cancel a selected condition waiter while another waits | The other waiter can receive the available signal, and cleanup sees the mutex held |
| Additional handler layers, mask changes, and handler `siglongjmp()` | No stranded request, accidental handler cancellation, or permanently altered cancellation state |
| C++ objects across libc and native Fil-C frames | Destructors and pthread cleanup run exactly once in the required order |
| Repeated cancellation during cleanup | No recursive unwind or duplicated cleanup |
| Fil-C wrappers with output conversion or copy-back | Completed native outputs are not abandoned when a deferred signal is delivered during reentry |

These tests are proposals, not results. Before choosing an implementation, the
project should also settle the glibc version target and seek upstream feedback
on the nested-handler glibc finding. No upstream issue was filed as part of this
investigation.

[posix-cancel]: https://pubs.opengroup.org/onlinepubs/9799919799.2024edition/functions/V2_chap02.html#tag_16_09_05
[posix-close]: https://pubs.opengroup.org/onlinepubs/9799919799.2024edition/functions/close.html
[austin-sem]: https://austingroupbugs.net/view.php?id=1076
[austin-close]: https://austingroupbugs.net/view.php?id=614
[glibc-rev]: https://github.com/bminor/glibc/commit/04e750e75b73957cf1c791535a3f4319534a52fc
[glibc-bug12683]: https://sourceware.org/bugzilla/show_bug.cgi?id=12683
[glibc-rewrite]: https://github.com/bminor/glibc/commit/89b53077d2a58f00e7debdfe58afabe953dac60d
[glibc-cancel]: https://github.com/bminor/glibc/blob/04e750e75b73957cf1c791535a3f4319534a52fc/nptl/pthread_cancel.c
[glibc-bridge]: https://github.com/bminor/glibc/blob/04e750e75b73957cf1c791535a3f4319534a52fc/nptl/cancellation.c
[glibc-asm]: https://github.com/bminor/glibc/blob/04e750e75b73957cf1c791535a3f4319534a52fc/sysdeps/unix/sysv/linux/x86_64/syscall_cancel.S
[glibc-unwind]: https://github.com/bminor/glibc/blob/04e750e75b73957cf1c791535a3f4319534a52fc/nptl/unwind.c
[glibc-cond]: https://github.com/bminor/glibc/blob/04e750e75b73957cf1c791535a3f4319534a52fc/nptl/pthread_cond_wait.c
[musl-rev]: https://github.com/ifduyue/musl/commit/5e9972eaef08ccf55dabe254ac829a30329793d3
[musl-asm]: https://github.com/ifduyue/musl/blob/5e9972eaef08ccf55dabe254ac829a30329793d3/src/thread/x86_64/syscall_cp.s
[musl-cancel]: https://github.com/ifduyue/musl/blob/5e9972eaef08ccf55dabe254ac829a30329793d3/src/thread/pthread_cancel.c
[musl-close]: https://github.com/ifduyue/musl/blob/5e9972eaef08ccf55dabe254ac829a30329793d3/src/unistd/close.c
[musl-exit]: https://github.com/ifduyue/musl/blob/5e9972eaef08ccf55dabe254ac829a30329793d3/src/thread/pthread_create.c
[musl-cond]: https://github.com/ifduyue/musl/blob/5e9972eaef08ccf55dabe254ac829a30329793d3/src/thread/pthread_cond_timedwait.c
[musl-design]: https://www.openwall.com/lists/musl/2011/04/18/1
[cosmo-release]: https://github.com/jart/cosmopolitan/commit/5907304049f37c9ed77593974d13202829443bea
[cosmo-initial]: https://github.com/jart/cosmopolitan/commit/5ddb5c2adad79407fb800fce47f389611f90a511
[cosmo-rev]: https://github.com/jart/cosmopolitan/commit/3293fad0a9eac7865c019be98fb993eeb933405e
[cosmo-asm]: https://github.com/jart/cosmopolitan/blob/3293fad0a9eac7865c019be98fb993eeb933405e/libc/sysv/systemfive.S
[cosmo-cancel]: https://github.com/jart/cosmopolitan/blob/3293fad0a9eac7865c019be98fb993eeb933405e/libc/thread/pthread_cancel.c
[cosmo-sem]: https://github.com/jart/cosmopolitan/blob/3293fad0a9eac7865c019be98fb993eeb933405e/libc/thread/sem_timedwait.c
[cosmo-type]: https://github.com/jart/cosmopolitan/blob/3293fad0a9eac7865c019be98fb993eeb933405e/libc/thread/pthread_setcanceltype.c
[cosmo-close]: https://github.com/jart/cosmopolitan/blob/3293fad0a9eac7865c019be98fb993eeb933405e/libc/calls/close.c
[cosmo-exit]: https://github.com/jart/cosmopolitan/blob/3293fad0a9eac7865c019be98fb993eeb933405e/libc/thread/pthread_exit.c
[cosmo-cond]: https://github.com/jart/cosmopolitan/blob/3293fad0a9eac7865c019be98fb993eeb933405e/libc/thread/pthread_cond_timedwait.c
[cosmo-nsync]: https://github.com/jart/cosmopolitan/blob/3293fad0a9eac7865c019be98fb993eeb933405e/third_party/nsync/mem/nsync_cv.c
[freebsd-rev]: https://github.com/freebsd/freebsd-src/commit/44b73821d1c077bf899298cbebbb2f625598c8e9
[freebsd-cancel]: https://github.com/freebsd/freebsd-src/blob/44b73821d1c077bf899298cbebbb2f625598c8e9/lib/libthr/thread/thr_cancel.c
[freebsd-signals]: https://github.com/freebsd/freebsd-src/blob/44b73821d1c077bf899298cbebbb2f625598c8e9/lib/libthr/thread/thr_sig.c
[freebsd-syscalls]: https://github.com/freebsd/freebsd-src/blob/44b73821d1c077bf899298cbebbb2f625598c8e9/lib/libthr/thread/thr_syscalls.c
[freebsd-kernel]: https://github.com/freebsd/freebsd-src/blob/44b73821d1c077bf899298cbebbb2f625598c8e9/sys/kern/kern_thr.c
[filc-rev]: https://github.com/pizlonator/fil-c/commit/4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c
[filc-signal]: https://github.com/pizlonator/fil-c/blob/4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c/libpas/src/libpas/filc_runtime.c#L1747-L1820
[filc-callback]: https://github.com/pizlonator/fil-c/blob/4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c/libpas/src/libpas/filc_runtime.c#L1052-L1124
[filc-syscall]: https://github.com/pizlonator/fil-c/blob/4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c/libpas/src/libpas/filc_runtime.h#L4581-L4592
[filc-unwind]: https://github.com/pizlonator/fil-c/blob/4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c/libpas/src/libpas/filc_runtime.c#L7398-L7435
[filnix-baseline]: https://github.com/mbrock/filnix/commit/32bf7f5e1e229a2be47bbc2ab048d985e30dc9f5
[filc-new-rev]: https://github.com/pizlonator/fil-c/commit/b6dd63481f796f8bff8502165c7dfc61091dbbd6
[filc-new-build-user]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/build_user_glibc.sh#L32-L40
[filc-new-build-yolo]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/build_yolo_glibc.sh#L31-L38
[filc-new-import]: https://github.com/pizlonator/fil-c/commit/742f85a6089401b80619029c7410a261eb5b7327
[filc-new-rebase]: https://github.com/pizlonator/fil-c/commit/181a1a5fd24a514e2892928c4536e71c5a50937d
[filc-new-switch]: https://github.com/pizlonator/fil-c/commit/495b0d6d62d0b6a5964990dfef9733abcf337ea7
[filc-new-remove]: https://github.com/pizlonator/fil-c/commit/94a9554660470a26432d4d1201a1d85ef20f2a47
[filc-new-read]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/projects/user-glibc-2.44/sysdeps/unix/sysv/linux/read.c#L19-L28
[filc-new-futex]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/projects/user-glibc-2.44/nptl/futex-internal.c#L25-L44
[filc-new-bridge]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/projects/user-glibc-2.44/sysdeps/unix/sysv/linux/syscall_cancel.c#L22-L94
[filc-new-cancel]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/projects/user-glibc-2.44/nptl/pthread_cancel.c#L32-L56
[filc-new-runtime]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/libpas/src/libpas/filc_runtime.c
[filc-new-syscall]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/libpas/src/libpas/filc_runtime.h#L4581-L4592
