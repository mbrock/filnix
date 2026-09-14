# Thread cancellation: what Fil-C needs to get right

Suppose a worker thread is waiting for input that will never arrive. Another
thread wants to shut it down. `pthread_cancel()` is meant to make that possible
without making the worker abandon a lock or lose track of a resource halfway
through an operation.

The difficulty is deciding exactly when the worker may stop. Too early, and it
can lose a file descriptor or a record of bytes it has already written. Too
late, and it can go back to sleep despite the request to stop.

This is why a cancellation fix that makes one PipeWire test pass is not yet a
general implementation. Filip Pizlo suggested comparing glibc, musl, and
Cosmopolitan to understand both their intended behavior and their bugs before
deciding what Fil-C should reproduce. This article explains what that comparison
found, with FreeBSD's thread library as a useful alternative design.

**The current starting point is Fil-C's glibc 2.44 port.** Upstream had already
upgraded when this investigation was done on September 14, 2026; its head was
rechecked for this revision. Filnix's older 2.40 pin is historical context, not
the latest upstream version. Tests of ordinary, non-Fil-C glibc 2.44 do not tell
us whether Fil-C's port behaves the same way. That distinction matters below.

The explanation comes first. Exact source revisions, test output, and commands
are in the [research notes](pthread-cancellation-notes.md). Those notes separate
what was tested from what was learned by reading source code.

The follow-up [implementation proposal](pthread-cancellation-design.md) defines
a candidate Fil-C/glibc contract, runtime and compiler responsibilities, and
acceptance tests. It is a proposed design, not an implemented general fix.

The [implementation checkpoint](pthread-cancellation-implementation.md) records
the resulting native runtime/glibc patches, executed Fil-C tests and remaining
coverage gaps.

## Cancellation is a request, not an immediate kill

A successful `pthread_cancel(worker)` call means that cancellation has been
requested. It does not mean the worker has stopped. The request can remain
**pending** until the worker reaches a place where it can act on it.

New threads start with cancellation enabled and **deferred**: they act on
requests during designated calls, known as **cancellation points**. A blocking
`read()` is one example. `pthread_testcancel()` is an explicit check that does
no other work.
When cancellation takes effect, the thread runs its cancellation cleanup and
exits rather than returning normally from that call. Another thread can wait
with `pthread_join()` and check for the result `PTHREAD_CANCELED`.

The application registers cleanup callbacks to release locks or resources it
owns. The libc does not automatically discover what the application needs to
clean up. This is one reason the exact stopping point matters.

There are two settings, and they answer different questions:

- **Enabled or disabled:** may cancellation take effect at all? Disabling it
  leaves requests pending until it is enabled again.
- **Deferred or asynchronous:** must cancellation wait for a cancellation
  point, or may it happen during other code too?

Asynchronous cancellation sounds convenient, but it gives the application much
less control over what it leaves unfinished. The standard guarantees safety
when interrupting only three thread-management functions this way:
`pthread_cancel()`, `pthread_setcancelstate()`, and `pthread_setcanceltype()`.
Canceling asynchronously during a function that is not safe for it has undefined
behavior. Fil-C's memory safety does not make arbitrary asynchronous cancellation
safe for locks, resources, or application state.

Most of the interesting problems here occur even with **deferred** cancellation.

## What POSIX requires—and what its issue numbers mean

POSIX is the standard that specifies portable Unix interfaces, including these
thread functions. glibc, musl, and Cosmopolitan implement those interfaces. They
can make different choices where the standard allows them to, and they can also
have bugs. A difference between two libcs is therefore not automatically a
standards violation.

The references use “issue” in two unrelated senses:

- **POSIX Issue 8 is an edition of the standard:** [POSIX.1-2024][posix-edition].
  “Issue 7” refers to the previous edition. This is like a book's edition number,
  not the number of a bug. This article uses “2024 standard” after this point.
- **An Austin Group issue is a tracker ticket.** The Austin Group maintains
  POSIX. Its tickets discuss defects, ambiguities, and proposed changes. For
  example, [ticket 1076][austin-sem] led to a change in the rules for semaphore
  waits. The number identifies the discussion; the accepted change is what
  matters to this investigation.

Three [cancellation rules][posix-cancel] explain most of the results below:

1. **A request already pending before a required cancellation-point call must
   take effect before that call returns**, if cancellation is enabled. The
   function need not block for this rule to apply. It may still have side effects
   before cancellation takes effect.
2. **A request during a blocking call can race with successful completion.**
   A waiting thread must be awakened to act on cancellation, but if the event
   it was waiting for occurs, or its timeout expires, before cancellation acts,
   normal return with cancellation still pending is also allowed.
3. **Cancellation is not rollback.** The permitted side effects of canceling
   a suspended call are those it could have had if interrupted by a signal and
   returning `EINTR`, the “interrupted operation” error. What that permits depends
   on the function. Those side effects must happen before cancellation cleanup.

The first rule concerns a request **before** the call. The second concerns a
request **during** it. Treating them as the same rule can make allowed behavior
look like a bug—or make a real violation look harmless.

The standard also changes over time. As we will see with `sem_wait()`, behavior
that conflicts with an older requirement can be allowed by the 2024 standard.
That does not make it interchangeable with glibc for an existing application.

## The two races around a syscall

A libc function such as `read()` usually wraps a kernel system call, or
**syscall**. The kernel may put the thread to sleep until data arrives. On Linux,
these libcs use an internal Unix signal to notify a thread about cancellation
and interrupt a blocked syscall. The pending request and the signal are separate:
the request records that the thread should stop; the signal gives it a chance
to notice.

It is tempting to implement a wrapper like this:

```c
/* Pseudocode: this is not a correct cancellation wrapper. */
check_for_cancellation();
result = syscall(...);
check_for_cancellation();
return result;
```

**The first check can be too early.** Suppose the cancellation signal arrives
just after the check. The handler runs and returns, and the thread then enters
the syscall. It can go to sleep with cancellation pending but no signal left to
wake it. A flag in memory cannot wake a sleeping thread by itself.

**The second check can be too late.** Suppose `accept()` has created a new socket
and returned its descriptor to the libc wrapper. If cancellation takes effect
before the wrapper returns that descriptor to the application, the application
has no number to pass to `close()`. Its cleanup handler cannot recover a resource
it never learned about. Similarly, a write may already have sent some bytes;
discarding its return value hides how much was sent.

For ordinary restartable I/O, the useful distinction is therefore: stop before
sleeping or while blocked without progress, but preserve a completed or partial
result. Individual functions still have their own rules. In particular,
`close()` needs separate treatment.

## How modern glibc, musl, and Cosmopolitan tell the difference

The Linux implementations we inspected use the interrupted instruction address to
recognize when cancellation can take effect. This address is called the
**program counter**, or PC. Linux saves it when delivering a signal.

The assembly wrapper marks a small stretch of instructions:

```asm
/* Schematic: argument setup and actual test instructions are omitted. */
begin:
        check_pending_cancellation
        syscall
end:
        return_to_caller
```

If the signal arrives between the pending check and the syscall, the PC is
inside this region. The handler can stop the thread before it enters the kernel.

When Linux restarts a syscall interrupted before it made progress, the saved
PC points back at the syscall instruction. When the syscall has a completed or
partial result to return, execution resumes after that instruction—at `end`,
outside the marked region. The cancellation handler can use this distinction
to stop the first case without throwing away the second case's result.

In [musl][musl-cancel], a deferred-cancellation handler redirects the PC to code
that cancels the thread after the handler returns. [Modern glibc][glibc-cancel]
can start cancellation from the handler itself. Their C wrappers also handle a
syscall returning `EINTR` with cancellation pending. [Cosmopolitan's assembly
wrapper][cosmo-asm] uses the same broad boundary technique and credits musl.
Its marked region also ends immediately after the syscall, before the remaining
instructions that return to the caller.

This is architecture-specific machinery, but it solves a concrete problem that
ordinary C checks before and after the call do not solve.

### Why older glibc behaves differently

glibc adopted this technique in **2.41**, so native 2.44 already contains it.
The older Linux implementation, still used in the 2.40 sources that Filnix pins,
temporarily enabled asynchronous cancellation around syscalls. This covered
the gap before sleeping, but also allowed cancellation after a syscall had
succeeded—or inside an unrelated application signal handler.

The [glibc bug report about those races][glibc-bug] dates to 2011. The
[replacement implementation][glibc-rewrite] was merged in August 2024 for 2.41.
Our host glibc 2.36 reproduces the old signal-handler problem. We did not execute
the descriptor-leak reproducer from that report.

This is why “match glibc” needs a version attached. Matching the old temporary
asynchronous behavior would not match what glibc 2.44 is trying to do.

## A signal handler can still make modern glibc miss cancellation

The PC check works when the cancellation signal interrupts the syscall wrapper.
What if another signal handler is running on top of it?

Our test arranges this sequence:

1. A worker blocks in `read()` on an empty pipe.
2. The controller sends `SIGUSR1`. Its application handler starts running in
   the worker and waits for permission to return.
3. While that handler is running, the controller requests cancellation.
4. The controller lets the application handler return, then checks whether the
   worker stopped or went back to waiting for input.

The application handler uses only lock-free atomic operations and calls **no
cancellation points**. This matters because calling a cancellation point from
a handler that interrupted cancellation-unsafe code can itself have undefined
behavior. That is not what this test is trying to exercise.

Each outcome occurred in all 20 runs for the corresponding build:

| Tested libc | What happened |
| --- | --- |
| glibc 2.36 | Cancellation stopped the thread inside the application handler. |
| glibc 2.41 and 2.44 | The handler finished, but `read()` restarted and stayed blocked until the test supplied data. |
| musl 1.2.6 | The handler finished, then the thread canceled before `read()` returned. |
| Cosmopolitan 4.0.2 | The handler finished, then the thread canceled before `read()` returned. |

Reading glibc's source explains the newer result. The cancellation signal sees
a PC inside the application handler, outside the syscall wrapper. It correctly
avoids canceling that handler, but does not arrange another signal for later.
The application handler was installed with `SA_RESTART`, meaning Linux should
restart this interrupted read when the handler returns. Execution goes straight
back to the syscall instruction, without repeating the earlier pending check.
The thread sleeps again.

musl and Cosmopolitan arrange a second chance. When the PC is outside the
cancellable region, they keep the cancellation signal blocked and send it to
the same thread again. It stays pending instead of immediately interrupting
the handler a second time. Returning from the application handler restores the
older signal mask—the set of signals blocked before that handler started—and
lets the pending signal be delivered against the underlying syscall. musl's [original design
explanation][musl-design] describes why this is needed. The research notes give
the [mask and requeue details](pthread-cancellation-notes.md#musl-and-cosmopolitan-keep-the-cancellation-signal-pending).

**This looks like a missed-wakeup bug in modern glibc, not proof that its whole
cancellation design is wrong.** It has not been confirmed by upstream. The POSIX
wording about cancellation “while suspended at a cancellation point” also leaves
room to debate a request arriving during another handler.

The test waits a bounded time, then supplies a rescue byte, so it does not prove
the worker would wait forever. It also delays 100 ms rather than directly
measuring receipt of the internal cancellation signal. The repeated observations
and source agree, but we have not proved every internal scheduling step. The
source suggests that repeating `pthread_cancel()` would not help once the
request bit is set; the test itself sends only one request.

## Differences outside the difficult syscall race

Four simpler comparisons help separate standards choices from compatibility
problems. They also show why one successful blocking-cancellation test is not
enough.

### A semaphore can return immediately without checking cancellation

A semaphore holds a count of available tokens. `sem_wait()` takes a token if
one is available, or waits if none are available. We gave it one token and made
cancellation pending before the call.

glibc and musl canceled the thread and left the token untouched. Cosmopolitan
took the token and returned. Its implementation tries the immediate-success
path before entering its cancellation machinery.

The **2024 standard allows this choice**. Earlier POSIX required `sem_wait()`
and `sem_timedwait()` to be cancellation points; the 2024 edition makes them
optional. The accepted [standards change for semaphore waits][austin-sem]
allowed implementations to avoid an extra cancellation check on the fast path.
That is the significance of ticket 1076—not that it reports a Cosmopolitan bug.

An application expecting glibc's behavior can still notice the difference.
“Allowed by current POSIX” and “behaves like glibc” are different claims.

### Closing a descriptor raises an ownership question

If cancellation happens during `close(fd)`, should cleanup close `fd` again?
If the first close already happened, another thread might have reused that
number, and the retry could close an unrelated file. If cancellation prevented
the close, failing to retry can leak the original descriptor.

Our test asks the narrower question: what if cancellation is pending **before**
calling `close()`? glibc and musl canceled and left the descriptor open.
Cosmopolitan closed it and returned; the thread canceled only at the explicit
`pthread_testcancel()` that followed. Unlike semaphore waits, `close()` remains
a required cancellation point. Returning with the earlier request still pending
conflicts with that rule.

The interrupted-close case needs separate testing. musl explicitly excludes
`close()` from its usual cancellation check after `EINTR` and treats Linux
close's `EINTR` as success. glibc's generic check has no such exclusion. FreeBSD
deliberately closes before acting on cancellation. These are source findings,
not interrupted-close test results.

The [2024 close specification][posix-close] also changed the portable error
rules: `EINTR` means the descriptor remains open, while `EINPROGRESS` means it
is closed. The older standard left its state after `EINTR` unspecified. Do not
assume those newer rules describe every existing OS implementation. The
[research notes](pthread-cancellation-notes.md#close-requires-an-explicit-ownership-policy)
trace the libc policies and the standards discussion.

### Disabling cancellation does not always prevent an interruption

We also requested cancellation while the worker had cancellation disabled and
was blocked in either `read()` or `poll()`. Here `poll()` waits for a descriptor
to become ready for I/O.

| Tested libc | Blocked read | Blocked poll |
| --- | --- | --- |
| glibc 2.36, 2.41, and 2.44 | Stayed blocked | Stayed blocked |
| musl 1.2.6 | Stayed blocked | Returned `EINTR` |
| Cosmopolitan 4.0.2 | Returned `EINTR` | Returned `EINTR` |

glibc avoids sending its internal cancellation signal when cancellation is
disabled. musl sends it, but its handler does not cancel the thread. The read
restarts; Linux does not restart `poll()` after signal handling. Cosmopolitan
does not install its cancellation handler with `SA_RESTART`, so both operations
are interrupted. Its Linux poll path uses `ppoll()`, a related syscall.

An interrupted operation is **not a canceled thread**. These results show a
compatibility difference, not cancellation taking effect while disabled. We
have not established a POSIX violation here.

### Switching to asynchronous mode does not have identical timing

In the remaining test, a worker requested its own deferred cancellation, then
switched to asynchronous mode. glibc and musl canceled before the setter returned.
Cosmopolitan returned from the setter; the worker later canceled at an explicit
check. POSIX allows latitude in asynchronous delivery timing, so this alone
does not establish a violation or prove the request could never arrive later.

## Stopping the thread is only part of cleanup

The 2024 standard requires registered pthread cleanup callbacks to run in
reverse registration order, followed by destructors for thread-specific data.
Cancellation is disabled and its type set to deferred while cleanup runs.
But that is not the whole behavior a glibc application may expect.

**C++ cleanup differs.** glibc uses *forced unwinding*: it walks back through
stack frames and runs their cleanup. With appropriate compiler support, this
runs destructors for local C++ objects too. A catch-all that swallows the forced
unwind instead of rethrowing it causes glibc to abort the process. musl and
Cosmopolitan run their registered thread cleanup without providing glibc's
general unwind through local C++ object scopes. Running thread-local destructors
is not the same as destroying local objects on abandoned stack frames.

**A condition-variable wait needs coordination, not just interruption.** A
condition variable lets threads wait for a notification while sharing a mutex.
A canceled waiter must reacquire that mutex before application cleanup. It also
must not consume a notification that another waiting thread could receive.
glibc can send a replacement notification; musl can let a notified waiter return
normally and leave cancellation pending. Cosmopolitan has more than one
implementation of condition waits, selected by configuration and mutex
properties. Its simpler fallback does not establish how the default path behaves.

These are [source findings about cleanup](pthread-cancellation-notes.md#cleanup-includes-more-than-pthread-callbacks).
We did not run a cross-libc C++ test or a condition-variable stress test. musl
and Cosmopolitan also have a non-POSIX “masked cancellation” extension that lets
some operations report an error instead of exiting; the notes explain its use
and limits.

## FreeBSD shows another way to prevent missed wakeups

FreeBSD's thread library, libthr, uses kernel support that Linux libcs do not
have in this form. Its `thr_wake()` operation can leave a remembered wakeup that
prevents a subsequent interruptible sleep. The notification need not disappear
just because it arrived before the thread went to sleep.

libthr also wraps application signal handlers: for deferred cancellation it
temporarily disables cancellation, restores the old setting when the handler
returns, and checks again. A handler that jumps out with `longjmp()` complicates
that restoration. These [FreeBSD source findings](pthread-cancellation-notes.md#freebsd-uses-kernel-support-to-avoid-missed-wakeups)
show an alternative to relying only on instruction addresses. We did not run
FreeBSD, and its design cannot simply be copied into a Linux libc.

## What the glibc 2.44 upgrade means for Fil-C

**Native glibc 2.44 and Fil-C's glibc 2.44 port are different implementations
of important cancellation paths.** Native here means the ordinary build,
without Fil-C instrumentation. The native build is the one in our test results.

At the [upstream Fil-C revision we inspected][filc-current], the [user-libc read
wrapper][filc-read] calls `zsys_read()` rather than glibc's ordinary cancellable
syscall wrapper. Its low-level synchronization wait, a futex wait, also goes
through the Fil-C runtime. The runtime makes the actual native call, then
returns to Fil-C code.

That changes where the cancellation decision can be made:

- Fil-C's user signal handler does not receive the original native signal
  context, including the PC. Copying musl's PC check into that handler is not
  enough when the information it needs is missing.
- Returning from a native syscall is not necessarily the end of the work.
  The runtime has to return to Fil-C execution, and some wrappers must convert
  results or copy output data. Canceling during that work can still hide a
  result the kernel already produced.
- Forced unwinding needs supported stack frames. Being able to jump out of a
  callback does not mean it is safe to unwind through arbitrary native or
  runtime frames.

The port also retains cancellation-marker names as empty C functions. Calling
those functions before and after an operation does not make their addresses
mark the syscall's instruction range, as native glibc's assembly labels do.
The [source audit](pthread-cancellation-notes.md#the-244-port-still-bypasses-native-glibcs-syscall-cancellation-checks)
documents this and the runtime paths. **We have not executed Fil-C 2.44's
cancellation behavior.** The source findings explain why the version bump alone
does not settle it; they are not a replacement for testing the port.

The earlier Filnix `pause()` experiment remains useful, but narrow. `pause()`
does not allocate a descriptor or transfer bytes. Escaping that wait and
starting cleanup therefore does not prove that the same escape is safe for
`accept()`, `open()`, or `read()`. Its use of temporary asynchronous cancellation
also needs testing with nested application handlers.

## What to preserve, and what to test next

For current upstream work, native glibc 2.44 is the relevant comparison—not the
old 2.40 implementation merely because this checkout still pins it. That does
not require blindly reproducing every glibc bug. It does require naming any
intentional difference and checking whether applications depend on it.

The most promising place to handle the syscall races is the Fil-C runtime code
that makes the native call. It controls both the transition into the kernel and
delivery of the result back to Fil-C. This is a proposed direction, not a chosen
implementation. Higher-level operations such as condition-variable waits still
need their own cleanup rules.

The next tests should ask concrete questions:

- Can a pending request leave a thread asleep after a nested signal handler?
- If cancellation races with `accept()` or `open()`, is every allocated
  descriptor either returned to the caller or closed?
- If a write sends only some bytes, does the caller learn how many were sent?
- Does canceling a condition waiter leave its mutex held for cleanup and its
  notification available to another waiter when required?
- Do pthread callbacks and C++ destructors run exactly once, even when another
  cancellation request arrives during cleanup?
- Can a result be lost while a Fil-C wrapper converts it or copies data back?

Memory safety does not answer these questions. Cancellation needs its own
accounting for what the thread has already done and what it can safely abandon.

## Evidence and reproduction

The [test program](../tests/pthread-cancel-differential.c) ran six scenarios
20 times on each of five Linux x86-64 builds: glibc 2.36, 2.41, and 2.44,
musl 1.2.6, and Cosmopolitan 4.0.2. That is **600 recorded executions**, all on
kernel `6.1.158+`. The [counted results](pthread-cancellation-results.txt) preserve
the observations; the [full comparison table](pthread-cancellation-notes.md#what-the-six-tests-found)
maps them to case numbers.

The tests arrange particular timings; they do not measure how often a problem
occurs in real applications or prove what happens under every schedule. The
build record names the libc packages but does not retain enough compiler and
archive information to reconstruct every binary exactly. Source-only findings
and newer source snapshots must not be mistaken for tested builds.

For verification, use the [build and run instructions](pthread-cancellation-notes.md#reproducing-the-native-comparison)
and [exact source revisions](pthread-cancellation-notes.md#source-versions-we-read).
The worker eventually calls `pthread_testcancel()` after any rescue, so its final
`canceled=1` result alone says nothing about whether cancellation happened at the
right time. The notes explain which output fields distinguish the behaviors.

[posix-edition]: https://pubs.opengroup.org/onlinepubs/9799919799.2024edition/mindex.html
[posix-cancel]: https://pubs.opengroup.org/onlinepubs/9799919799.2024edition/functions/V2_chap02.html#tag_16_09_05
[posix-close]: https://pubs.opengroup.org/onlinepubs/9799919799.2024edition/functions/close.html
[austin-sem]: https://austingroupbugs.net/view.php?id=1076
[musl-cancel]: https://github.com/ifduyue/musl/blob/5e9972eaef08ccf55dabe254ac829a30329793d3/src/thread/pthread_cancel.c
[musl-design]: https://www.openwall.com/lists/musl/2011/04/18/1
[glibc-cancel]: https://github.com/bminor/glibc/blob/04e750e75b73957cf1c791535a3f4319534a52fc/nptl/pthread_cancel.c
[glibc-bug]: https://sourceware.org/bugzilla/show_bug.cgi?id=12683
[glibc-rewrite]: https://github.com/bminor/glibc/commit/89b53077d2a58f00e7debdfe58afabe953dac60d
[cosmo-asm]: https://github.com/jart/cosmopolitan/blob/3293fad0a9eac7865c019be98fb993eeb933405e/libc/sysv/systemfive.S
[filc-current]: https://github.com/pizlonator/fil-c/commit/b6dd63481f796f8bff8502165c7dfc61091dbbd6
[filc-read]: https://github.com/pizlonator/fil-c/blob/b6dd63481f796f8bff8502165c7dfc61091dbbd6/projects/user-glibc-2.44/sysdeps/unix/sysv/linux/read.c#L19-L28
