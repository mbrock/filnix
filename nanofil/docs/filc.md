# How Fil-C works

Fil-C is a memory-safe implementation of C and C++. It compiles existing programs with few or no changes: OpenSSH, CPython, curl, SQLite, Emacs and [hundreds more](https://fil-c.org/programs_that_work). It guarantees that no access reaches memory the pointer was not given, however buggy or hostile the code. A program that breaks that rule stops with a Fil-C panic; it is never quietly corrupted. Fil-C is Filip Pizlo's work: a fork of clang 20 with one new LLVM pass, a runtime library, and a concurrent garbage collector.

This page explains how those parts fit together. Each idea links to its page in the [concept index](concepts/), and each section cites Fil-C's own documentation on [fil-c.org](https://fil-c.org/documentation) and its source. The shaded notes say where nanofil meets the same idea. nanofil is a second, small compiler for the same target, written in Prolog ([the guide](guide.md)), with a Rocq model that proves its checks are enough ([the formal campaign](formal.md)).

## The promise

Fil-C's rule is called [[gimso|GIMSO]], garbage in, memory safety out. The compiler gives every program a memory-safe meaning, however strange the program is. Each operation either does what C says it does or ends the program in a [[trap|Fil-C panic]]. There is no third outcome where a bad pointer reads or writes someone else's bytes. Fil-C has no `unsafe` keyword, and Fil-C code does not call ordinary C code. The whole userland is compiled with it, libc included, so no unchecked code shares the address space with the program.

Fil-C also aims to be fanatically compatible. Pointers stay 8 bytes. Unions, type punning, pointer arithmetic outside an object and casts between pointers and integers all keep working, provided the program never uses a pointer to touch memory outside its object. That combination drives everything below: checks must be dynamic, and the information they need must ride along with pointers without changing their size.

> nanofil keeps the same promise in two halves. [[pizlonate|Pizlonating]] makes every check explicit in its IR, and the [[validator]] accepts only checked IR whose accesses are all covered. [[soundness|Soundness]] ([valid_no_unchecked]) proves that a validated module never makes an unchecked access. The model's [[outcome|outcomes]] separate a panic, which it calls a [[trap]], from [[unchecked]], the outcome GIMSO rules out.

## Pointers carry capabilities

Every pointer in Fil-C carries a [[capability]]: the authority to access one object. While a pointer is in a register or local variable, it is a [[flight-pointer|flight pointer]], a pair of words:

- the intval, the address the program sees. The program can do anything with it: add to it, mask it, print it, compare it. Nothing trusts it.
- the [[lower]], a pointer to the start of the object this pointer may access. The program cannot see or change it. Only an allocation creates one, and every pointer derived from that allocation's result carries it.

Just below the lower sits the object header, which the program cannot reach:

```diagram
┌──────────────────────────────┐
│ upper: one past the object   │   lower − 16
│ aux word: flags, aux pointer │   lower − 8
├──────────────────────────────┤ ← lower
│ payload: the object's bytes  │
└──────────────────────────────┘ ← upper
```

An access of N bytes at a pointer is allowed when lower ≤ intval and intval + N ≤ upper, and the flags allow it: a write needs an object that is not read-only. Vector and pointer accesses must also be aligned. Anything else panics, with a message naming the reason and the source line ([InvisiCaps](https://fil-c.org/invisicaps), [GIMSO](https://fil-c.org/gimso)).

There are three kinds of capability. A null lower allows nothing, which is what a pointer made from a plain integer gets. A plain capability has bounds. A special capability belongs to a function or a runtime object such as a thread. Its upper equals its lower, so no data access passes, and its flags say what it is.

> nanofil's interpreter and the Rocq model write a pointer as `ptr(Addr, Cap)` ([ptr]). They abstract the lower to the object's [[identity]] and keep its current bounds in a [[region]], so freeing through one alias empties what every alias sees. The access test is `interp:cap_access_res/7`, transcribed as [cap_access_res]. It tests null, then bounds, then read-only, then alignment.

## Pointers at rest

A pointer stored to memory is a pointer at rest, and Fil-C still has to keep its capability. It cannot widen the pointer, because C programs know `sizeof(void *)` is 8. So the intval goes in the object's bytes, where the program expects it. The lower goes in the object's [[aux|aux allocation]], a side table as large as the payload that the aux word in the header points to, slot for slot. No capability's bounds ever cover an aux allocation, which is why the capabilities are invisible: the name InvisiCaps.

This layout has three useful consequences:

- Store a pointer and load the slot back as an integer, and you get its intval. Store an integer over a pointer and load a pointer back, and you get the new intval with the old lower: a pointer that may trap, never a forged one.
- Two threads racing on a pointer slot may tear it, pairing one store's intval with another's lower. The result is still a lower the runtime created, so the worst case is a panic. Atomic pointers (`_Atomic`, `std::atomic`) never tear: their slot holds an atomic box, a 16-byte object with the whole pair, updated by 128-bit atomics.
- The garbage collector finds every pointer in an object by reading its aux allocation alone. An object that never held a pointer has none and is a leaf.

> In nanofil a pointer load or store expands to a fixed protocol of aux, lower and address steps (`ir:pointer_memory_effects/2`). The Rocq model keeps the stored capabilities as [m_aux], and the [[runtime]] axiom [aux_round_trip] says what the runtime may do to them at a safepoint.

## Integers that become pointers again

Casting a pointer to an integer and back is common C. Masking off tag bits and rounding to an alignment are typical uses. By the rules above, an integer turned into a pointer has a null lower and can access nothing. To make real code work, the compiler runs a small abstract interpreter over each function. When the integer certainly came from exactly one pointer, through arithmetic, phis and selects but not through memory or a call, the new pointer gets that pointer's lower. Fil-C calls this [[launder|pointer-as-int laundering]] ([GIMSO, inttoptr](https://fil-c.org/gimso#inttoptr)).

> nanofil does the same in `launder:launder_func/4`, before checking. The model sees only the result: an unlaundered integer-to-pointer conversion ([Itop]) yields a pointer with no capability.

## Free, and the collector

C's `free` must work, and use after free must be caught every time, not just when the memory happens to be unmapped. Fil-C gets both by not reusing memory until nothing points to it.

Free is immediate and cheap. It sets the object's upper to its lower and raises its free flag, so every pointer to the object, in any thread, now fails every check, and a second free panics too. The memory itself stays, because pointers to it may still exist. [[fugc|FUGC]], Fil's Unbelievable Garbage Collector, reclaims it later. As it marks, it repoints every lower that names a freed object at a single shared free singleton, so the freed memory has no references left and can be swept. A program that forgets to free leaks nothing: an unreachable object is reclaimed anyway ([FUGC](https://fil-c.org/fugc)).

FUGC runs on its own threads, concurrently with the program and in parallel. It never moves objects and never stops the world. It needs only a store barrier: while it marks, storing a pointer marks its target. It needs no load barrier, because it rescans thread stacks until nothing new turns up.

> The model has one thread and no collector. Instead, the [[runtime]] is a page of axioms in Runtime.v, each with a native test. Allocation is [[fresh]] ([fresh_allocation]); no object moves ([non_moving]); free changes only the header ([[retention]], [free_lifetime]); and at a safepoint no object is freed or reclaimed ([collector_live]), so nothing the program can still name goes ([rooting], a lemma from it). Every theorem holds for any runtime that satisfies them.

## Safepoints

A concurrent collector has to know where every live pointer is, including pointers that sit only in registers. Fil-C solves this with safepoints ([[poll|pollchecks]]). These are points where the compiler guarantees that every live lower is recorded in the function's Pizderson frame, a small [[root|root]] record on the stack. Only at those points does a thread answer the collector.

The compiler puts a pollcheck on every back edge of the control-flow graph, so no loop can run without reaching one. A pollcheck costs one load and one branch on the thread's state word. When the collector wants something done, such as scanning stacks or flushing allocation caches, it sets a bit there and waits for every thread to do it at its next pollcheck: a soft handshake. A thread about to block in a system call first *exits*, and while it is out the collector does the thread's handshake work itself. Signals are handled the same way: the runtime defers a signal to the next pollcheck, so a signal handler runs at a known point and may allocate ([safepoints](https://fil-c.org/safepoints)).

Safepoints are also what make an ordinary load safe. Between a pointer load and the next pollcheck the collector cannot finish a cycle, so the loaded pointer's object stays valid without any barrier.

> In nanofil's IR a pollcheck is a poll edge, `poll(L)`. The validator demands one in every cycle (`ir:polls_every_cycle/1`, [polls_every_cycle]). Natively a safepoint is also where a signal handler the program installed runs, and it may free, so checks done before one prove nothing after it: no [[live-fact|live fact]] crosses a safepoint. In the model the runtime frees nothing at a safepoint ([collector_live]), and a handler is program code; installing one is a call to an external with no contract, which ends the run. The soundness theorem's one runtime hypothesis, [[spares]], covers the three exceptions, and every runtime meets it.

## Calls and linking

A function pointer is a flight pointer like any other. Its lower names a special function object, and a call checks that it really is a function. Fil-C also survives calls through the wrong type, too many or too few arguments, and a symbol defined as data in one file and used as a function in another. Each either panics or converts the bits in a defined way.

The generic way to call does that safely and slowly. The caller copies its arguments, bytes and lowers, into two per-thread CC buffers. The callee reads back what its own signature expects, after checking that enough bytes were passed. Fil-C's [[fast-generic-convention|optimized calling convention]] avoids this in the common case. Every function object holds a fast entry that takes arguments in registers, a generic entry, and a 64-bit signature, an arithmetic encoding of its type. A call through a pointer compares signatures. When they match, it jumps straight to the fast entry with the arguments in registers. When they differ, a thunk translates through the generic convention ([calling convention](https://fil-c.org/calling_convention)). A variadic function's extra arguments end up in a read-only heap object that `va_arg` reads through an ordinary capability.

Linking is made safe the same way. Every symbol is renamed with a `pizlonated_` prefix and becomes a [[getter]], a function that returns the symbol's flight pointer, initializing the global on first use. Code that uses a global calls its getter and then checks the result like any pointer ([runtime, linking](https://fil-c.org/runtime#linking)).

> nanofil's backend emits both conventions (`filc_abi:signature/3`, `filc_amd64:fast_call//4`). The model follows the generic entry's argument conversions for calls through a pointer ([indirect_call_conv]). A [[getter]] call is a safepoint, so it ends every live fact, except a [[repeated-getter|repeated getter]], whose first call already returned.

## The runtime and the libc sandwich

Programs link against libpizlo.so, the Fil-C [[runtime]]. It holds the allocator, built on WebKit's libpas, along with FUGC, the safepoint machinery, threads, signals, exceptions, and a checked wrapper for every system call. The runtime is ordinary C, and it uses an ordinary libc to talk to the kernel. On top of it sits a second copy of the same libc, glibc or musl, compiled with Fil-C, and the program links against that copy. That is the libc sandwich ([runtime](https://fil-c.org/runtime)). When the program calls `read`, the Fil-C libc's code is checked like the program's, and the system call itself goes through a runtime wrapper that checks the buffer's capability before the kernel touches it.

> nanofil compiles only the program. Its calls into libc are [[external-call|external calls]]. The core model sends only `free` to the runtime and stops at any other external call. A later campaign describes libc functions by contracts, in ExternalCalls.v and Stdio.v.

## What makes it fast enough

Fil-C costs roughly 1.5 to 4 times the time of ordinary C, and much of the design exists to stay near the low end ([compiler](https://fil-c.org/compiler)):

- **Optimize first, then instrument.** Clang runs a short LLVM pipeline before FilPizlonator, Fil-C's pass, and the full pipeline after it. Locals become registers, functions inline, and redundant loads disappear while the code is still plain C.
- **Escape analysis.** Every local whose address is taken starts as a heap allocation, because a pointer to it may outlive the frame. Locals that never really escape go back on the stack.
- **Inline fast paths.** Allocation, pollchecks and most intrinsics are inlined. A pollcheck is one test and one branch.
- **Check scheduling.** Bounds checks are hoisted and merged, and checks that an earlier check already covers are removed. Fil-C's own documentation calls this the area with the most room left.
- **Calls without checks.** Matching signatures take the register convention. A direct call to a known function skips the getter, the function check and the signature check entirely.
- **A collector that stays out of the way.** No load barrier, a store barrier that does work only while marking, black allocation during a cycle, and sweeping by bitvector SIMD.

> Check removal is where nanofil does most of its own work, and where it differs from upstream: each removal is validated, and the model proves the validator sound. [[reuse|Reuse]] drops a check that an earlier [[live-fact|live]] one covers. [[renew|Renew]] keeps an earlier check's bounds and tests only what a free can change. [[check_ahead]] checks bytes early for accesses still to come, which may make a run trap early, through a [[doomed|doomed frame]]. A [[guard]] tests a loop's whole range once. Each has its own concept page.

## What it does not promise

Fil-C makes memory errors deterministic panics. It does not make a program correct. Integer overflow is not caught, logic bugs remain, and a panic still ends the process, which may itself be a denial of service. Data races between threads are allowed, and a racy program may compute garbage, but it cannot corrupt a capability. Code compiled without Fil-C cannot be linked in, so a whole system needs a Fil-C userland. Filnix packages exactly that. Last, the guarantee is only as good as the compiler and runtime: the parts that must be trusted are the compiler, the runtime and the kernel.

> That last point is what nanofil's Rocq model is for. It does not cover FilPizlonator. It covers nanofil's own pass and validator: it proves that a validated program never makes an unchecked access, assuming the runtime axioms above. [Panics.v](../rocq/theories/Panics.v) states the next goal, that a particular program never panics ([never_panics]).
