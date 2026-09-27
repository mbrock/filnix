# Data race: parallel evaluation mutates a failed thunk's shared exception

**Affects:** Determinate Nix 3.22.5 (nix-src v3.22.5, based on Nix 2.35.2)
with `eval-cores` > 1. `builtins.parallel` is not needed: plain
`nix eval --json` triggers it too.

**Impact:** an unsynchronized `std::list::push_front` from several evaluator
threads on one exception object. Natively it corrupts the list's links and
silently drops trace entries. Under a memory-safe build (Fil-C) it is an
out-of-bounds write. ThreadSanitizer reports it directly.

## Cause

When a thunk's evaluation throws, `ValueStorage::force`
(`src/libexpr/include/nix/expr/eval-inline.hh`) memoizes the failure:

```c++
} catch (...) {
    state.tryFixupBlackHolePos((Value &) *this, pos);
    setStorage(new Value::Failed{.ex = std::current_exception()});
    throw;
}
...
done:
    if (InternalType(p0_ & 0xff) == tFailed)
        std::rethrow_exception((std::bit_cast<Failed *>(p1))->ex);
```

Every later forcing of the value rethrows **the same exception object**
(`std::rethrow_exception` does not copy it with libstdc++ or libc++). On the
way up, catch sites decorate the exception in place. For example,
`EvalState::callFunction` does `addErrorTrace(e, pos, "while calling the '%1%'
builtin", ...)`, and `forceInt`, `evalBool` and friends do
`e.addTrace(positions[pos], errorCtx)`. `BaseError::addTrace` is
`err.traces.push_front(...)` on a `std::list<Trace>` inside the shared object.

With several evaluator threads, each worker that reaches the failed thunk
runs `push_front` on the same list at the same time. The thread that first
threw also keeps decorating it while the others already rethrow it.
`CloneableError::throwClone()`, documented as "Useful when the exception can
get modified when appending traces", exists but has no callers.

## Reproducer

`race3.nix`:

```nix
{ n ? 20000 }:
let
  bad = builtins.throw "shared failure";
  xs = builtins.genList (i: builtins.tryEval (builtins.add bad i)) n;
  failures = builtins.length (builtins.filter (r: !r.success) xs);
in
builtins.parallel xs (builtins.seq failures (builtins.sub 0 bad))
```

```sh
nix eval --extra-experimental-features parallel-eval --option eval-cores 8 \
  --show-trace --impure --expr 'import ./race3.nix {}'
```

Without `builtins.parallel`, using `nix eval --json`'s parallel forcing
(`race.nix`):

```nix
{ n ? 5000 }:
let
  bad = builtins.throw "shared failure";
in
builtins.listToAttrs (builtins.genList (i: {
  name = "a${toString i}";
  value = { x = builtins.add bad i; y = builtins.sub i bad; };
}) n)
```

```sh
nix eval --option eval-cores 8 --json --impure --expr 'import ./race.nix {}'
```

## Evidence

### Native build: lost updates

The final error's trace shows every frame that any forcing prepended to the
shared exception, summarized as "(N duplicate frames omitted)". Single
threaded, the count is exact. With 8 threads, updates are lost:

| eval-cores | "duplicate frames omitted" (race3.nix, n = 20000) |
| --- | --- |
| 1 | 19999, 19999 |
| 8 | 19823, 19792, 19744, 19628, 19790 |

That is 150 to 370 `push_front`s lost per run. Nothing crashed in 20 native
runs with n = 50000, so the corruption is silent.

### ThreadSanitizer

A native build of the same source with Nix's `withTSan` knob (GCC 15,
`enableGC = false`) reports races in `BaseError::addTrace` for both
reproducers. The memory is the exception allocated by `primop_throw`:

```
WARNING: ThreadSanitizer: data race (pid=323174)
  Write of size 8 at 0x725000010190 by thread T10:
    #0 nix::BaseError::addTrace(std::shared_ptr<nix::Pos const>&&, nix::HintFmt, nix::TracePrint) (libnixutil.so+0x112ade)
    #1 void nix::EvalState::addErrorTrace<char [17], std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> > >(nix::Error&, nix::PosIdx, char cons
    #2 nix::EvalState::callFunction(nix::Value&, std::span<nix::Value*, 18446744073709551615ul>, nix::Value&, nix::PosIdx) (libnixexpr.so+0x63013)
    #3 nix::ExprCall::eval(nix::EvalState&, nix::Env&, nix::Value&) (libnixexpr.so+0x11f995)
    #4 nix::ValueStorage<8ul, void>::force(nix::EvalState&, nix::PosIdx) (libnixexpr.so+0x1e19f5)
    #5 nix::prim_tryEval(nix::EvalState&, nix::PosIdx, nix::Value**, nix::Value&) (libnixexpr.so+0x165650)
    #6 std::_Function_handler<void (nix::EvalState&, nix::PosIdx, nix::Value**, nix::Value&), void (*)(nix::EvalState&, nix::PosIdx, nix::Value**, nix::Value&)>::_M_invok
    #7 nix::EvalState::callFunction(nix::Value&, std::span<nix::Value*, 18446744073709551615ul>, nix::Value&, nix::PosIdx) (libnixexpr.so+0x11deca)
    #8 nix::ExprCall::eval(nix::EvalState&, nix::Env&, nix::Value&) (libnixexpr.so+0x11f995)
    #9 nix::EvalState::callFunction(nix::Value&, std::span<nix::Value*, 18446744073709551615ul>, nix::Value&, nix::PosIdx) (libnixexpr.so+0x11c880)
    #10 nix::ValueStorage<8ul, void>::force(nix::EvalState&, nix::PosIdx) (libnixexpr.so+0x1e1a65)
    #11 void std::move_only_function<void ()>::_S_invoke<nix::EvalState::makeWork<nix::prim_parallel(nix::EvalState&, nix::PosIdx, nix::Value**, nix::Value&)::{lambda()#1
    #12 nix::Executor::worker() (libnixexpr.so+0x155f8d)
    #13 boost::detail::thread_data<nix::Executor::createWorker(nix::Executor::State&)::{lambda()#1}>::run() (libnixexpr.so+0x2d771c)
    #14 thread_proxy (libboost_thread.so.1.89.0+0xccf6)
  Previous write of size 8 at 0x725000010190 by thread T4:
    #0 nix::BaseError::addTrace(std::shared_ptr<nix::Pos const>&&, nix::HintFmt, nix::TracePrint) (libnixutil.so+0x112ade)
    #1 void nix::EvalState::addErrorTrace<char [17], std::__cxx11::basic_string<char, std::char_traits<char>, std::allocator<char> > >(nix::Error&, nix::PosIdx, char cons
    #2 nix::EvalState::callFunction(nix::Value&, std::span<nix::Value*, 18446744073709551615ul>, nix::Value&, nix::PosIdx) (libnixexpr.so+0x63013)
    #3 nix::ExprCall::eval(nix::EvalState&, nix::Env&, nix::Value&) (libnixexpr.so+0x11f995)
    #4 nix::ValueStorage<8ul, void>::force(nix::EvalState&, nix::PosIdx) (libnixexpr.so+0x1e19f5)
    #5 nix::prim_tryEval(nix::EvalState&, nix::PosIdx, nix::Value**, nix::Value&) (libnixexpr.so+0x165650)
    #6 std::_Function_handler<void (nix::EvalState&, nix::PosIdx, nix::Value**, nix::Value&), void (*)(nix::EvalState&, nix::PosIdx, nix::Value**, nix::Value&)>::_M_invok
    #7 nix::EvalState::callFunction(nix::Value&, std::span<nix::Value*, 18446744073709551615ul>, nix::Value&, nix::PosIdx) (libnixexpr.so+0x11deca)
    #8 nix::ExprCall::eval(nix::EvalState&, nix::Env&, nix::Value&) (libnixexpr.so+0x11f995)
    #9 nix::EvalState::callFunction(nix::Value&, std::span<nix::Value*, 18446744073709551615ul>, nix::Value&, nix::PosIdx) (libnixexpr.so+0x11c880)
    #10 nix::ValueStorage<8ul, void>::force(nix::EvalState&, nix::PosIdx) (libnixexpr.so+0x1e1a65)
    #11 void std::move_only_function<void ()>::_S_invoke<nix::EvalState::makeWork<nix::prim_parallel(nix::EvalState&, nix::PosIdx, nix::Value**, nix::Value&)::{lambda()#1
    #12 nix::Executor::worker() (libnixexpr.so+0x155f8d)
    #13 boost::detail::thread_data<nix::Executor::createWorker(nix::Executor::State&)::{lambda()#1}>::run() (libnixexpr.so+0x2d771c)
    #14 thread_proxy (libboost_thread.so.1.89.0+0xccf6)
  Location is heap block of size 512 at 0x725000010000 allocated by thread T4:
    #0 malloc (libtsan.so.2+0x8a9ac)
    #1 __cxa_allocate_exception (libstdc++.so.6+0xc40c3)
    #2 std::_Function_handler<void (nix::EvalState&, nix::PosIdx, nix::Value**, nix::Value&), nix::primop_throw::{lambda(nix::EvalState&, nix::PosIdx, nix::Value**, nix::
    #3 nix::EvalState::callFunction(nix::Value&, std::span<nix::Value*, 18446744073709551615ul>, nix::Value&, nix::PosIdx) (libnixexpr.so+0x11deca)
    #4 nix::ExprCall::eval(nix::EvalState&, nix::Env&, nix::Value&) (libnixexpr.so+0x11f995)
    #5 nix::ValueStorage<8ul, void>::force(nix::EvalState&, nix::PosIdx) (libnixexpr.so+0x1e19f5)
```

(TSan separately reports `prim_tryEval`'s `MaintainCount
trylevel(state.trylevel)`: a plain `int` changed by all threads. Only the
debugger reads it, and the debugger turns parallel evaluation off, so that
one is harmless but noisy.)

### Fil-C (memory-safe C/C++) build

Built with [Fil-C](https://github.com/pizlonator/fil-c) (see
[mbrock/filnix](https://github.com/mbrock/filnix), `docs/determinate-nix.md`),
race3.nix stopped in every run (4 of 4), with `ptr >= upper` or `ptr < lower`.
The same happens with race.nix and plain `nix eval --json --option eval-cores 8`:

```
filc safety error: cannot write pointer with ptr < lower.
    pointer: 0x7fb876ceb910,0x7fb87774e210,0x7fb87774e300,aux=0x7fb8768dc500
    expected 8 writable bytes with ptr aligned to 8 bytes.
semantic origin:
    (libnixutil.so) filc-libcxx-git/include/c++/list:969:26: std::__1::list<nix::Trace, allocator>::__link_nodes_at_front(std::__1::__list_node_base<nix::Trace,
    (libnixutil.so) filc-libcxx-git/include/c++/list:1247:3: std::__1::list<nix::Trace, allocator>::push_front(nix::Trace&&) (inlined)
    (libnixutil.so) ../error.cc:32:16: nix::BaseError::addTrace(std::__1::shared_ptr<nix::Pos const>&&, nix::HintFmt, nix::TracePrint)
check scheduled at:
    (libnixexpr.so) ../eval.cc:898:7: void nix::EvalState::addErrorTrace<char [32], std::__1::basic_string<char, std::__1::char_traits<char>
    (libnixexpr.so) ../eval.cc:1746:25: nix::EvalState::callFunction(nix::Value&, std::__1::span<nix::Value*, 18446744073709551615ul>, nix::
    (libnixexpr.so) ../eval.cc:1853:11: nix::ExprCall::eval(...)
    (nix) determinate-nix-expr-x86_64-unknown-linux-gnufilc0-3.22.5+5-dev/include/nix/expr/eval-inline.hh:142:23: nix::ValueStorage<8ul, voi
    (libnixexpr.so) ../primops.cc:1207:15: nix::prim_tryEval(...)
    (libnixexpr.so) ../eval.cc:1743:21: nix::EvalState::callFunction(nix::Value&, std::__1::span<nix::Value*, 18446744073709551615ul>, nix::
    (libnixexpr.so) ../eval.cc:1853:11: nix::ExprCall::eval(...)
[pid] filc panic: thwarted a futile attempt to violate memory safety.
```

## Proposed fix

Never modify a failed value's stored exception. Store a copy when the thunk
fails, because the thrower's own catch sites keep decorating the exception
in flight, and rethrow a fresh copy on every later forcing. All `BaseError`
subclasses are `CloneableError`s, so `throwClone()` keeps the dynamic type.
`tryEval` still catches `ThrownError` and `AssertionError`.

The suite already states the intended behaviour, and its expected output
contradicts it. `tests/functional/lang/eval-fail-memoised-error-trace-not-mutated.nix`
(also in upstream Nix since 2.34) says:

```nix
let
  a = throw "nope";
  b = builtins.addErrorContext "forcing b" a;
  c = builtins.addErrorContext "forcing c" a;
  d = builtins.addErrorContext "forcing d" a;
in
# Since nix 2.34 errors are memoised. Trying to eval a failed thunk includes
# the trace from when it was first forced. When forcing a failed value it gets
# a fresh instance of the exceptions to avoid trace mutation.
builtins.seq (builtins.tryEval b) (builtins.seq (builtins.tryEval c) d)
```

Its `.err.exp` expects d's error to show `forcing d`, `forcing c` *and*
`forcing b`. That output is the mutation the test's name and comment rule
out: b's and c's contexts were prepended to the one stored exception. With
the patch, d's error shows only `forcing d` above the `throw`, and the patch
updates that expected output.

A stored exception can't keep "the trace from when it was first forced" in
full without a race. The first thrower's outer frames are added after other
threads can already see the stored value, so the patch keeps the trace up to
the failing thunk.

```diff
diff --git a/src/libexpr/include/nix/expr/eval-inline.hh b/src/libexpr/include/nix/expr/eval-inline.hh
index 6d43911..45ba8fc 100644
--- a/src/libexpr/include/nix/expr/eval-inline.hh
+++ b/src/libexpr/include/nix/expr/eval-inline.hh
@@ -143,7 +143,22 @@ void ValueStorage<ptrSize, std::enable_if_t<detail::useBitPackedValueStorage<ptr
             }
         } catch (...) {
             state.tryFixupBlackHolePos((Value &) *this, pos);
-            setStorage(new Value::Failed{.ex = std::current_exception()});
+            /* Store a copy: this thread's catch sites keep prepending
+               traces to the exception in flight, while other threads may
+               already be rethrowing the stored one. */
+            std::exception_ptr ex;
+            try {
+                throw;
+            } catch (BaseError & e) {
+                try {
+                    e.throwClone();
+                } catch (...) {
+                    ex = std::current_exception();
+                }
+            } catch (...) {
+                ex = std::current_exception();
+            }
+            setStorage(new Value::Failed{.ex = ex});
             throw;
         }
     }
@@ -152,8 +167,17 @@ void ValueStorage<ptrSize, std::enable_if_t<detail::useBitPackedValueStorage<ptr
         p0_ = waitOnThunk(state, p0_);
 
 done:
-    if (InternalType(p0_ & 0xff) == tFailed)
-        std::rethrow_exception((std::bit_cast<Failed *>(p1))->ex);
+    if (InternalType(p0_ & 0xff) == tFailed) {
+        /* The stored failure is shared by every thread (and every later
+           forcing) that reaches this value, but catch sites prepend traces
+           to the exception in flight. Throw a copy so that nobody modifies
+           the shared one. */
+        try {
+            std::rethrow_exception((std::bit_cast<Failed *>(p1))->ex);
+        } catch (BaseError & e) {
+            e.throwClone();
+        }
+    }
 }
 
 [[gnu::always_inline]]
diff --git a/tests/functional/lang/eval-fail-memoised-error-trace-not-mutated.err.exp b/tests/functional/lang/eval-fail-memoised-error-trace-not-mutated.err.exp
index 9327371..5482d91 100644
--- a/tests/functional/lang/eval-fail-memoised-error-trace-not-mutated.err.exp
+++ b/tests/functional/lang/eval-fail-memoised-error-trace-not-mutated.err.exp
@@ -15,10 +15,6 @@ error:
 
        … forcing d
 
-       … forcing c
-
-       … forcing b
-
        … while calling the 'throw' builtin
          at /pwd/lang/eval-fail-memoised-error-trace-not-mutated.nix:2:7:
             1| let
```

Checked with native builds of v3.22.5 plus this patch:

- race3.nix gives the same short trace with eval-cores 1 and 8, and no
  "duplicate frames omitted".
- A TSan build reports no `addTrace` races for race3.nix or race.nix (two
  runs each). Only the `trylevel` race above remains.
- Native functional suite: 212 ok, 10 skipped, and `lang` passes with the
  updated expected output. The one failure, `gc-closure`, died of SIGPIPE
  in the test script itself: `printf %s "$input2" | head -n1` under
  `pipefail`, a harness race, not in Nix. It passes in the unpatched run.
  Without the `.err.exp` change, the only failure is
  `eval-fail-memoised-error-trace-not-mutated`.
- A side effect, also relevant to upstream Nix 2.35, which has `Failed`
  values too: errors no longer carry frames from unrelated earlier forcings.
  Before the patch, this prints "while calling the 'add' builtin" for the
  `sub` failure, in both Nix 2.35.2 and Determinate Nix:

  ```nix
  let
    bad = throw "boom";
    first = builtins.tryEval (builtins.add bad 1);
  in builtins.seq first (builtins.sub bad 2)
  ```
