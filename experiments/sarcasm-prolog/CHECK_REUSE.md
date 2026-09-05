# Check reuse investigation

The prototype can describe and independently validate reuse of an earlier
covering read. This is an **advisory analysis**: `--emit-checks` prints its
certificates, and `--verify-checks` runs it before ordinary emission. Neither
changes generated C. Every access remains subject to Fil-C instrumentation.

```sh
nix run .#sarcasm-prolog -- --emit-checks experiments/sarcasm-prolog/examples/checks.s
nix run .#sarcasm-prolog -- --verify-checks --emit-c experiments/sarcasm-prolog/examples/checks.s
```

## Obligations and validity

`check-model.pl` describes the normal continuation of each checked access:

```prolog
protection(value(P), capability(P), index(I, Scale),
           range(Start, ExclusiveEnd), permission(read),
           alignment(1), kind(integer))
```

The value and capability identities belong to the same typed pointer.
Identical address bits with a different capability cannot satisfy this
obligation. Index identities include their integer width; edge pullback
canonicalizes nested views and constants without guessing arithmetic
equalities. Ranges must be nonempty, nonnegative and representable within
`PTRDIFF_MAX`. Permission, alignment and access kind remain separate.

A certificate names the target access, an earlier covering read, and every
intervening operation. At a block entry it enumerates **all** incoming
edges, translates the requirement through each edge's actual simultaneous
assignments, and supplies a proof for each predecessor. Each path must end
at the named witness. A read on only one arm of a diamond is insufficient.

Ordinary integer reads can establish reusable facts. Integer arithmetic and
flag computations preserve them. Stores, pointer copies/derivations,
pointer loads/stores and unknown operations invalidate them. Unknown effects
include any future calls, frees, safepoints or concurrent mutation. Every
edge belonging to a directed cycle is also a barrier: Fil-C can insert
polling while transforming a loop, independently of source instructions.
Local reuse within one iteration is still possible. This policy is deliberately
more conservative than the compiler's per-fact invalidation rules.

Each proposal carries `retained_offset_guard(Target)`. Even an earlier
covering range does not authorize deleting the later effective-offset
overflow and `PTRDIFF_MAX` guards. This analysis neither widens a read nor
introduces an earlier check. Adjacent-read grouping remains a separate
transformation with its documented allowance for earlier faults.

`check-reuse.pl` performs a bounded backward witness search. Rejection is
explicit data; backtracking cannot refund consumed search steps. Exhaustion
or an exception aborts analysis without returning a partial report. Cyclic
edges terminate the search conservatively. `check-validator.pl` follows the
supplied certificate and checks local obligations; it does not enumerate
witnesses or call the optimizer's coverage predicate. The instruction-effect
model and the already-validated typed graph remain trusted inputs.

Trealla tabling adds no useful capability to this finite, bounded search,
so this milestone does not adopt it. Any future tabled solver still needs
explicit completeness/error reporting and comparison with a terminating
reference on cycles, exceptions, resource limits and partial answers. A
caught worker error cannot be interpreted as an empty complete answer set.

## A source witness is not a machine witness

The certificate is conditional on the modeled checked read succeeding.
LLVM may eliminate that read before Fil-C instruments accesses. A source
certificate therefore does **not** prove that a retained machine guard ran.
A future backend consuming certificates to remove checks would also need
to retain or validate the actual machine witness and its validity interval.
No unchecked primitive or such backend is introduced here.

The pinned compiler already performs forward check propagation and optional
backward scheduling in
[`FilPizlonator.cpp`](https://github.com/pizlonator/fil-c/blob/4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp).
`removeRedundantChecksUsingForwardAI` merges facts at successors. Calls and
backedge polling invalidate lifetime and auxiliary-pointer facts; stores
invalidate selected auxiliary-pointer facts. Bounds, liveness, alignment
and write permission are distinct checks.

## Reproducible compiler probes

`protection-probe.py` compiles small C fixtures in three modes, runs their
valid cases and a free-during-call failure, and retains assembly plus
`metrics.json`. These standalone C probes use volatile reads and calls to
isolate compiler behavior; those constructs are not additions to the
accepted assembly subset.

Pinned compiler/runtime revision:
`4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c`. Compiler:
`/nix/store/x2i9jyjvpnngn0yq5kbdlrw4gg43wzm3-filc-cc-wrapper-/bin/clang`.
All probes use `-O2`; assembly uses `-fno-addrsig`. The alternate modes use
`-mllvm -filc-propagate-checks-backward=false` or
`-mllvm -filc-optimize-checks=false`. The latter disables check optimization,
not protection: the post-call invalid access still fails in every mode.

The metric below counts **static conditional branches targeting compiler-
labelled access-failure blocks**. It does not count source loads, logical
check groups, dynamic checks or custom `zcheck_readonly` diagnostic guards.

| C probe | Default | Forward only | Check optimization disabled |
|---|---:|---:|---:|
| Wide read, arithmetic, covered byte | 3 | 3 | 3 |
| Wide read before diamond, covered byte after join | 3 | 3 | 3 |
| Wide read on only one arm | 6 | 6 | 6 |
| Explicit `zcheck_readonly(p,8)`, indexed byte | 3 | 3 | 3 |
| Wide read, byte store, covered byte | 4 | 4 | 6 |
| Wide read, retained volatile covered byte | 3 | 3 | 5 |
| Wide read, opaque call, covered byte | 4 | 4 | 5 |

For the first probe, ordinary LLVM optimization replaces the byte read with
an extraction from the wide value even when Fil-C check optimization is
disabled. The volatile probe keeps both data reads and demonstrates actual
check reuse: the later byte needs no additional guard in the default mode.
After the opaque call, an extra freed-object test protects the later read;
the runtime fixture verifies this by actually freeing the object in that
call. Counts for the one-arm probe span different paths, rather than six
checks on every invocation. The explicit `zcheck_readonly` probe retains
three later access-failure branches **in addition to** its own diagnostics;
it is not a useful source-level check-elision mechanism in this example.

The seven assembly fixtures separately exercise same-block coverage, a
dominating witness through both diamond arms, a check on only one arm,
stores, changed indices, cycles, and local reuse inside a loop. They produce
three certificates in total. Both grouping modes agree with native assembly
and a bytewise reference on 14,336 complete return/buffer cases per variant.
A last-byte read on the unchecked arm succeeds even when a hoisted wide
check would fail. Eight failure modes per variant cover null/freed objects,
conditional bounds, read-only storage, overflow and a later loop iteration.

Mutation tests alter actual witness widths as well as certificate fields,
omit predecessors, change edge inputs and permissions, and insert honest
records of invalidating effects. Zero-budget, partial-prefix and exception
tests require no report to escape. The Nix check runs all of this and
compares C output with and without analysis byte for byte.

The evidence supports keeping check removal in Fil-C. The prototype now
has explicit, reviewable proof obligations without duplicating its runtime
check scheduler. Generated-code improvements should first target the
ordinary value IR and be evaluated separately from memory protection.
