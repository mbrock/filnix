# The bounded decoder slice

`examples/decoder.s` translates a stream of byte indices through a 64-entry
table. Each entry holds four output bytes, loaded as two little-endian
halfwords. It is a small substitution decoder that exercises input reads,
indexed table reads, stores, conditional exits and loop-carried pointers.
It is not a zstd or Huffman decoder.

## Interface and observable behavior

`tiny_decode(state, bound)` takes the usual pointer/integer signature. The
state layout is:

| Offset | Field |
|---|---|
| 0 | Pointer to the first table entry |
| 8 | Current input pointer |
| 16 | Current output pointer |
| 24 | Unsigned 64-bit count consumed by this invocation |

The first three fields are typed pointer slots. State must occupy a
separate, writable object; table, input and output may overlap each other.
No concurrent mutation, volatile or atomic accesses are modeled.

For each of at most `bound` input bytes, an index in 0..63 selects an entry.
The decoder reads the whole entry before writing its four output bytes,
then advances input by one and output by four. An index outside 0..63 ends
decoding before consuming that byte or reading its table entry. Return 0
means the bound was reached; return 1 means an invalid index was encountered.
Both exits write back the final pointers and consumed count. The table
pointer remains unchanged.

A zero bound reads and writes state but touches no table/input/output data,
so null data pointers are allowed in that case. Likewise, an invalid first
index does not dereference table or output. Cursor pointers may be saved
one past the last byte written/read. The test caller exercises their
capabilities when later dereferences are within the allocation.

Invalid memory still traps through Fil-C. Earlier iterations can already
have written output when a later access fails; state writeback happens only
on a normal exit. No transactional rollback is promised. Read grouping has
the trap-timing contract in [SEMANTICS.md](SEMANTICS.md).

The unsigned counter starts at zero and stops when it reaches `bound`, so
it cannot wrap before that exit. This fixture is bounded even though the
translator also accepts source programs with nonterminating loops. Compiler
analysis termination is a separate property of the finite dataflow domain.

`examples/loops.s` supplies a second fixture: `loop_walk(node, bound)` sums
64-bit node values for exactly the requested number of steps. A node holds
a next pointer at offset 0 and a value at offset 8. Nodes may form a cycle.
The next pointer is loaded with pointer semantics and becomes the pointer
used by the next iteration, exercising changes of capability identity.

## Tests

`decoder-runtime.c` contains a bytewise C oracle. Native source assembly,
grouped translation and ungrouped translation agree on status, consumed
count, final pointer positions and complete table/arena contents. There are
10,240 deterministic cases per variant, including unaligned addresses and
five layouts: separate buffers, output at input, output one byte ahead,
output three bytes behind, and output overlapping the table. Invalid
symbols are mixed with valid data; aliasing may change future input or table
entries and must affect later iterations in program order.

Separate cases reach the exact input/output allocation ends and the last
table entry, or perform zero iterations with null data pointers. The node
walk covers 520 start/count combinations per variant over eight separately
allocated nodes. Nineteen runtime failures cover null/freed data, later
iteration bounds, a partial table entry, read-only output/state, short
state, aliasing beyond bounds and invalid pointers loaded on a backedge.
One case changes a next pointer's address to a real earlier node while
retaining another node's capability; the later access must fail.

Another 55 native differential programs test counter/countdown loops,
backedges to function entry, pointer swaps, multiple backedges, nested loops,
a cycle with two entry points, and stores that overlap future reads. Each variant compares 14,080 exact
return/full-buffer outcomes. Execution has timeouts. Prolog tests also
reject missing first-iteration values, undefined flags from a backedge,
conflicting pointer/integer types, and corrupted dataflow certificates.

## Initial assembly inspection

Inspected with the pinned Fil-C compiler at
`/nix/store/x2i9jyjvpnngn0yq5kbdlrw4gg43wzm3-filc-cc-wrapper-`, using the
wrapper's `-O2 -fno-addrsig` lowering. The Nix check retains `decoder.c`,
`decoder-separate.c`, `decoder.s`, `decoder-plain.s`, `loops.s` and
`loops-plain.s` for reproduction. This is an inspection, not a benchmark.

- Grouping produces one 32-bit table load and one covering table-range
  check. The ungrouped version has two 16-bit loads and checks the two
  halfword ranges separately. Input and output retain their own checks.
- Neither decoder variant calls the flag helper. Typed block parameters
  and edge copies disappear into the compiler's value/register handling.
  However, the source unsigned comparison against 63 becomes a comparison
  against 62 followed, on one path, by a comparison against 63. The explicit
  CF/ZF formula is a concrete opportunity to improve condition lowering.
- Both decoder variants reserve 152 bytes of local stack space in addition
  to saved registers. Input and table bases are reloaded from stack in the
  normal loop. Capability roots are also written for GC. These costs are
  not eliminated by source-level read grouping.
- The normal loop tests Fil-C's polling state and can call
  `filc_pollcheck_slow`. Other calls belong to access-failure paths or to
  pointer-state writeback barriers/metadata allocation after the loop.
  There is no unconditional per-iteration helper call on the fast path.
- The node walk reserves 40 bytes of local stack space. Fil-C combines
  protection for the value and next-pointer slot into a 16-byte range/alignment
  check even though the Prolog read planner does not merge pointer accesses.
  Loading the next pointer also loads its capability metadata. GC polling
  remains in the loop.

These findings guide milestones 5–6: distinguish a source proof from actual
machine-check elimination, inspect existing compiler reuse, and investigate
condition lowering and register pressure before considering a direct backend.
