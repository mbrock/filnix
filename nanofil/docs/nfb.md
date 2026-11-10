# RFC draft: a bytecode for nanofil IR

Nov 10, 2026 · @Mikael Brockman

> This is Mikael Brockman's draft, kept as he wrote it. Where the
> implementation departs from it or fills in what it left open, a
> quoted note marked **Changed in the implementation** says so beside
> the text it changes, and the [assigned numbers](#appendix-assigned-numbers)
> at the end record every opcode, code and packing. The Prolog encoder
> and decoder are [nfb.pl](../src/nfb.pl), with `nanofil encode`,
> `nanofil decode` and the corpus gate `tests/nfb.sh`.

## Summary

This proposes **NFB**, a binary encoding of a nanofil IR module: the same `module(Items)` that `ir.pl` defines, written as a stream of little-endian 32-bit words inside a small sectioned container.

NFB is a faithful encoding of the term form, not a new IR. Every module that `valid_module/1` accepts has exactly one NFB encoding, in either stage (unchecked or checked) and either mode (plain or filc). Decoding gives back the module, up to the names of temporaries, labels and locals.

Status: a draft for discussion. Opcode numbers and section ids are provisional. Nothing here is implemented.

> **Changed in the implementation (Nov 10, 2026).** The Prolog side is implemented: [nfb.pl](../src/nfb.pl), the
commands `encode FILE OUT` and `decode FILE`, and the gate
`tests/nfb.sh`, which round-trips every module of the corpus, unchecked
and checked, with and without `-O`. The Gallina side is in the
backend project: `rocq/backend/NfbTerm.v` reads and writes module terms
by the same table, and `rocq/backend/Nfb.v` gives `encode` and `decode`
over Syntax.v's modules, through IrTerm.v's encoders and Transport.v's
`decode_module`. `rocq/backend/tests/nfb.sh` holds the two to the same
bytes on the corpus, NAMES included, and the Gallina reader to the same
module. The Gallina reader keeps a string's bytes as they are; the
Prolog one also requires them to be UTF-8. The numbers are still
provisional (major version 0).

## Motivation

The IR's only concrete form today is Prolog canonical terms. That was the right choice while every producer and consumer was Prolog. Four things now pull toward a binary form.

- **A wire format for the library.** The Gallina backend campaign ends in `libnanofil`, a Fil-C library that a program hands IR at run time. The regex compiler is the first client. Today it prints terms that a Prolog process reads.
- **Decode cost.** In the Rocq model a name is a ground term, compared structurally, and every table is a map keyed by hashed names. `Maps.v` records that the validator was thirty times slower before its buckets were keyed by integers. A format with dense integer ids removes names from the hot path altogether.
- **Identity.** The regex cache keys a shared object by a hash of printed term text. A format with one encoding per module makes the bytes themselves the identity.
- **A small proved reader.** A reader of untrusted input should be short, total and proved. A hand-written term parser in OCaml is none of these. The plan already says M4 replaces it with a Gallina one.

## Goals and non-goals

Goals:

1. **Faithful.** It encodes exactly the grammar of `ir.pl`. No construct is added, dropped or reinterpreted.
2. **One encoding per module.** The encoder is a function, and the decoder accepts only its image.
3. **Linear to read.** One forward pass, no recursion on input depth, memory proportional to the input.
4. **Dense ids.** Temporaries, blocks, locals and symbols are small integers, so a consumer can use arrays where the model uses maps.
5. **Provable.** The format is simple enough that encoder and decoder are short Gallina functions with an inverse theorem.
6. **Easy to produce.** A client in C can write a module with a header-only helper and no library.

Non-goals:

- **Compactness.** A regex function is a few kilobytes. Stored modules can be compressed outside the format.
- **A stable public ABI.** The format follows the IR, and the IR still changes.
- **Replacing the term form.** Terms stay the form people read, the docs typeset and Prolog computes on.
- **Carrying native code.** Embedding NFB in an object file is discussed under Open questions, not specified.

## Design overview

Five decisions shape everything else.

- **Container: sections with lengths, as in WebAssembly.** A header, then sections, each an id and a length in words. A reader can skip a section it does not need.
- **Body: a flat word stream, as in SPIR-V.** Every instruction begins with a word holding its opcode and its length. Nothing is nested, so nothing is parsed recursively.
- **Ids are implicit and dense.** A temporary's id is its position among the function's definitions: parameters first, then each defining instruction in stream order. Blocks are numbered in stream order, and so are named locals. A definition never names its result, so two definitions of one temporary cannot be written.

> **Changed in the implementation (Nov 10, 2026).** ir.pl's IR is not strict SSA: a temporary may be defined
more than once (`tests/fixtures/memory.ir`, and five other corpus files,
test the validator on it), so "cannot be written" would make NFB
unfaithful. A temporary's id is its place among *first* definitions. An
instruction that defines a temporary again is preceded by a **rebind**
word (opcode 1): its length counts one word per temporary the
instruction defines, 0 for a first definition and the id plus one for a
redefinition. It is written only when one of those words is nonzero, so
the encoding stays a function of the module. A strict-SSA producer never
writes one.
- **Phis stay phis.** The model, the semantics and the validator are about `phi(tmp(D), K, Pairs)`. NFB encodes that, and does not convert to block parameters.
- **Lists keep their order.** Where the term form has a list (items, blocks, phi pairs, call arguments), NFB writes it in the same order. Canonical form comes from the encoder being a function of the term, not from sorting.

One optional property, **ordered**, is declared by a header flag: blocks are in reverse postorder and every non-phi operand is defined earlier in the stream. A producer that can promise this lets a consumer compile in one pass.

> **Changed in the implementation (Nov 10, 2026).** the encoder sets the flag itself, exactly when rules 11 and
12 of Well-formedness hold, so it is part of the canonical form rather
than a producer's promise. Reverse postorder is not tested: rules 11 and
12 are what a one-pass consumer needs.

## Conventions

- **Word.** An unsigned 32-bit integer, stored little-endian. A file is a whole number of words. Every length in the format counts words.
- **`i64`.** A signed 64-bit integer as two words, low then high. Used for offsets, bounds and sizes (`Lo`, `Hi`, `Off`, `Size`).
- **Enumerations** (class, width, condition, rights, linkage and so on) take one word each. Their codes are listed where they are used. A value outside the list is an error.
- **String id.** An index into the STRINGS section.
- **Symbol id.** An index into the SYMBOLS section.
- **Block index.** A block's position in its function, entry block 0.
- **Temporary id.** Parameters take 0 to n-1 in order. Each later definition takes the next ids, in stream order. A phi, a `let`, a `flight`, a load from a local and a single call result define one. A tuple call result defines two. An `asm_fixed` defines one per output.
- **Local id.** Named locals are numbered by their `local_alloc`, in stream order. This is a separate numbering from temporaries, as the term form has a separate namespace.

Class codes:

| Code | Class | Code | Class |
| --- | --- | --- | --- |
| 0 | `void` (result positions only) | 5 | `x` |
| 1 | `w` | 6 | `p` |
| 2 | `l` | 7 | `a` |
| 3 | `s` | 8 | `f` |
| 4 | `d` |  |  |

### Operands

A value of the IR (`tmp`, `const` or `global`) is one **operand word**. Its low two bits are a tag, and the remaining 30 bits a payload.

| Tag | Payload | Term |
| --- | --- | --- |
| 0 | temporary id | `tmp(N)` |
| 1 | the constant itself, 0 to 2^30 - 1 | `const(N)` |
| 2 | index into CONSTANTS | `const(N)`, N at or above 2^30 |
| 3 | symbol id | `global(S)` |

A constant below 2^30 must be written inline. This leaves each constant one spelling.

> **Changed in the implementation (Nov 10, 2026).** the corpus has negative constants (`const(-1)`,
`const(-32768)`, a `-9223372036854775808` data item) and x87
constants above 2^64 (open question 4). So the inline payload of tag 1
is a signed 30-bit integer, from -2^29 to 2^29 - 1 in two's complement,
and tag 2 indexes a CONSTANTS entry for any other integer from -2^95 to
2^95 - 1. A constant inside the inline range must be written inline.

## Container

A file is a four-word header followed by sections.

| Word | Field | Value |
| --- | --- | --- |
| 0 | magic | `0x0042464E`, the bytes `N F B 0x00` |
| 1 | version | major in the high 16 bits, minor in the low 16; this draft is 0.1 |
| 2 | flags | bit 0: stage, 0 unchecked, 1 checked. Bit 1: mode, 0 plain, 1 filc. Bit 2: ordered. Other bits zero |
| 3 | section count | the number of sections that follow |

Each section is:

| Word | Field |
| --- | --- |
| 0 | section id |
| 1 | payload length in words |
| 2... | payload |

Sections appear in increasing id order, each id at most once. The file ends where the last section ends.

Ids below `0x100` are **core** sections. They define the module, and a reader rejects a core id it does not know. Ids from `0x100` up are **side** sections. They never change what the module means, a reader may skip them, and they are outside the module's identity.

The stage and mode flags restate what `module_stage/2` and `module_mode/2` derive from a module's vocabulary. A reader checks that they agree with the body.

## Sections

| Id | Name | Holds |
| --- | --- | --- |
| 1 | STRINGS | symbol names and `loc` file names |
| 2 | CONSTANTS | 64-bit constants too large for an operand word |
| 3 | SYMBOLS | every name the module defines or refers to |
| 4 | DATA | the `data/4` items |
| 5 | FUNCTIONS | the `func/5` items |
| 6 | CERTIFICATES | reserved; see Stages and evidence |
| 0x100 | NAMES | the original names of temporaries, labels and locals |
| 0x101 | CONTEXT | the `context/2` records |

An empty core section is omitted.

**STRINGS.** A count, then each string as a byte length followed by its bytes, padded with zero bytes to a word boundary. Strings are byte strings, not text: a symbol name is whatever the atom's character codes are. They are sorted by bytes, distinct, and each is used by a core section.

**CONSTANTS.** A count, then each constant as two words, low then high. Sorted ascending as unsigned 64-bit, distinct, each at or above 2^30, each used.

> **Changed in the implementation (Nov 10, 2026).** each constant is three words, low first, a signed 96-bit
integer in two's complement. They are sorted ascending as signed
integers, distinct, each outside the inline range and each used.

**SYMBOLS.** A count, then three words per symbol: name (string id), kind and linkage, and one extra word.

| Kind | Means | Linkage | Extra |
| --- | --- | --- | --- |
| 0 | function defined here | `export`, `local`, `weak` | 0 |
| 1 | data defined here | `export`, `local`, `ro(...)`, `tls(...)`, `weak`, `ro(weak)`, `init(...)`, `extern(weak)` | the priority of an `init` linkage, else 0 |
| 2 | alias | `export`, `weak` | the target's symbol id |
| 3 | named but not defined | none | 0 |

Defined symbols and aliases come first, in the order of the module's item list. Symbols that are only named follow, sorted by name. The item order matters because a backend emits in that order.

**DATA.** For each kind-1 symbol, in symbol order: the alignment, an item count, then the items.

| Item | Encoding after its kind word |
| --- | --- |
| `item(W, const(N))` | width, then N as two words |
| `item(b, str(Chars))` | byte length, then the bytes, padded |
| `item(l, sym(S, Off))`, `item(p, sym(S, Off))` | width, symbol id, `Off` as `i64` |
| `zero(N)` | N as two words |

> **Changed in the implementation (Nov 10, 2026).** each item starts with a kind word: 0 for
`item(W, const(N))`, 1 for `str`, 2 for `sym`, 3 for `zero`. A
constant item's N is a constant word, the operand form of tag 1 or 2,
since data items have the same negative and wide constants as code.

**FUNCTIONS.** For each kind-0 symbol, in symbol order: the body's length in words, then the body. The length lets a reader skip to any function, or hand functions to separate workers.

**NAMES.** For round trips with the term form: per function, the original name of each temporary, block and local, as term text. Without it a decoder invents names from the ids.

> **Changed in the implementation (Nov 10, 2026).** NAMES and CONTEXT hold terms, not their text, so a reader
needs no term parser. A side section starts with its own string pool,
in STRINGS's layout, of every atom and functor it uses. A term is a tag
word and its parts: 0 an integer (three words, as CONSTANTS), 1 an
atom (a pool id), 2 a compound (its functor's pool id, its arity, its
arguments), 3 a proper list (its length, its elements). NAMES then has,
per function in symbol order, three lists: its temporaries' names in id
order, its labels' and its locals'. Without NAMES a decoder names each
by its id, an integer: `tmp(0)`, block `0`.

**CONTEXT.** The module's `context/2` records as canonical term text. They are explanatory and no stage reads them.

> **Changed in the implementation (Nov 10, 2026).** CONTEXT is the pool, a count, then for each `context/2`
item the number of other items before it and the item itself, so that
the decoder puts it back where it stood.

## Function bodies

A body is a short header, then one stream of instructions.

| Field | Words | Notes |
| --- | --- | --- |
| return type | 1 | a class code, 0 for `void`; for `tuple([K1, K2])`, `0x100 + 16*K1 + K2` |
| parameter count | 1 |  |
| parameter classes | 1 each | `w`, `l`, `p`, `s` or `d` |
| block count | 1 | must equal the number of blocks in the stream |
| temporary count | 1 | must equal parameters plus definitions |
| local count | 1 | must equal the number of `local_alloc` |

The three counts let a consumer allocate its tables before reading the stream. A reader checks each against what it finds.

### Instructions

Every instruction starts with a header word: the opcode in the low 16 bits, and the instruction's total length in words, header included, in the high 16. The rest is fixed by the opcode: static attributes first, in the order the term writes them, then operands.

An instruction that can vary in length (a phi, a call, an `asm_fixed`, an effect list) takes its element count from the header's length. No instruction contains another.

### Blocks

There is no block marker. A block is its phis, then its other instructions, then exactly one jump. The jump ends the block, and the next instruction begins the next one. So the opcodes fall into three groups (phi, plain, jump), and their order within a block is fixed.

The first block is the entry block and has no phis.

### Jumps and targets

A jump target is one word: the block index shifted left by one, with the low bit set for `poll(L)`.

| Jump | After the header |
| --- | --- |
| `goto(T)` | target |
| `branch(V, T1, T2)` | operand, target, target |
| `ret(V)` | operand |
| `rets([V1, V2])` | operand, operand |
| `ret` | nothing |
| `unreachable` | nothing |

### Phis

`phi(tmp(D), K, Pairs)` is the class, then one pair per predecessor: a block index and an operand. The pairs keep the term's order. D is implicit.

## Instruction set

The rule is mechanical. Each instruction form of `ir.pl`, and each Op of a `let`, gets one opcode. Its words are the header, then the result class if it defines a temporary, then the term's static attributes in the order the term writes them, then its arguments as operands.

The tables give the layout after the header. "K" is a class word, "opnd" an operand word. Opcode numbers will be assigned per group, with gaps, when the layouts are agreed.

### Ops of `let`, both stages

| Ops | Layout |
| --- | --- |
| `add` `sub` `mul` `div` `udiv` `rem` `urem` `and` `or` `xor` `sar` `shr` `shl` | K, opnd, opnd |
| `neg` `copy` `cast` `truncd` `truncx` `ptoi` `itop` | K, opnd |
| the twelve float and integer conversions (`stosi` ... `ultof`) | K, opnd |
| `cmp(Cond, K1)` | K, condition, K1, opnd, opnd |
| `ext(T)` | K, source type, opnd |
| `load(T)` | K, load type, opnd |
| `alloc(Align)` | K, alignment, opnd |
| `va_args` | K, opnd |
| `va_arg` | K, opnd |
| `setjmp(Kind)` | K, kind, opnd, opnd |
| `atomic_load(p)` | K, opnd |
| `cas(T)` | K, load type, opnd, opnd, opnd |

### Ops of `let`, checked stage

"Range" is `Lo`, `Hi` as two `i64`, then rights, then alignment: six words.

| Ops | Layout |
| --- | --- |
| `check` | K, range, opnd |
| `check_ahead` | K, range, `AHi` as `i64`, opnd |
| `renew`, `check_limit`, `renew_if` | K, range, opnd, opnd |
| `renew_hull` | K, range, opnd, opnd, opnd |
| `half_check` | K, bound, range, opnd, opnd |
| `span_test` | K, `Lo`, `Hi` as `i64`, opnd |
| `limit(Size)` | K, size, opnd |
| `check_local` | K, local id, `Off`, `Bytes` as `i64`, rights, alignment |
| `check_function` | K, opnd |
| `raw_load(T, Off)` | K, load type, `Off`, opnd |
| `raw_load_pointer(Off, Effects)` | K, `Off`, opnd, then one effect code per remaining word |
| `raw_cas(T, Off)` | K, load type, `Off`, opnd, opnd, opnd |

### Other instructions

| Instruction | Layout | Defines |
| --- | --- | --- |
| `store(W, V, A)` | width, opnd, opnd |  |
| `atomic_store(p, V, A)` | opnd, opnd |  |
| `fence` | nothing |  |
| `access(K, A, Size, Align)` | rights, size, alignment, opnd |  |
| `touch(tmp(Q))` | opnd |  |
| `local_alloc(Name, Size)` | `Size` as `i64` | one local |
| `local_load(tmp(D), K, T, Name, Off)` | K, load type, local id, `Off` | one temporary |
| `local_store(W, V, Name, Off)` | width, local id, `Off`, opnd |  |
| `call(Res, Callee, Args)` | result word, callee opnd, then (K, opnd) per argument | 0, 1 or 2 |
| `raw_call(Res, Callee, Args)` | as `call`, the callee a class-`f` temporary | 0, 1 or 2 |
| `flight(tmp(D), Op, Args, Lower)` | op, lower flag, lower opnd, then (kind, opnd) per argument | one temporary |
| `raw_store(W, Off, V, A)` | width, `Off`, opnd, opnd |  |
| `raw_store_pointer(Off, V, A, Effects)` | `Off`, opnd, opnd, then effect codes |  |
| `asm_fixed(M, Ins, Outs)` | mnemonic, input count, (register, opnd) per input, then a register per output | one per output |
| `loc(File, Line)` | string id, line |  |

A call's result word is 0 for `void`, a class code for one result, or the tuple form used for return types.

> **Changed in the implementation (Nov 10, 2026).** `flight` is its op (copy, add or sub), a lower tag (0 for
`none`; 1 for `lower(P)`, then P's operand), then per argument a tag (0
for a value, 1 for `address(P)`) and an operand: a `none` lower writes
no operand. `touch` is one operand. The opcode of each form is in the
assigned numbers.

Effect codes name the members of `pointer_memory_effects/2`: `aux_read`, `lower_resolve`, `address_read`, `aux_ensure`, `lower_barrier`, `rooted_reload`, `lower_write`, `address_write`, `atomic_read`, `atomic_write`, `atomic_cas`. The lists are written out because the IR says they are executed, not implied.

## Stages and evidence

NFB carries both stages with one encoding. The header says which, and the opcode groups enforce it: an unchecked module may not contain a checked-stage opcode, and a checked filc module may not contain the checking `load`, `store` or indirect `call`.

Which stage a client sends decides what it is trusted with.

| A client sends | The library does | A wrong module can cause |
| --- | --- | --- |
| unchecked | pizlonates, validates, compiles | a wrong result or a Fil-C panic |
| checked | validates, compiles | nothing more, if `valid` accepts only safe modules |

The first row is the regex compiler's position today: it is outside the safety argument. The second row rests on `valid_no_unchecked`. A client that is not trusted to be correct should send unchecked IR until that theorem covers every construct it uses.

**Evidence is already in the stream.** The checked stage's reuse forms take earlier proofs as operands: `renew` reads the proof it renews, `half_check` the proof that covers the other bound, `renew_if` the span test that guards it. The validator checks these and does not search for them. NFB needs nothing extra to carry them.

**Certificates are reserved.** Campaign 5 of the formal plan proposes `discharged(Cert)`: a check replaced by a certificate that it cannot fail. Section id 6 is reserved for a table of certificates, and one opcode for an instruction that names an entry. Their layout waits for that campaign's certificate language.

## Well-formedness

A reader enforces these before anything else looks at the module. They are structural: each is checked in one pass with no knowledge of what the instructions mean.

1. The magic and major version match, unused flag bits are zero, and the file's length is the header plus the sections' lengths.
2. Section ids increase. Every core id is known.
3. Every count and length fits in what remains of its section.
4. Every enumeration word holds a listed code.
5. Every string id, symbol id, constant index, block index, temporary id and local id is below its table's size.
6. Every instruction's length is one its opcode allows, and it ends inside its function body.
7. Each block is phis, then plain instructions, then one jump. The entry block has no phis. The last instruction of a body is a jump.
8. The block, temporary and local counts in a body's header equal what the stream contains.
9. A local id is used only after its `local_alloc` in the stream.
10. The canonical-form rules of the next section hold.

If the ordered flag is set, two more:

11. Every operand that is a temporary, outside a phi, has an id already defined earlier in the stream.
12. Every jump target with an index at or below the current block's has its poll bit set.

Rule 12 is a syntactic sufficient condition for the checked stage's requirement that every cycle of the CFG has a poll edge, since any cycle has an edge that goes backward in the stream.

A module that passes is a term of the grammar. It is not yet a valid module: classes, dominance, single-use of proofs and the stage rules remain `valid_module/1`'s and `Validate.v`'s work.

> **Changed in the implementation (Nov 10, 2026).** the Prolog reader enforces rule 10, and with it all the
others, by writing the module it read and requiring the very words it
was given, side sections from 0x200 aside. It also refuses a body whose
block, temporary or local count exceeds the words left in it before any
table is sized. The stage and mode flags are computed from the module
by `module_stage/2` and `module_mode/2`, so they agree by the same
check; a checked-stage opcode in an unchecked module is refused that
way, and a checked filc module's leftover `load`, `store` or indirect
`call` is `valid_module/1`'s to refuse.

## Canonical form and identity

A module has one encoding because every choice an encoder could make is fixed.

- Lists keep the term's order. Nothing semantic is sorted.
- STRINGS and CONSTANTS are sorted, hold no duplicates, and hold nothing unused.
- A constant below 2^30 is inline.
- Named-only symbols are sorted by name, after the defined ones in item order.
- Padding bytes and unused bits are zero.
- An empty core section is absent.
- Ids are implied by position, so there is no numbering to choose.

The **module id** is the SHA-256 of the header and the core sections, with the section count taken as the number of core sections. Side sections do not contribute. Two modules with the same id are the same term up to the names of temporaries, labels and locals.

Each function body is also a self-contained byte range once its symbols are fixed, so a **function id** can be defined the same way. That would let a JIT cache one function at a time.

A cache key for compiled code is the module id together with the compiler's version and options. The regex experiment's README already notes that its key omits the compiler's version.

## Versioning and extension

- **Major version.** A reader rejects a major version it was not built for. While the IR is still changing, a change to any existing layout bumps the major version. There is no compatibility promise across majors.
- **Minor version.** A minor version may add opcodes, enumeration codes and core sections. A reader built for minor n rejects a module that uses anything from a later minor, because it rejects unknown opcodes and codes. It reads every module of minor n or earlier.
- **Opcodes are never renumbered or reused** within a major version. A removed instruction's number stays retired.
- **Unknown means refuse.** An unknown opcode, enumeration code or core section fails the whole module. This is what `rx.pl` does with a PCRE2 opcode it does not name, and for the same reason: guessing is worse than falling back.
- **Side sections are the extension point.** Tools may add side sections with ids from `0x200` up for their own data. These never affect meaning or identity.

The format's version is separate from the compiler's. A cache needs both.

## Relation to the term form and the Rocq model

The term form stays the reference. NFB is defined by two functions between them, and should be implemented three times: in Prolog, in Gallina, and as a small C writer for clients.

**Prolog.** `nanofil encode` and `nanofil decode` beside `ir_text.pl`. The gate is a round trip over the whole corpus: decode of encode is the same term when NAMES is written, and the same term up to renaming when it is not.

**Gallina.** `encode : module -> list word` and `decode : list word -> option module`, in the backend project, over `Syntax.v`'s own types. The decoder takes the place of `Transport.decode_module` and the hand-written term reader in `main.ml`. A function outside the core subset still decodes: it becomes `IOutside` with its term rebuilt from the words, as it does today.

The theorems wanted, in order of use:

1. **Round trip.** `decode (encode m) = Some m'` with `m'` equal to `m` up to names.
2. **Canonical.** If `decode ws = Some m` then `encode m = ws` on the core sections. With the first, this makes the module id a sound identity.
3. **Total and bounded.** `decode` terminates on every word list and rejects anything malformed. If it is written with fuel, the fuel is the input's length and is proved never to run out.

The second is the one that costs something, because every canonical-form rule becomes a case in the proof. It is also the one that justifies using the bytes as a cache key.

> **Changed in the implementation (Nov 10, 2026).** The Gallina
> `decode` takes words only if `encode` writes the same words for the
> module it read, so the canonical theorem costs little:
> `decode_canonical` in `rocq/backend/NfbProof.v` proves it, with the
> words compared on the core sections and NAMES, and
> `decode_identity` gives the sound identity. The cost moves to the
> round trip, which must show that the reader inverts the writer;
> that proof is in progress. Total and bounded is
> `rocq/backend/NfbTotal.v`: every reader that takes fuel is given the
> length of its words, and each lemma there proves that more fuel
> gives the same answer, because each round reads a word.

**Agreement between the two.** The Prolog and Gallina encoders must produce the same bytes for every module of the corpus. This is the same byte-identity standard the backend campaign already uses for assembly.

**Speed.** Reusing `Syntax.v` means the decoder still builds names and the backend still looks them up in `Maps.v`. The gain from dense ids arrives only when a consumer works on ids directly. A reasonable path is to decode to an id-indexed form, prove it corresponds to the `Syntax.v` module, and let the hot passes use that form.

## Security considerations

The reader's input is untrusted by assumption. Under Fil-C a reader's bug is a panic and not a corruption, but a panic inside a host process is still a denial of service, so the reader should not have any.

- **No offsets.** The format has lengths and indices, never a position to jump to. A reader only moves forward.
- **Every length is checked against what remains** before it is used to allocate or to loop.
- **No recursion on input.** The stream is flat. The deepest structure is section, function, instruction.
- **Work is linear in the input.** No field causes work out of proportion to its size: `zero(N)` describes N bytes without containing them, and a consumer must bound it by its own limits, not by the file's size.
- **Declared counts are verified, not trusted.** A body's block, temporary and local counts may size tables, but they are bounded by the body's length before allocation and compared with the stream afterwards.
- **Strings are bytes.** Symbol and file names are never interpreted, and a consumer that prints them must escape them.
- **Side sections are inert.** A consumer that compiles must not read NAMES or CONTEXT for anything that affects the code.
- **Passing the reader proves nothing about safety.** Only pizlonation or `valid` does. A consumer that accepts checked modules must run `valid` on what it decoded, every time.

Resource limits (largest module, most functions, largest `alloc`) belong to the consumer's policy and are not part of the format.

## Alternatives considered

| Alternative | Why not |
| --- | --- |
| Keep terms only, with a Gallina term reader | Solves the proved-reader goal, not decode cost or identity. Names stay on the hot path. |
| Protocol Buffers | Not canonical, tagged and variable-length throughout, and a heavy runtime for a small library. |
| FlatBuffers or Cap'n Proto | Built on internal offsets, so a safe reader validates a pointer graph. Hard to specify and prove. |
| CBOR or MessagePack | Reasonable for side sections. For instructions they spend a type tag per operand that the opcode already implies. |
| LLVM-style bitstream | Much more compact, much more complex, and forward references are a known source of trouble. |
| Variable-length integers (LEB128) | Smaller files, but branchy to decode, and each number has several spellings unless minimal encoding is enforced. |
| A stack machine, as WebAssembly | Compact and simple to validate, but the IR is already SSA and a consumer would rebuild it. |
| Block parameters in place of phis | Often nicer to encode, but the model, the semantics and the proofs are about phis. A second form would need a second set of theorems. |
| Dominator-relative value numbers, as SafeTSA | Makes a non-dominated use unwritable, which would remove a class of validation. It forces every producer to compute dominators, and the validator's dominance proof already exists. |
| Required block order instead of a flag | Reordering blocks changes the assembly, which would break byte identity with the Prolog pipeline while it is the oracle. |

## Open questions

1. **Is this Fil-bytecode?** Filip Pizlo proposed a Fil-bytecode with a Rocq specification and "it never panics" as the oracle. NFB's checked stage may be that format, or a lower layer under it. Worth settling with him before the layouts are fixed.
2. **Do names affect the assembly?** If block or temporary names reach the emitted text, byte identity with the Prolog compiler needs the NAMES section to be read by the backend while Prolog is the oracle. That contradicts "side sections are inert" for that period.
3. **`loc` in the stream or beside it.** `loc(File, Line)` is an instruction in the IR, so this draft encodes it as one, and it is part of the module id. Moving line information to a side section would make two modules that differ only in line numbers identical, but departs from the term form.
4. **Constants.** The draft assumes a `const(N)` is a non-negative integer below 2^64, as `ir.pl`'s class moduli suggest. Extended-precision (`x`) constants, if they exist as values, need a third form.
5. **Imports carry no signature.** A named-only symbol is just a name, as in the IR. The library's client must agree with it on what each import is. Should NFB record an expected signature, or a contract name, for each?
6. **Ordered: a flag or a second profile?** One flag keeps the format single. A producer that sets it wrongly is rejected, which is cheap to check. Is the one-pass consumer worth even that?
7. **The 16-bit instruction length.** It caps a call at about 32,000 arguments and a phi at as many predecessors. A long form can be added if the corpus has anything larger.

> **Changed in the implementation (Nov 10, 2026).** no instruction of the corpus comes near it; the encoder
refuses one longer than 65535 words. Questions 2 and 4 are answered
provisionally above and sent to Mikael: block labels do reach the
emitted assembly (`.L<function>.<label>`, filc_amd64.pl's
`block_label`), so while Prolog is the oracle a backend that wants byte
identity reads NAMES for labels; and constants are signed and up to 96
bits wide. Question 3 keeps the draft's default, `loc` in the stream.
8. **An id-indexed model.** The speed argument needs a consumer that works on ids. Whether that is a second inductive in the backend or a change to `Syntax.v` is the model owner's decision.
9. **The hash.** SHA-256 is a conventional choice. A Gallina implementation for the identity theorem is not needed, since the theorem is about bytes, but the library needs one in its trusted base.
10. **Shipping the IR with the code.** A `.nanofil.ir` section in the shared object, holding the checked module the code was compiled from, would let anyone re-run `valid` against the binary they have. Not specified here.

## Appendix: a worked example

A plain, unchecked module with one function that adds one to its argument:

```prolog
module([
  func(add1, export, w, [param(w, tmp(x))],
    [block(start, [],
       [let(tmp(y), w, add, [tmp(x), const(1)])],
       ret(tmp(y)))])
]).
```

Its encoding is 30 words, 120 bytes. The opcode numbers (`0x0010` for `add`, `0x0082` for `ret`) and the packing of the kind and linkage word are placeholders.

```text
; header
0042464E   magic "NFB\0"
00000001   version 0.1
00000004   flags: unchecked, plain, ordered
00000003   3 sections

; STRINGS
00000001   section id 1
00000003   3 words
00000001   1 string
00000004   4 bytes
31646461   "add1"

; SYMBOLS
00000003   section id 3
00000004   4 words
00000001   1 symbol
00000000   name: string 0
00000000   kind 0 (function), linkage export
00000000   extra

; FUNCTIONS
00000005   section id 5
0000000D   13 words
0000000C   body: 12 words
00000001   returns w
00000001   1 parameter
00000001   of class w            ; defines temporary 0
00000001   1 block
00000002   2 temporaries
00000000   0 locals
00040010   add, 4 words         ; defines temporary 1
00000001   class w
00000000   operand: temporary 0
00000005   operand: constant 1, inline
00020082   ret, 2 words         ; ends block 0
00000004   operand: temporary 1
```

The names `x`, `y` and `start` are gone: they are temporaries 0 and 1 and block 0. A NAMES section would restore them.

## Appendix: assigned numbers

Provisional, major version 0, minor 1. The one table they come from is
`nfb_form/3` and `nfb_code/3` in [nfb.pl](../src/nfb.pl); this appendix
restates it.

### Opcodes

Every instruction's header word is its opcode in the low 16 bits and
its length in words, header included, in the high 16. The fields are
the draft's layouts; a `let` writes its result class first.

| Opcode | Form | Fields after the header |
| --- | --- | --- |
| `0x01` | rebind | one word per temporary the next instruction defines |
| `0x08` | `phi` | K, then (block index, operand) per pair |
| `0x10`-`0x1C` | `add` `sub` `mul` `div` `udiv` `rem` `urem` `and` `or` `xor` `sar` `shr` `shl` | K, operand, operand |
| `0x20`-`0x30` | `neg` `copy` `cast` `truncd` `truncx` `ptoi` `itop` `stosi` `stoui` `dtosi` `dtoui` `xtosi` `xtoui` `swtof` `uwtof` `sltof` `ultof` | K, operand |
| `0x38` | `cmp(Cond, K1)` | K, cond, K1, operand, operand |
| `0x39` | `ext(T)` | K, ext type, operand |
| `0x3A` | `load(T)` | K, load type, operand |
| `0x3B` | `alloc(Align)` | K, align, operand |
| `0x3C` | `va_args` | K, operand |
| `0x3D` | `va_arg` | K, operand |
| `0x3E` | `setjmp(Kind)` | K, kind, operand, operand |
| `0x3F` | `atomic_load(p)` | K, operand |
| `0x40` | `cas(T)` | K, cas type, operand ×3 |
| `0x50` | `check` | K, range, operand |
| `0x51` | `check_ahead` | K, range, `AHi` as i64, operand |
| `0x52` | `renew` | K, range, operand, operand |
| `0x53` | `renew_hull` | K, range, operand ×3 |
| `0x54` | `half_check` | K, bound, range, operand, operand |
| `0x55` | `span_test` | K, `Lo`, `Hi` as i64, operand |
| `0x56` | `renew_if` | K, range, operand, operand |
| `0x57` | `limit(Size)` | K, size, operand |
| `0x58` | `check_limit` | K, range, operand, operand |
| `0x59` | `check_local` | K, local id, `Off`, `Bytes` as i64, rights, align |
| `0x5A` | `check_function` | K, operand |
| `0x5B` | `raw_load(T, Off)` | K, load type, `Off`, operand |
| `0x5C` | `raw_load_pointer` | K, `Off`, operand, effect per word left |
| `0x5D` | `raw_cas(T, Off)` | K, cas type, `Off`, operand ×3 |
| `0x60` | `store` | width, operand, operand |
| `0x61` | `atomic_store` | operand, operand |
| `0x62` | `fence` | nothing |
| `0x63` | `access` | rights, size, align, operand |
| `0x64` | `local_alloc` | `Size` as i64; defines a local |
| `0x65` | `local_load` | K, load type, local id, `Off` |
| `0x66` | `local_store` | width, local id, `Off`, operand |
| `0x67` | `call` | result word, callee, (K, operand) per argument |
| `0x68` | `asm_fixed` | mnemonic, input count, (register, operand) per input, register per output |
| `0x69` | `loc` | string id, line |
| `0x70` | `touch` | operand |
| `0x71` | `raw_call` | as `call` |
| `0x72` | `flight` | op, lower tag and operand, (tag, operand) per argument |
| `0x73` | `raw_store` | width, `Off`, operand, operand |
| `0x74` | `raw_store_pointer` | `Off`, operand, operand, effect per word left |
| `0x80` | `goto` | target |
| `0x81` | `branch` | operand, target, target |
| `0x82` | `ret(V)` | operand |
| `0x83` | `rets` | operand per word left |
| `0x84` | `ret` | nothing |
| `0x85` | `unreachable` | nothing |

The groups: phi is `0x08`, jumps are `0x80` and up, every other opcode
is plain. A range is `Lo` and `Hi` as i64, rights, align: six words.
Align, size and line are one word each.

### Codes

| Enumeration | Codes |
| --- | --- |
| class | 0 `void`, 1 `w`, 2 `l`, 3 `s`, 4 `d`, 5 `x`, 6 `p`, 7 `a`, 8 `f` |
| width | the class codes of `w` `l` `s` `d` `x` `p`; 9 `b`, 10 `h` |
| load type | the class codes of `l` `s` `d` `x` `p`; 16 `sw`, 17 `uw`, 18 `sh`, 19 `uh`, 20 `sb`, 21 `ub` |
| ext type | the class codes of `s` `d`; the narrow codes 16 to 21 |
| cas type | the class codes of `l` `p`; the narrow codes 16 to 21 |
| cond | 0 `eq` 1 `ne` 2 `sle` 3 `slt` 4 `sge` 5 `sgt` 6 `ule` 7 `ult` 8 `uge` 9 `ugt` 10 `le` 11 `lt` 12 `ge` 13 `gt` 14 `o` 15 `uo` |
| rights | 0 `read`, 1 `write` |
| bound | 0 `upper`, 1 `lower` |
| setjmp kind | 0 `setjmp`, 1 `'_setjmp'`, 2 `sigsetjmp` |
| effect | 0 `aux_read` 1 `lower_resolve` 2 `address_read` 3 `aux_ensure` 4 `lower_barrier` 5 `rooted_reload` 6 `lower_write` 7 `address_write` 8 `atomic_read` 9 `atomic_write` 10 `atomic_cas` |
| flight op | 0 `copy`, 1 `add`, 2 `sub` |
| mnemonic | 0 `cpuid` 1 `xgetbv` 2 `rdtsc` 3 `rdtscp` 4 `lfence` 5 `sfence` 6 `pause` |
| register | 0 `a`, 1 `b`, 2 `c`, 3 `d` |
| function linkage | 0 `export`, 1 `local`, 2 `weak` |
| data linkage | 0 `export` 1 `local` 2 `weak` 3 `ro(export)` 4 `ro(local)` 5 `ro(weak)` 6 `tls(export)` 7 `tls(local)` 8 `init(ctor, P)` 9 `init(dtor, P)` 10 `init(ctor, none)` 11 `init(dtor, none)` 12 `extern(weak)` |
| alias linkage | 0 `export`, 2 `weak` |

A symbol's second word is its kind in the low 8 bits and its linkage
code above them; an `init(_, P)` with an integer P has P in the extra
word. A result or return word for `tuple([K1, K2])` is
`0x100 + 16*K1 + K2`. A target is the block index shifted left once,
bit 0 set for `poll`. Strings are the UTF-8 bytes of an atom's codes,
sorted by bytes; a `str/1` data item holds its bytes as they are.
