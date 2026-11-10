# A spike: proofs that link user glibc's IR

[zsys.md](zsys.md) proposes moving the formal campaign's libc boundary
down to libpizlo: compile user glibc to checked IR, link it into the
program's module, and give contracts only to libpizlo's `zsys_`
primitives. This spike tries that end to end on two small programs.
Hello's proof keeps Campaign 4's per-function contracts; nothing here
changes it.

The result is two Iris proofs whose module contains glibc's own code:

- [len.c](../rocq/glibc/len.c) returns `strlen` of a literal. Its
  module holds glibc's strlen, and it calls no contract at all:
  `len_never_panics`.
- [say.c](../rocq/glibc/say.c) writes a literal to descriptor 1 with
  glibc's strlen and write. The one contract is libpizlo's
  `zsys_write`: `say_logic_safe`. It is safety from any memory that
  holds the literal and the thread's errno, not `never_panics` from
  the module's initial memory, which has no errno.

## The pipeline

1. **glibc's units.** [survey/glibc/capture.nix](../survey/glibc/capture.nix)
   keeps each preprocessed unit of the staging user glibc. A unit's
   `.filc_*` module asm is dropped, as `run.py --drop-filc-asm` does,
   until nanofil reads those directives. Then `nanofil -O` compiles
   `string/strlen.os` and `io/write.os` like any C file.
2. **Linking.** [link.pl](../rocq/link.pl) links the program's checked
   module with the units' modules from `main`. glibc defines `__strlen`
   and the alias `strlen`, so the linker now reads aliases: an alias is a
   definition, reaching it reaches its target, a weak declaration
   gives way to any definition, and a weak function or alias gives way
   to a strong definition of the same name. Hello's fixture is
   byte-identical after the change.
3. **The fixture.** [rocq/glibc/code.sh](../rocq/glibc/code.sh) does
   both steps and prints the linked module as Gallina, as
   `LenCode.v` and `SayCode.v`. It checks them, or rewrites them with
   `--update`.
4. **Which symbols come from where.** `find_fn` finds every glibc name
   in the module, so a call of `strlen` or `write` is a direct call
   (`wp_call_bind`). `ExternalMachine.v`'s `external_site` sends what
   is left to the registry. That is `zsys_write` for say.c, and
   nothing for len.c. No new dispatch was needed.

```sh
nix build -f nanofil/survey/glibc/capture.nix \
  -o /tmp/glibc-pp
FILCC=... rocq/glibc/code.sh /tmp/glibc-pp
nix build -L .#checks.x86_64-linux.nanofil-glibc
```

The Nix check compiles the proofs against the model's theories, runs
parse.sh on them and runs the native probe, in about a minute. It is
off the quick gate. code.sh needs the six-minute capture, so it is
run by hand.

## The proofs

[GlibcLogic.v](../rocq/glibc/GlibcLogic.v) holds what both proofs
share:

- `wp_raw_load_read`: Logic.v's raw long load through a read-only
  capability too. strlen reads a literal's words through one.
- `pieces_never_panics`: `heap_never_panics` for a program that starts
  owning pieces of its initial memory, here the literal's.
- `step`: takes the next instruction by its rule, with every premise
  computed. `norm_env` keeps the frame's environment as numerals.

[LenLogic.v](../rocq/glibc/LenLogic.v) walks glibc's word-at-a-time
`__strlen` over the literal "hello, glibc". It owns the literal's life
and its two words, reads each after a check that passes, and returns
12. [SayLogic.v](../rocq/glibc/SayLogic.v) does the same for
"hello, glibc\n", then enters `__libc_write`, whose body is one call
of `zsys_write`.

Both proofs are about one fixed literal. Every value of the run is a
numeral, so the proof is mostly computation. A strlen triple for any
string is the next step (below).

## The zsys_write contract

[ZsysWrite.v](../rocq/glibc/ZsysWrite.v) is the one new trusted
contract. At the pin, libpizlo's `filc_native_zsys_write` asserts fd
is not its log descriptor. It then checks that the buffer is readable
for `size` bytes, makes the system call, and on failure stores errno
through user glibc's errno handler. The contract follows those steps:

| Field | zsys_write |
| --- | --- |
| world | the thread's errno pointer, libpizlo's log fd |
| pre | buffer readable for n bytes, fd not the log, errno a live aligned int |
| writes | errno's 4 bytes, nothing else |
| post | k ≤ n bytes accepted for fd and k returned, or -1 and none |
| panics | null or out-of-bounds buffer, argument size |

The errno callback is named as the call's one writable root rather
than proved. The machine's `effects` rule then keeps every other byte.
The world is trusted to be the real one: the pointer is the calling
thread's user glibc `errno`, already allocated (Fil-C allocates a
thread-local on first use, and the contract allows no allocation);
glibc's `errno_handler` is registered, as `__libc_start_main` does
(`filc_set_errno` panics without one); and `FILC_DUMP_ERRNOS` is
unset, so a failure logs nothing.
The observation reuses ExternalCalls.v's `StreamBytes`, read here as
bytes the kernel accepted for the descriptor. Its probe,
[zsys-write.c](../rocq/glibc/zsys-write.c), checks each clause natively
against libpizlo: full, read-only, empty and partial writes, EBADF,
EAGAIN, and a buffer one byte too short, which panics before writing.
The EBADF case also checks that a stack array, a heap object and a
global are unchanged. Two clauses go untested: the bound k < 2^31,
which needs a 2 GiB buffer, and the log-descriptor assertion.

## Findings

- **glibc's strlen is safe on Fil-C only because objects are whole
  words.** It reads the aligned 8-byte word that holds the first byte,
  then every word through the one holding the NUL. That stays in
  bounds because filcc gives a 13-byte literal a 16-byte object, and
  the model's layout rounds data to 8. A general strlen triple must
  require the object's end to be 8-aligned. Every Fil-C object meets
  that, but no current string predicate states it.
- **The libc boundary moves, but no new dispatch is needed.** Linking
  takes care of it, as zsys.md predicted.
- **`errno` is the first callback.** Naming the handler's effect as a
  writable root works for a single store. Proving `errno_handler`'s
  triple would remove the trust.
- **Cost.** Each proof walks about 90 instructions of strlen. The
  computed steps take about 7 seconds and the Qed about 13; each file
  checks in under 30 seconds.
- **parse.sh.** The grammar reads `let x := eval vm_compute in t in`
  only when a single tactic follows. The tactics are written that way;
  [rocq_syntax.pl](../web/rocq/rocq_syntax.pl) is unchanged.

## Next steps

1. A strlen triple for any string, `string p` with an 8-aligned object
   end, proved once over `__strlen`'s IR. That is the first lemma
   "module strlen implements `strlen_contract`" of zsys.md.
2. The other leaf functions Hello calls that reach no primitive
   (`strcmp`, `memchr`, the ctype tables), the same way.
3. `printf` only after these. It pulls in the stdio core of about 357
   symbols, with its locks, vtables and locale.
4. Drop the `.filc_*` rewrite once nanofil reads the directives.

## Decisions this raises

1. **What the proofs trust about glibc's compiler.** These proofs are
   about nanofil's IR of glibc, while programs run with filcc's
   `libc.so` (zsys.md). Recommended: state it as a named assumption in
   this spike's doc, and decide before Hello uses glibc's IR.
2. **A descriptor event.** `StreamBytes` means stdio acceptance in
   Campaign 4's contracts, and ExternalCalls.v says it is not a kernel
   write. Reusing it does no harm while no registry holds both `puts`
   and `zsys_write` and no theorem states a zsys trace. Recommended:
   add a separate event for kernel-accepted bytes before either
   happens. It is Campaign 4's file.

## Review

An Oracle review of the contract and the link.pl change found two
blockers, both fixed:

- The errno cell was any writable span, so the contract could be
  stated for a world it is false of. It is now ExternalCalls.v's
  `errno_cell` (a nonnull, aligned, writable int) at the world's
  pointer, with the trusted world relation above.
- A weak declaration (`#pragma weak foo` without a definition, which
  nanofil prints as `extern(weak)` data) overrode another object's
  weak definition, so the link used a null symbol. It now gives way
  to any definition.

Its notes, left open:

- link.pl retargets an alias of an overridden weak function to the
  strong definition; in ELF the alias keeps the original address.
  Weak data is not treated as weak, so it still fails as defined twice.
- Hello passes each libgnu.a member as a plain object. A strong
  definition in a member a linker would not extract now wins
  silently. Hello has no weak items today, so its link is unchanged.
- No program can own errno's pieces, so a program proof cannot read
  errno.
- `wp_raw_load_read` and `pieces_never_panics` generalise Logic.v's
  `wp_raw_load` and `heap_never_panics`, and belong there. Logic.v is
  Campaign 3's file.
