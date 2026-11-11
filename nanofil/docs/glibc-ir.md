# A spike: proofs that link user glibc's IR

[zsys.md](zsys.md) proposes moving the formal campaign's libc boundary
down to libpizlo: compile user glibc to checked IR, link it into the
program's module, and give contracts only to libpizlo's `zsys_`
primitives. This spike tries that end to end on two small programs.
Hello's proof keeps Campaign 4's per-function contracts; nothing here
changes it.

The result is a triple for glibc's own strlen and two Iris proofs
whose module contains glibc's own code:

- [StrlenLogic.v](../rocq/glibc/StrlenLogic.v) proves
  `wp_glibc_strlen` over `__strlen`'s IR, for any string whose object
  is laid out in whole words.

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
   keeps each preprocessed unit of the staging user glibc. `nanofil -O`
   compiles `string/strlen.os` and `io/write.os` like any C file, its
   `.filc_*` module asm intact, so the IR carries glibc's real
   aliases and `__GI_` names.
2. **Linking.** [link.pl](../rocq/scripts/link.pl) links the program's checked
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

## Assumption G1: the proofs are about nanofil's IR of glibc

Every theorem here is about the module that nanofil compiles from
user glibc's preprocessed units, with their `.filc_*` asm. The
programs these proofs describe run with filcc's `libc.so`, which is
built from the same sources by filcc's LLVM pass. The theorems carry
over to a native run only if both compilers give each glibc function
the same behaviour, the same safety checks and the same object
layout. That is an assumption, not a theorem: call it **G1**. Any
claim that rests on these proofs about a real binary names G1.

G1 already applies to the program's own code, which is also nanofil's
IR. What is new is that glibc's code is under it too, where until now
Campaign 4's contracts and their native probes stood. Each native
probe, such as [zsys-write.c](../rocq/glibc/zsys-write.c), checks one
libpizlo primitive under filcc. It does not check G1 for glibc's code.
**Decided by mbrock (2026-11-10):** G1 stands as a named, written-down
assumption for now. Whether to keep it is decided before Hello uses
glibc's IR.

## The proofs

[GlibcLogic.v](../rocq/glibc/GlibcLogic.v) holds what the proofs
share:

- `wp_raw_load_read`: Logic.v's raw long load through a read-only
  capability too. strlen reads a literal's words through one.
- `pieces_never_panics`: `heap_never_panics` for a program that starts
  owning pieces of its initial memory, here the literal's.
- `step`: takes the next instruction by its rule, with every premise
  computed. `norm_env` keeps the frame's environment as numerals.

### glibc's strlen, for any string

[StrlenLogic.v](../rocq/glibc/StrlenLogic.v) proves
`wp_glibc_strlen`, a triple of `__strlen`'s IR over any registry and
world, so a program uses it as a rule at its call. glibc's strlen
loads the aligned word that holds the string's first byte, masks off
the bytes before the string, then loads each next word until one
holds a zero byte, and counts bits to find which. So the triple is
about whole words, not bytes:

| Premise | Meaning |
| --- | --- |
| capability | names the object b, read-write or read-only |
| alignment | b is 8-aligned |
| ownership | b's life, and every byte of the words from the one holding the first byte through the one holding the NUL, bytes past the NUL included |
| bounds | those words lie in b's region |
| result | the index of the first zero byte from the string's start |

That is the whole-word rounding glibc's strlen depends on, stated as a
premise: a string whose NUL ends an object mid-word does not meet it.
[StrlenBits.v](../rocq/glibc/StrlenBits.v) holds the bit facts:
bitwise ops and carry-free sums byte by byte, the two zero-byte masks
of string-fza.h and string-fzb.h, and the population count of
string-fzi.h, each byte claim checked on all 256 bytes by computation.
The loop is proved for any number of words by induction on them.

### The programs

[LenLogic.v](../rocq/glibc/LenLogic.v) and
[SayLogic.v](../rocq/glibc/SayLogic.v) take glibc's strlen by
`wp_glibc_strlen`. The literal's object is 16 bytes and 8-aligned, and
the program owns its life and both words, which is the triple's
premise. SayLogic.v then enters `__libc_write`, whose body is one
call of `zsys_write`, and walks it with `step`.

## The zsys_write contract

[OsWrite.v](../rocq/glibc/zsys/OsWrite.v) is the trusted `zsys_write`
contract over [OsWorld.v](../rocq/glibc/zsys/OsWorld.v). At the pin, libpizlo's `filc_native_zsys_write` asserts fd
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
  the model's layout rounds data to 8. `wp_glibc_strlen` states it as
  its ownership and bounds premise.
  [WordString.v](../rocq/glibc/string/WordString.v)'s `word_string`
  states a C string in those terms, and StrlenWord.v proves the triple
  over it at any share (`wp_glibc_strlen_ws`).
- **The libc boundary moves, but no new dispatch is needed.** Linking
  takes care of it, as zsys.md predicted.
- **`errno` is the first callback.** Naming the handler's effect as a
  writable root works for a single store. Proving `errno_handler`'s
  triple would remove the trust.
- **Cost.** StrlenLogic.v takes about 54 seconds, most of it the two
  Qeds (15 and 16 s), and StrlenBits.v about 3. With the triple,
  LenLogic.v takes 6 seconds and SayLogic.v 7, down from 28 and 29
  when each walked strlen's 90 instructions on its literal.
- **parse.sh.** The grammar reads `let x := eval vm_compute in t in`
  only when a single tactic follows. The tactics are written that way;
  [rocq_syntax.pl](../web/rocq/rocq_syntax.pl) is unchanged.

## Next steps

This spike's steps are done: the strlen triple, the `word_string`
bridge to it, and the fixtures regenerated with the `.filc_*`
directives kept. The leaf functions (`strcmp`, `memchr`, the ctype
tables, malloc), libio and exit, and later `printf`, are milestones of
the campaign to prove GNU Hello over user glibc (its Campaign Ledger),
which builds on these files. The leaf fixtures are in
[rocq/glibc/string](../rocq/glibc/string/code.sh).

## Decisions this raises

1. **What the proofs trust about glibc's compiler.** Recorded as
   assumption G1 (above). mbrock's decision: it stands as written for
   now, and is decided again before Hello uses glibc's IR.
2. **A descriptor event.** `StreamBytes` means stdio acceptance in
   Campaign 4's contracts, and ExternalCalls.v says it is not a kernel
   write. Reusing it does no harm while no registry holds both `puts`
   and `zsys_write` and no theorem states a zsys trace. Recommended:
   add a separate event for kernel-accepted bytes before either
   happens. It is Campaign 4's file.

## Review

An Oracle review of the contract and the linker change found two
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

- The linker retargets an alias of an overridden weak function to the
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
