# Function-order shuffling (funkyenv) meets Fil-C

An investigation into [NixVegas/funkyenv](https://github.com/NixVegas/funkyenv) —
per-deployment, seeded shuffling of function layout in ELF binaries — and
whether, where, and how it should be combined with Fil-C in filnix.

## Verdict up front

**Do not apply funkyenv's overlay to the Fil-C package set as-is: it
evaluates cleanly and then silently breaks the Fil-C bintools contract.**
Both of funkyenv's linker variants replace the `extraBuildCommands` of
filnix's bintools wrapper, deleting the lines that inject
`-lpizlo -lyoloc -lyolom -lc++ -lc++abi`, the `ld-fil1-*.so` dynamic-linker
path, and the `ld -r` wrapper hook into every link (experiment E3 below).
Evaluation succeeds and the stdenv still reports the Fil-C compiler and role
salt, so nothing warns you until links fail or produce non-Fil-C binaries.

That said, the *idea* composes well with filnix's existing structure, and
there are residual attack paths — public binary caches, unsafe runtime
islands, data-only interpreter corruption, and plain Fil-C bugs — where
"the attacker cannot download bit-identical binaries and look up offsets"
buys real margin on top of memory safety. The right shape is a
filnix-native port of the mechanism, not the upstream overlay:

- an opt-in `shuffleSeed` parameter on `mkPkgsFilc` (default off, so the
  public caches stay canonical),
- implemented inside [`toolchain/wrappers.nix`](../toolchain/wrappers.nix)
  by *extending* the Fil-C bintools wrapper with a native `ld.lld` symlink,
  never overriding it,
- with a canary/verifier rewritten for pizlonated symbol names,
- exposed to services through the NixOS module
  ([`nixos/filc.nix`](../nixos/filc.nix)), starting with PHP-FPM — the
  service both projects independently chose as their motivating example.

Everything labelled **observed** below was run during this investigation.
Everything labelled **inferred** follows from source but still needs a run
on a Linux builder (this investigation ran on an `aarch64-darwin` host with
no Linux remote builder, and Fil-C itself is Linux-only).

## 1. What funkyenv actually does

funkyenv is small: one Nix module (`funkyenv.nix`, 128 lines), a 4-line
overlay, a 13-line C canary, and two shell scripts. It is a *stdenv adapter
factory*: `pkgs.funkyenv.seed 4` (or `pkgs.lldFunkyenv.seed 4`) returns a
stdenv variant, used either per-package via
`override { stdenv = ...; }` or for a whole package set via
`config.replaceStdenv`.

Mechanically, for every derivation built with that stdenv it:

1. **Compiles with `-ffunction-sections`**, appended to
   `env.NIX_CFLAGS_COMPILE`, so each function lands in its own ELF input
   section (`.text.foo`) and becomes individually movable at link time.
2. **Links with a shuffling linker and a deterministic seed:**
   - mold variant: `stdenvAdapters.useMoldLinker`, then
     `--shuffle-sections=<seed>` (seed 0 to 2⁶³−1) appended to
     `env.NIX_LDFLAGS`. With no section glob, mold shuffles input sections
     generally, not only `.text`.
   - lld variant: the bintools wrapper's `ld` is symlinked to `ld.lld`
     (done in the wrapper, not via `-fuse-ld`, so builds that clear
     `NIX_CFLAGS_LINK` — notably glibc — still get it), and the flag is
     `--shuffle-sections=.text*=<seed>` (seed 1 to 2³²−2; lld treats 0 as
     "random" and 2³²−1 as "reverse"), delivered through an `@response`
     file so the cc-wrapper cannot glob-expand `.text*` away.
3. **Links a canary object into every binary** (`canary.c`): 32 tiny
   `static` functions `__funkyenv_canary_0..31`, marked
   `__attribute__((used, retain, noinline))`, compiled once with the plain
   (unadapted) stdenv, and appended unconditionally to `NIX_LDFLAGS`.
4. **Fails the build if the shuffle did not happen.** A setup hook
   (`verify-shuffle.sh`) runs in `postFixupHooks`: for every `EXEC`/`DYN`
   ELF file in every output it extracts the canary numbers in address
   order via `nm -n` and fails if they are missing (the file was linked
   without funkyenv's flags, or stripped) or still `0 1 2 … 31`.
   `dontVerifyFunkyenv = true` opts a derivation out.
5. **Provides an audit view:** every funky package gains
   `passthru.functionOrder` (and `functionOrderAgainst <pkg>`), a
   derivation that lists each binary's text symbols in address order for
   the normal and the shuffled build side by side, for diffing.

The security claim is narrow and honest: it is *diversification*, not
memory safety. If a service is exposed to the internet and an attacker
gains a primitive that needs to know where functions live (the README's
example is PHP exploitation in the style of "PHP2Shell", where a corrupted
internal function pointer is aimed at a known target), then binaries whose
function permutation depends on a seed only the operator knows cannot be
studied offline. ASLR randomizes the base; funkyenv randomizes the
*relative* layout that ASLR leaves fixed. The price is the usual one for
`replaceStdenv`-style world forks: a full from-source rebuild, and
bootstrap packages (glibc and friends) stay unshuffled unless rebuilt
separately — the README documents doing glibc with the lld variant
because mold cannot link glibc's dynamic loader.

Its test is telling: a NixOS VM running WordPress on a PHP whose
interpreter *and bundled extensions* are shuffled (via a `newScope`
`callPackage` trick, since `php.override { stdenv }` alone misses the
extensions nixpkgs builds with the global stdenv).

## 2. What Fil-C already does, and what it does not

Fil-C and funkyenv defend different layers, and Fil-C's layer is strictly
the stronger one for the attacks funkyenv worries about most:

| Attacker step | Fil-C (filnix pkgsFilc) | funkyenv (native) |
| --- | --- | --- |
| Out-of-bounds read/write, use-after-free, type-confused pointer | Traps: InvisiCap capability check on every access; freed objects keep empty bounds until FUGC collects them | No effect |
| Forge a function pointer from an integer / leaked address | No capability, wrong type: traps when called through the pizlonated ABI | Address is at least unknown without the seed |
| Know one leaked code address, compute all others | Works today: public caches ship the bit-identical binary, ASLR only shifts the base | Fails: relative offsets depend on the secret seed |
| In-bounds, same-object field corruption; logic/data-only attacks | Allowed (bounds checks pass); consequence depends on program logic | Makes code-pointer targets harder to name |
| Bugs in unsafe code: runtime ("yolo") parts, hand assembly, native libs in the same process | Outside Fil-C's guarantee by construction | Raises cost: offsets not downloadable |
| Bug in Fil-C itself (compiler pass, runtime, GC) | Violates the guarantee | Diversification is then the only layer left |
| Non-memory bugs (auth, injection, SSRF, …) | No effect | No effect |

Two filnix-specific facts sharpen the middle rows:

- **filnix publishes its binaries.** `scripts/ship` builds everything in
  [`scripts/ci-outputs.txt`](../scripts/ci-outputs.txt) on swa and
  publishes to two public binary caches before pushing; release tarballs
  and the `ghcr.io/mbrock/filnix-php` image are public too. Anyone can
  fetch the exact `php-fpm` a filnix NixOS host runs and read every
  function offset out of it. That is precisely the precondition funkyenv
  exists to remove — for native binaries it is the *only* precondition an
  exploit writer needs beyond the bug itself, and under Fil-C it remains
  useful for every residual row in the table.
- **A filnix system is a mixed system.**
  [`nixos/filc.nix`](../nixos/filc.nix) swaps chosen services (sshd, tor,
  unbound, lighttpd, redis, bind, php-fpm, optionally Nix and the login
  shell) for Fil-C builds and explicitly leaves systemd, glibc, and the
  kernel native. For those native parts funkyenv applies today, unchanged,
  and nothing about Fil-C weakens its case there. A complete "funky
  filnix host" story is two independent switches, not one.

So the honest framing is: under Fil-C, shuffling is *defense in depth for
the edges of the guarantee*, plus protection for the native majority of a
filnix NixOS system. It is never a substitute for the trap, and for a pure
Fil-C binary with no unsafe islands its marginal value is small. It is
also cheap at run time (layout only; no per-access cost on top of Fil-C's
existing 1.5–4×), which makes "small but real" easier to accept than it
would be for, say, another instrumentation pass.

## 3. Experiments

All experiments were run on the investigation host (`aarch64-darwin`,
Determinate Nix 2.32.4, no Linux builder configured). Fil-C binaries
cannot be built or run there, so Fil-C-side claims are established at
the evaluation and derivation level, which turns out to be where the
decisive breakage lives anyway.

### E1 — funkyenv on its nominal Darwin target: broken (observed)

funkyenv's flake lists `aarch64-darwin` in `supportedSystems` and defines
`checks.<system>.default` for it. Building
`hello.override { stdenv = pkgs.funkyenv.seed 4; }` there fails at
evaluation:

```
error: Mold can't be used to emit Mach-O (Darwin) binaries
```

The lld variant gets further but fails at configure: it symlinks `ld` to
the ELF `ld.lld`, which cannot produce Mach-O executables
("C compiler cannot create executables"). funkyenv is in practice a
Linux/ELF tool — fine for filnix purposes (Fil-C is Linux-only too), but
it means none of this investigation's results depend on Darwin quirks of
the *target*: the Fil-C side was evaluated for `x86_64-linux` throughout.

### E2 — the shuffle primitive itself (observed)

`canary.c` plus a six-function test file, compiled
`clang -target x86_64-unknown-linux-gnu -O2 -fPIC -ffunction-sections`
and linked as ELF shared objects with lld 21.1.8 and mold 2.42.1 (both
from nixpkgs, running on the Darwin host):

```
lld seed=none  canary: 0 1 2 … 31            prog: alpha beta gamma delta eps zeta entry
lld seed=4     canary: 29 14 25 0 22 13 …    prog: zeta delta beta gamma alpha eps entry
lld seed=999   canary: 6 22 17 3 1 21 …      prog: delta alpha entry gamma beta zeta eps
mold seed=4    canary: 3 6 20 30 23 0 10 …
```

Deterministic per seed, different per linker, exactly as funkyenv's
verifier expects (its `nm -n | sed` extraction reproduced the orders
above). There is nothing exotic about the primitive; the interesting
questions are all about the toolchain around it.

### E3 — the naive composition over Fil-C (observed, decisive)

Compose exactly as a user would try first — funkyenv's overlay in
filnix's cross overlay slot:

```nix
pkgsF = filnix.lib.x86_64-linux.mkPkgsFilc {
  crossOverlays = [ (import /path/to/funkyenv/overlay.nix) ];
};
helloFunky = pkgsF.hello.override { stdenv = pkgsF.lldFunkyenv.seed 4; };
```

Evaluation succeeds. The resulting stdenvs report `name = "funkyenv"`,
`cc.name = "filc-cc-wrapper-"`, and the correct Fil-C role salt
`x86_64_unknown_linux_gnufilc0`. The hello derivation even contains the
right-looking environment:

```
NIX_CFLAGS_COMPILE = " -ffunction-sections"
NIX_LDFLAGS = " @/nix/store/…-funkyenv-lld-4.rsp /nix/store/…-funkyenv-canary-x86_64-unknown-linux-gnufilc0/lib/funkyenv-canary.o"
```

with the verifier hook in `nativeBuildInputs` and a canary derivation
built by the Fil-C cross stdenv (note the `gnufilc0` name suffix — in
cross-overlay position, funkyenv's `stdenv.mkDerivation` *is* the Fil-C
stdenv, so the canary would be Fil-C-compiled; more on that in E4).

The breakage is one level down, in the bintools wrapper derivation.
filnix's `filc-bintools`
([`toolchain/wrappers.nix`](../toolchain/wrappers.nix)) is
`wrapBintoolsWith` over the patched GNU binutils 2.43.1
([`toolchain/binutils.nix`](../toolchain/binutils.nix)), and its
`extraBuildCommands` are load-bearing: they append
`-L<filc-glibc>/lib` and `-lpizlo -lyoloc -lyolom -lc++ -lc++abi` to
`nix-support/libc-ldflags` (which is how *every* Fil-C link acquires the
runtime), write the `ld-fil1-x86_64.so` dynamic-linker path, and install
an `ld-wrapper-hook` that strips those libraries again for relocatable
`ld -r` links (guarded by
[`tests/link-hygiene.nix`](../tests/link-hygiene.nix)).

`wrapBintoolsWith` is `makeOverridable`, and an `.override` *replaces*
arguments. Both funkyenv variants override `extraBuildCommands`:

- lld variant: `bintools.override { extraBuildCommands = ''ln -sf …/ld.lld "$out/bin/ld" …''; }`
- mold variant: `stdenvAdapters.useMoldLinker`, which does the equivalent
  replacement to symlink `ld.mold`.

Diffing the three bintools derivations (plain Fil-C, lld-funky seed 4,
mold-funky seed 4) confirms it: in both funky variants the `-lpizlo …`
line, the `ld-fil1` line, and the entire `ld-wrapper-hook` are **gone**,
leaving only the linker symlink. The suffix salt survives (filnix applies
it with `overrideAttrs` on top), which makes the failure mode nastier:
`tests/wrapper-roles` would still pass its salt assertions while every
link silently lost the Fil-C runtime.

A second, independent problem in the same diff: the symlinked linkers
come from `…-x86_64-unknown-linux-gnufilc0-llvm-binutils-wrapper-21.1.8`
and `…-x86_64-unknown-linux-gnufilc0-mold-unwrapped-wrapper-2.41.0`.
funkyenv asks for `buildPackages.llvmPackages.bintools`, intending a
build-platform tool; in filnix's spliced cross package set that resolves
to the *Fil-C-target* bintools wrapper. Fil-C binaries do run on the
Linux builder, so this might not even fail loudly — it would quietly
make the whole package set depend on a Fil-C-built lld/mold to link
itself, a bootstrap knot nobody asked for, at Fil-C build prices.

### E4 — pizlonation vs. the canary and verifier (inferred, strong)

funkyenv's verifier is a text pattern over `nm` output:

```sh
$NM -n --defined-only "$file" | sed -n 's/.* __funkyenv_canary_\([0-9]*\)$/\1/p'
```

It requires a symbol literally named `__funkyenv_canary_<n>` at end of
line. Fil-C does not emit C identifiers as ELF names
([`docs/toolchain-symbols.md`](toolchain-symbols.md)): a function
`nm_test_func` becomes the public accessor `pizlonated_nm_test_func`
plus FI/FIP signature-specific entry points and ET thunks, and
[`tests/libtool-symbols.nix`](../tests/libtool-symbols.nix) greps raw
`nm` output for exactly those prefixed names. The canary functions are
`static`, so the precise spelling of their pizlonated forms needs one
`filcc` run on a Linux builder to pin down — but on the available
evidence the verifier's pattern matches *nothing* in a Fil-C binary, so
every funky Fil-C build would fail in `postFixup` with the misleading
diagnosis "has no canary functions; it was not linked with funkyenv's
flags". The `functionOrder` audit derivation has the same class of
problem: its symbol lists would be pizlonated names and thunks, still
diffable, but not the C names a reader expects.

There is a subtler point underneath: in upstream funkyenv the canary is
deliberately compiled with the *unadapted* stdenv, i.e. it is ordinary
unshuffled-flag native code linked into every binary. In the Fil-C cross
position (E3) it accidentally becomes Fil-C code — which is what you
want on principle (an uninstrumented object in every Fil-C binary would
be a small but real hole in the "no unsafe code" story, dead or not),
but it means the canary's 32 functions also acquire Fil-C function
metadata, GC/stack-trace tables, and the FI/FIP/ET entourage. Whether
`retain` interacts with Fil-C's section handling exactly as with
GNU/LLD conventions is another swa experiment, listed in §6.

### E5 — which linkers can shuffle a Fil-C binary at all (observed + source)

Fil-C target links in filnix do not use lld or mold today. The compiler
*itself* is built with lld (`LLVM_USE_LINKER = "lld"` in
[`lib/default.nix`](../lib/default.nix)), but programs compiled *by*
Fil-C are linked by the patched GNU binutils, configured
`--enable-gold=default` — so `ld` is gold, chosen (with two local
patches) for pizlonated version-script handling and demangling. Neither
GNU ld.bfd nor gold implements `--shuffle-sections`; the flag is an
lld invention (added in 2021 to smoke out static-init-order and
pointer-comparison bugs) that mold adopted compatibly. I verified the
flag in the `--help` of nixpkgs' lld 21.1.8 and used it in E2; GNU ld
2.46 (nixpkgs) has no trace of it.

Consequence: a Fil-C funkyenv is a *linker migration* for target code,
not a flag flip. That intersects filnix specifics in three places:

1. The ccache wrapper in `toolchain/wrappers.nix` rewrites
   `-Wl,--version-script=…` into a bare `--version-script=…` because
   Fil-C's Clang driver must pizlonate version scripts before the linker
   sees them. That rewrite is driver-level and should be
   linker-independent — but every version-script user (OpenSSL is the
   named example) becomes a regression test for the new linker.
2. The patched binutils still supplies `nm`, `readelf`, `strip`, `as`
   and friends; only `ld` would change. funkyenv's verifier calls `$NM`
   and `$READELF` from the stdenv, so binutils stays in the loop.
3. funkyenv's own README warns mold cannot link glibc's dynamic loader
   and prescribes lld there. filnix has *two* glibcs (yolo-glibc and
   filc-glibc, [`runtime/`](../runtime)) plus libpizlo, all built
   upstream-style outside `pkgsFilc`. Shuffling them is a separate,
   harder project; the sane first scope shuffles only `pkgsFilc`
   programs against an unshuffled Fil-C runtime — the same stance
   funkyenv takes toward nixpkgs' bootstrap.

One more degree of freedom is worth recording: with
`-ffunction-sections`, GNU ld also lays input sections out in link-line
order, so a seeded permutation of object files *on the link line* (for
instance from the existing `ld-wrapper-hook`, which already rewrites
link arguments for `ld -r`) could shuffle with the stock gold linker and
no migration at all. The catch is that link-line order is semantically
loaded — archive member resolution depends on it — whereas
`--shuffle-sections` permutes *after* symbol resolution. Permuting only
plain `.o` arguments and leaving archives in place is probably safe, but
"probably" across all of nixpkgs is a long tail; lld's post-resolution
shuffle is the conservative choice.

### E6 — seeds, store paths, and the public caches (observed)

The seed is not a runtime secret managed outside Nix; it is baked into
derivations. The E3 hello derivation literally contains
`"__funkyShuffleSeed": 4` in its structured attrs and references a store
path named `funkyenv-lld-4.rsp`. Anyone who can read the `.drv` — from a
binary cache, a builder, or a leaked closure — learns the seed, and with
the seed and the (deterministic) linker they can recompute the layout
given the same object files. Operationally this means:

- Seeded builds must never be pushed to filnix's public caches, and
  `scripts/ship`'s publish-everything flow must exclude them by
  construction, not by discipline. Keeping shuffle *off* in the default
  `mkPkgsFilc { }` (and therefore in `scripts/ci-outputs.txt`) achieves
  that; a seeded set is a private fork of the world, built and cached
  (if at all) on infrastructure the operator controls.
- A per-seed world has per-seed store paths for everything: the E3 funky
  hello and plain hello are different derivations with different outputs
  (`l3hvls…` vs the plain build), and `-ffunction-sections` changes
  every object file, so ccache gives no cross-seed relief for compile
  work either (filnix's ccache keys on wrapper *contents*;
  the shuffle flag itself is link-only, but the section flag is not).
- Debugging gets operator-local: Fil-C stack traces resolve through its
  own tables in the binary, so shuffled binaries remain self-describing
  at trap time, but addresses from a shuffled deployment no longer match
  the public build's debug info. funkyenv's `functionOrder` passthru is
  the right antidote and should be ported with pizlonation awareness.

## 4. Where the composition is genuinely awkward

Beyond the E3/E4 breakage (fixable, see §5), four Fil-C-specific
questions need answers before trusting a shuffled Fil-C world. These are
the reasons this report recommends a staged prototype rather than a
flag day.

1. **Section-order assumptions in Fil-C's own metadata.** Fil-C emits
   more than code per function: capability/GC/stack-trace metadata lives
   in auxiliary sections that reference functions. lld's restricted form
   `--shuffle-sections=.text*=` permutes only text input sections and
   fixes up relocations, so reference-by-relocation metadata is safe by
   construction. Anything that instead assumes *paired ordering*
   (the *i*-th metadata entry describes the *i*-th function) or
   address-sorted tables built at link time from input order would
   break silently and intermittently. mold's unrestricted shuffle
   additionally permutes `.init_array`/`.fini_array` contributions and
   data sections across objects — constructor-order and
   pointer-comparison bugs are literally what lld invented this flag to
   *detect*. Verdict: lld `.text*` only, and treat the Fil-C test suite
   plus filnix's `checks` (link-hygiene, wrapper-roles, the staging
   regression set) as the gate. *Per this repo's standing rule, changes
   touching runtime/GC assumptions get an Oracle review before the
   toolchain pin moves; a linker swap for all target code qualifies.*

2. **`-ffunction-sections` under FilPizlonator.** The instrumentation
   pass already transforms every function; filnix currently uses
   `-ffunction-sections` in exactly one port (a zstd CFLAGS line in
   [`ports.nix`](../ports.nix)) and one SaRCAsm test, so there is little
   accumulated evidence either way. Risks are mundane rather than deep:
   larger objects, more sections for the linker, possible interactions
   with `--gc-sections` users (a shuffled+retained canary must survive
   GC, hence `retain`), and changed inlining/code-layout performance on
   top of Fil-C's existing overhead. Measure on the php bench
   ([`bench/php`](../bench)) before adopting world-wide.

3. **The verifier's threat model vs. stripped/symbolic realities.**
   Upstream's verifier fails closed on any `EXEC`/`DYN` without visible
   canary symbols. nixpkgs strips most binaries' symbol tables into
   separate debug outputs — upstream handles this because its hook runs
   in `postFixup` ordered after strip handling in its test set, with
   `dontVerifyFunkyenv` as the escape hatch. In `pkgsFilc`, the ports
   overlay already carries per-package quirks by the hundreds
   ([`ports/default.nix`](../ports/default.nix) DSL); a
   `dontVerifyShuffle`-style port verb fits that culture, but each use
   is a silent hole in the "everything shuffled" claim and should be
   counted, the way campaign tooling counts broken ports.

4. **What stays unshuffled is what attackers study.** Exactly as
   funkyenv leaves bootstrap glibc plain, a first filnix port leaves
   yolo-glibc, filc-glibc, libpizlo, libc++, and the loader plain — and
   those are large, stable, public binaries mapped into every Fil-C
   process. Their memory-safety posture differs (filc-glibc/libc++ are
   Fil-C-compiled; yolo-glibc and parts of libpizlo are the unsafe
   island), so the unshuffled residue overlaps with the least-protected
   code. This does not make phase 1 useless — the *program* (php-fpm and
   its extensions) is where the bugs and the call targets are — but the
   report to users must not overclaim, and shuffling the runtime (lld
   against two glibcs, mold excluded by the loader problem) is the
   natural phase 2, with the loader as its crux experiment.

## 5. Proposed design: `mkPkgsFilc { shuffleSeed = …; }`

filnix already has the right seam. `mkPkgsFilc` in
[`flake.nix`](../flake.nix) accepts `staging`, `blockRustGo`, and
`crossOverlays`, and builds the cross stdenv by
`baseStdenv.override { cc = filcc; }`. A seed belongs next to those
knobs, threaded into `toolchain.nix` → `toolchain/wrappers.nix`, so
that *the Fil-C wrapper itself* grows the shuffle instead of an outside
adapter fighting it:

```nix
# flake.nix (sketch)
mkPkgsFilc = { staging ? false, blockRustGo ? false,
               crossOverlays ? [ ], shuffleSeed ? null }:
  let cc = (if staging then filcc-staging else filcc);
      cc' = if shuffleSeed == null then cc
            else cc.overrideShuffle shuffleSeed;   # wrappers.nix
  in … baseStdenv.override { cc = cc'; } …
```

Inside `toolchain/wrappers.nix`, the shuffle variant of `filc-bintools`
must **append to, never replace**, the existing `extraBuildCommands`:

```sh
# added after filnix's own libc-ldflags / dynamic-linker / ld-wrapper-hook lines
ln -sf ${nativeLld}/bin/ld.lld "$out/bin/ld"
```

where `nativeLld` is explicitly the *build platform's*
`pkgs.llvmPackages.bintools` (the `pkgs` that `toolchain.nix` already
receives is the build package set — this is the one place in the design
where being inside filnix rather than in a cross overlay makes the
correct tool the easy one, fixing E3's splicing knot by construction).
GNU `nm`/`readelf`/`as`/`strip` from the patched binutils remain; only
`ld` changes, and the `ld -r` hook keeps working because it lives in
the bintools wrapper's `nix-support`, above whichever `ld` binary sits
underneath.

The remaining pieces, each small:

- **Flags via wrapper `nix-support`, not derivation env.** Put
  `-ffunction-sections` into the cc-wrapper's `cc-cflags` file
  (alongside the existing `-Wno-unused-command-line-argument` and
  `-gz=none` lines) and `@…/shuffle.rsp` plus the canary object into a
  `*-ldflags` file the wrapper always applies. This is strictly more
  robust than upstream's `env.NIX_LDFLAGS`, which builds can (and some
  ports do) overwrite; it also makes the shuffle part of the wrapper's
  identity, so filnix's content-keyed ccache distinguishes seeded from
  unseeded objects correctly. It must use the salted flag channels the
  wrapper already reads (`NIX_LDFLAGS_x86_64_unknown_linux_gnufilc0`
  discipline from `tests/wrapper-roles`), which falling out of
  `nix-support` gives for free.
- **Canary compiled by filcc, verifier pattern learned from filcc.**
  Build `funkyenv-canary.o` inside `wrappers.nix` with the Fil-C
  compiler (a tiny `runCommand` on the builder, like `filc-cc`), then
  write the verifier's `sed` pattern against the *observed* pizlonated
  spelling. Run the check as a cc-wrapper setup hook next to the
  existing libtool/autoconf/header hooks, so it applies to everything
  the stdenv builds without per-derivation `nativeBuildInputs` edits.
  Keep upstream's fail-closed semantics and `dontVerify…` escape, named
  in filnix style, and surface the escape as a verb in the ports DSL so
  campaign tooling can enumerate unshuffled exceptions.
- **`functionOrder` passthru** on the seeded stdenv's `mkDerivation`,
  as upstream does, but reporting both raw pizlonated names and
  demangled C names (filnix's patched `nm -C` already strips
  `pizlonated_` unless `FILC_PRESERVE_PREFIX` is set — reuse it).
- **NixOS surface:** `filc.shuffleSeed` (null or int) in
  `nixos/filc.nix`, applied by rebuilding `filc.packages` via
  `mkPkgsFilc { shuffleSeed = cfg.shuffleSeed; }`, with documentation
  that this (a) forks the world, (b) must not point at the public
  caches, and (c) composes with — does not replace — upstream funkyenv
  on the native side for systemd/glibc and other native services.
- **Seed hygiene in-repo:** never commit a real seed; the NixOS option
  should accept a path to a file outside the store-evaluated config if
  we ever want `nixosConfigurations` examples (a seed in a public repo
  is a public seed). CI's `checks` use seed 4, like upstream.

Explicit non-goals for phase 1: shuffling the runtime/glibcs/loader
(E5.3, phase 2), the mold variant (unrestricted section shuffle is the
wrong default under Fil-C metadata, §4.1, and mold is doubly excluded
once loaders enter scope), link-line permutation under gold (E5,
interesting but the archive-order tail-risk is unnecessary), and any
seed-by-default (the public-cache workflow in `scripts/ship` depends on
one canonical world).

## 6. Recommendation and staged plan

**Adopt the idea, as §5, in stages; do not adopt the overlay.** Each
stage is independently stoppable, and stages 0–1 are an afternoon on
swa:

0. **Pin the unknowns (swa, `x86_64-linux`).** Compile `canary.c` with
   `filcc -ffunction-sections`; record the exact ELF names/sections for
   the static retain functions and their FI/FIP/ET companions; link a
   hello-world and `pkgsFilc.hello` with `ld.lld
   --shuffle-sections=.text*=4` by hand; run them; run
   `checks.libtool-symbols`, `checks.link-hygiene`,
   `checks.wrapper-roles` against an lld-swapped bintools. This
   converts every "inferred" in E4/§4 into observed fact. *Consult
   Oracle on §4.1 (linker/metadata soundness) before stage 2, per repo
   policy for runtime-adjacent changes.*
1. **Prototype behind `mkPkgsFilc { shuffleSeed = 4; }`** exactly as §5,
   with one new check mirroring upstream's: a PHP whose
   interpreter + extensions verify as shuffled (filnix's PHP port
   already builds extensions inside the cross set, so unlike nixpkgs
   no `newScope` trick should be needed — confirm via the verifier,
   which is its raison d'être), plus a NixOS VM test modeled on
   funkyenv's `tests/wordpress.nix` but asserting *both* layers:
   the process maps the Fil-C runtime (`ld-fil1`, `libc.so.6666` —
   the existing `tests/nixos` assertions) *and* its canaries are
   permuted. That single test is the whole thesis in one place.
2. **Measure, then widen.** `bench/php` before/after (build time, binary
   size, request latency); build the `ci-outputs` set seeded on swa
   *without publishing*; count `dontVerify` exceptions the ports need.
   Only then consider stage 3.
3. **Runtime shuffle (phase 2, optional).** lld for filc-glibc/libc++/
   libpizlo first, yolo-glibc + loader last and only if the loader
   experiment passes. This is the upstream "shuffle glibc separately"
   story, doubled.

If stage 0 shows Fil-C metadata *does* depend on input-section order,
the fallback is not mold (worse) but giving up on program-text shuffle
and keeping funkyenv for the native side of filnix systems only —
still a coherent, useful outcome, and §2's table says the Fil-C side
loses the least of any code in the system.

## Appendix: reproducing the experiments

- E1: flake in `/tmp/exp1` consuming `git+file:///private/tmp/funkyenv`
  (upstream @ `deabcca`), `hello.override` with each stdenv variant on
  `aarch64-darwin`.
- E2: `/tmp/exp2.sh` under
  `nix shell nixpkgs#lld nixpkgs#llvm nixpkgs#mold nixpkgs#binutils`;
  objects in `/tmp/exp2/`.
- E3/E6: `/tmp/exp3.nix`, `/tmp/exp4.nix` against this repo's
  `lib.x86_64-linux.mkPkgsFilc` with
  `crossOverlays = [ (import /private/tmp/funkyenv/overlay.nix) ]`;
  derivation diffs via `nix derivation show` / `strings` on the plain
  (`pwl976…`), lld-funky (`zibxnl…`), and mold-funky (`38admi…`)
  `binutils-wrapper-2.43.1` derivations, and on the funky hello
  derivation `wyl1sq…` vs plain `hrih2a…`.

Upstream sources consulted: funkyenv `README.md`, `funkyenv.nix`,
`overlay.nix`, `canary.c`, `verify-shuffle.sh`, `function-order.sh`,
`flake.nix`, `tests/wordpress.nix` (all at `deabcca`). filnix sources:
[`flake.nix`](../flake.nix) (`mkPkgsFilc`),
[`toolchain.nix`](../toolchain.nix),
[`toolchain/wrappers.nix`](../toolchain/wrappers.nix),
[`toolchain/binutils.nix`](../toolchain/binutils.nix),
[`lib/default.nix`](../lib/default.nix),
[`nixos/filc.nix`](../nixos/filc.nix),
[`docs/toolchain-symbols.md`](toolchain-symbols.md),
[`tests/link-hygiene.nix`](../tests/link-hygiene.nix),
[`tests/wrapper-roles.nix`](../tests/wrapper-roles.nix),
[`tests/libtool-symbols.nix`](../tests/libtool-symbols.nix),
[`scripts/ship`](../scripts/ship),
[`scripts/ci-outputs.txt`](../scripts/ci-outputs.txt).
