# Fil-C symbols and libtool

Fil-C's ELF names are not C identifiers. For example, compiling
`int nm_test_var; void nm_test_func(void) {}` produces the public accessors
`pizlonated_nm_test_var` and `pizlonated_nm_test_func`, as well as FI/FIP
signature-specific entry points, ET thunks, and native runtime references.
Libtool's default `nm` probe tries to redeclare all of these as C identifiers.
Fil-C then adds another ABI prefix, so linking the probe fails. Configure can
continue with an empty `global_symbol_pipe`, breaking later export-list builds.

The compiler wrapper installs `toolchain/libtool-setup-hook.sh`. Just before
configure, after package patches and autoreconf, it runs
`toolchain/libtool-symbols.py` on generated configure scripts, including bundled
subprojects and an explicit out-of-tree `configureScript`. It preserves mtimes
and only acts when Fil-C is the selected host compiler.

Libtool already models a platform symbol prefix. The hook changes its candidate
prefixes from `"" "_"` to `"pizlonated_"`. Its normal compile/link probe still runs;
no cache result is forced. The resulting pipeline has three columns:

```text
T pizlonated_nm_test_func nm_test_func
```

The raw ELF name and C name remain distinct. Helper entry points do not match
the prefix. Generated C declarations, preloaded symbol tables, and source-name
export regexes use libtool's existing machinery. Plain `nm`, `$NM`, and explicit
binutils paths retain their real output and normal exit status. This replaces
all 17 `depizloing-nm` uses and the gettext/unbound `fixSympat` uses.

The upstream gettext patch used to prefix every name in
`libtextstyle.sym.in`. That hunk is removed: gettext also compares this list
against C names to generate namespace-hiding macros. The list must contain C
names; the Fil-C compiler wrapper already passes linker version scripts through
Clang for ABI translation. Keeping prefixes here would incorrectly rename the
public API. The other upstream gettext fixes remain applied.

## Bernstein's binutils patch

The checked-in patch comes from [djb's Filian compiler installation script](https://cr.yp.to/2025/20251030-filian-install-compiler.sh).
It changes `bfd_demangle`, so `nm -C` can remove the old `pizlonated_` prefix;
plain `nm` does not call that path. It also does not account for the newer FI/FIP
and ET symbols. `FILC_PRESERVE_PREFIX` disables its prefix removal. The separate
experimental `binutils-version-script-depizlonation.patch` is not applied.
Neither demangling nor version-script matching solves libtool's raw-name/C-name
problem. The existing binutils build and linker behavior are unchanged.

## Verification

```sh
nix build .#checks.x86_64-linux.libtool-symbols
nix build --no-link \
  .#legacyPackages.x86_64-linux.pkgsFilc.expat \
  .#legacyPackages.x86_64-linux.pkgsFilc.libffi \
  .#legacyPackages.x86_64-linux.pkgsFilc.lzo \
  .#legacyPackages.x86_64-linux.pkgsFilc.pkgconf-unwrapped \
  .#legacyPackages.x86_64-linux.pkgsFilc.gdbm \
  .#legacyPackages.x86_64-linux.pkgsFilc.gmp \
  .#legacyPackages.x86_64-linux.pkgsFilc.gettext \
  .#legacyPackages.x86_64-linux.pkgsFilc.ldns \
  .#legacyPackages.x86_64-linux.pkgsFilc.libssh2 \
  .#legacyPackages.x86_64-linux.pkgsFilc.unbound
```

The focused check generates configure with autoreconf in `preConfigure`, checks
raw/C symbol columns and C declarations, builds and runs a libtool `-dlpreopen`
program, and builds and runs against a shared library with an export regex.
It also checks bundled and out-of-tree configure discovery, idempotence, mtime
preservation, native-compiler isolation, and `nm` failure status.

This integration is downstream of the compiler and runtime builds. Comparing
recursive `filcc` derivation graphs before and after the change replaced only
the final cc-wrapper and added its setup-hook derivation; all 982 existing
dependencies, including LLVM, binutils, libc, and libc++, remained identical.

All ten package builds above completed with successful real libtool probes
(gettext has five). The focused check passed; removing the setup hook reproduced
the original failed probe. Separate public-API smoke programs compiled, linked,
and ran against ldns, libssh2, and libtextstyle, including a libtextstyle global
variable. The installed gettext executable also ran successfully.
