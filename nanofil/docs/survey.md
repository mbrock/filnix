# Package survey

How much of the C in filnix's ports builds with nanofil alone, and what
stops the rest. Unlike the program checks (PLAN.md, M4), the survey is
not part of the Nix check and fixes nothing: it measures.

## Method

[survey/default.nix](../survey/default.nix) defines `nanofilize`, a
package adapter over the Fil-C staging package set: the package's
`CC` is [survey/cc.sh](../survey/cc.sh), which hands every compile of C
to nanofil-cc, one source at a time (a compile-and-link `cc -o x x.c`,
as configure's probes do, too). Preprocessing, assembling and linking go
to filcc, since they compile no C. A C compile nanofil-cc cannot take
(`-S`, or C on stdin or in a file without a `.c` suffix) is logged as a
fallback and refused, never compiled by clang, so a package builds with
nanofil alone or fails. C++ still goes to filcc and is counted
([survey/cxx.sh](../survey/cxx.sh)). Libraries a package links with are
the staging set's, built by filcc; each package's own checkPhase and
installCheckPhase run as the port runs them.

[survey/run.py](../survey/run.py) takes the packages ports.nix names,
sets aside those that do not evaluate, those whose sources hold more
than half as many C++ files as C files, and those with no C sources,
builds each of the rest with filcc and then (where filcc's build
succeeds) with nanofil, and writes [survey/survey.tsv](../survey/survey.tsv)
and the table below. Rerun it from the repository root:

```sh
python3 nanofil/survey/run.py --jobs 6 --cores 3        # all of them
python3 nanofil/survey/run.py zlib xz                   # some
nix build -f nanofil/survey nf.zlib                     # one, by hand
python3 nanofil/survey/run.py --report                  # tables from survey.tsv
```

Builds already in the store are reused, and only `bin/` and `src/` of
nanofil enter the nanofil builds, so a rerun after a compiler change
rebuilds only those.

"filcc" and "nanofil" say `tests pass` when the build ran its own tests
and they passed, `built` when it has none (or the port skips them),
`tests fail` when the build failed in a check phase, and `fails in
PHASE` otherwise. The first error is the first of nanofil's own
messages, the wrapper's refusal, configure's verdict, or a compiler or
make error, in that order.

## Results

The survey of 2026-10-28, at `0ad8d8b`: of the 300 packages ports.nix
names, 209 are C. filcc builds 201 of them. Of those 201, nanofil alone
builds 61 (30%). The 18 among them whose ports run tests pass them, as
filcc's builds do; no built package's tests disagree with filcc's. One
more (nspr) builds its libraries but fails linking its tests. The other
139 fail: 127 while building and 12 in configure. The 61 built ones
compiled 10,173 objects with nanofil. 15 of them also hold some C++
(capstone, cups, expat, …), which filcc compiled. libselinux and libsepol
logged a few refused compiles that their builds tolerated.

The packages built are bash, capstone, cmocka, cups, duktape, e2fsprogs,
expat, file, freetype, gawk, gnu-shepherd, gnumake, gnutar, gsl, imlib2,
jq, libarchive, libcap_ng, libcbor, libedit, libepoxy, libev, libevdev,
libglvnd, libidn2, liblc3, libmhash, libmpdclient, libpng, libraqm,
libselinux, libsepol, libshout, libssh2, libtasn1, libvmaf, libxml2, lzo,
minizip, mpdecimal, mpfr, nghttp2, oniguruma, pixman, pth, recode, runit,
scrypt, seatd, spandsp, sqlite, torsocks, ttyd, uwimap, wasm3, wavpack,
wayland, x264, xvidcore and zlib (and bashNonInteractive).

Several programs with nanofil checks (dash, xz, coreutils, sed, CPython)
fail here. Their checks build their own configurations, with configure
cache variables and flags chosen for nanofil; the survey builds each
port as it stands.

### Causes

Each failure counts once, under its first error. Removing that cause
gets a package to its next error, not necessarily to a build. Six
configure verdicts trace to the same causes through a probe (see
[run.py](../survey/run.py)'s `CAUSES`):

- **Threads.** The probe for `-pthread` (fftw, kronosnet, krb5,
  libmicrohttpd, pcre2, tpm2-abrmd) expands glibc's
  `pthread_cleanup_push`, which declares a local
  `__attribute__((__aligned__))`, so it counts under alignment attributes.
- **C89 and C99.** Autoconf 2.70's C89 probe has a K&R definition. Every
  autoconf configure therefore concludes the compiler is not C89. For
  gnupg ("No C-89 compiler found") and liburcu ("does not support C99")
  that is fatal.
- **Redeclarations.** nanofil accepts an incompatible redeclaration of a
  library function (C11 6.7p4), which clang refuses. gnulib's strerror_r
  probe therefore picks the POSIX signature under glibc's GNU one, and
  perror.c fails to compile (bison, coreutils, diffutils, grep, m4, sed).
  curl's prototype-mismatch probe fails the same way.
- **Others.** cryptsetup's libdevmapper.h declares a constructor it does
  not define (as libgpg-error's gpg_err_init does). gmp's probe passes
  arguments to a function defined with `()`, which nanofil refuses at
  compile time and clang accepts.

The three causes that would unblock the most packages:

1. **Alignment attributes** (23): `aligned` on locals, members and types,
   including glibc's pthread cancellation buffer.
2. **The generic `__atomic` builtins** (20): `__atomic_load(p, &v, order)`
   and `__atomic_compare_exchange`. The `_n` forms already work. 19 of
   the 20 are GLib's `g_once_init_enter` and `g_atomic_*` macros (in
   gtype.h, generated enum types, and GLib itself), so `__atomic_load` is
   what keeps the whole GLib and GTK stack out.
3. **Missing GCC builtins** (22, as two rows below):
   - `__builtin_types_compatible_p` and `__builtin_choose_expr` (9:
     systemd, util-linux, git, tor, pam, …);
   - `__builtin_assume`, `__builtin_prefetch`, `__builtin_ffsl`,
     `__builtin_isinf`, `__builtin_memcpy`, `__builtin_return_address` and
     x86 intrinsics (13).

   Constant expressions nanofil does not fold come next (13), but
   they are of several kinds, for example an address laundered through
   `uintptr_t` in a static initializer (lighttpd).

<!-- survey table -->

| Set aside | Packages |
| --- | ---: |
| C++ | 59 |
| evaluation fails | 20 |
| no C sources found | 12 |

| filcc | nanofil | Packages |
| --- | --- | ---: |
| built | fails in buildPhase | 79 |
| tests pass | fails in buildPhase | 48 |
| built | built | 43 |
| tests pass | tests pass | 18 |
| built | fails in configurePhase | 7 |
| tests pass | fails in configurePhase | 5 |
| dependency fails | not tried | 4 |
| fails in buildPhase | not tried | 2 |
| tests fail | not tried | 2 |
| tests pass | tests fail | 1 |

| Cause | Packages | Which |
| --- | ---: | --- |
| alignment attributes | 23 | dav1d, dbus, fftw, graphene, gtksourceview4, kbd, krb5, kronosnet, libaom, libcap, libcdio, libffi, libhandy, libmicrohttpd, libsodium, libvpx, mailutils, pcre2, quickjs, rhash, svt-av1, tpm2-abrmd, zlib-ng |
| generic __atomic builtins | 20 | at-spi2-core, cairo, dconf, gdk-pixbuf, glib, gssdp_1_6, gtk3, gtk4, gtksourceview3, json-glib, libdbusmenu, libgit2, libgudev, libhighscore, libical, libmbim, libsoup_3, pango, polkit, vala |
| other syntax or typing gaps | 17 | bind, binutils-unwrapped, emacs30, finit, gupnp_1_6, kittydoom, libevent, libjpeg_turbo, libseccomp, libxkbcommon, openssl, openssl-sarcasm, parted, python312, ruby_3_3, unbound, zix |
| constant expressions not folded | 13 | busybox, dbus-glib, gobject-introspection-unwrapped, guile-avahi, guile_3_0, libgsf, libiconv, libxcrypt, lighttpd, nettle, p11-kit, tinycc, weston |
| other builtins | 13 | cogl, ghostscript, gnutls, imagemagick, isa-l, libgbm, libpq, libuv, mbedtls, netcdf, perl5, redis, zstd |
| inline or top-level asm | 12 | ell, flac, fstrm, libapparmor, libblake3, libdeflate, libressl, nss, openssh, physfs, rdkafka, xz |
| K&R definitions | 10 | a2ps, cyrus_sasl, dash, db53, gd, gnupg, libtirpc, liburcu, potrace, rpcbind |
| __builtin_types_compatible_p, __builtin_choose_expr | 9 | btrfs-progs, gettext, git, mariadb-connector-c_3_3, pam, systemd, tor, tpm2-tss, util-linux |
| incompatible redeclarations accepted | 7 | bison, coreutils, curl, diffutils, gnugrep, gnum4, gnused |
| aliases beyond one prototyped function | 4 | alsa-lib, elfutils, fontconfig, gtk2 |
| constructor on a declaration | 3 | cryptsetup, libgcrypt, libgpg-error |
| vector types | 3 | libopus, libtiff, libwebp |
| GNU case ranges | 2 | libinput, procps |
| unresolved Fil-C symbol at link | 2 | keyutils, nspr |
| calls passing arguments to a () function | 1 | gmp |
| nanofil internal failure | 1 | trealla |

| Package | Version | filcc | nanofil | nanofil objects | Cause | First error |
| --- | --- | --- | --- | ---: | --- | --- |
| a2ps | 4.15.7 | tests pass | fails in buildPhase | 258 | K&R definitions | `nanofil: regex.c:813: K&R-style parameter lists are not supported, at )` |
| alsa-lib | 1.2.15.3 | built | fails in buildPhase | 66 | aliases beyond one prototyped function | `nanofil: control.c:2974: alias is supported only for one prototyped, non-variadic function` |
| at-spi2-core | 2.60.5 | built | fails in buildPhase | 72 | generic __atomic builtins | `nanofil: atk/atk-enum-types.c:15: undeclared identifier __atomic_load` |
| bash | 5.3p9 | built | built | 570 |  |  |
| bashNonInteractive | 5.3p9 | built | built | 575 |  |  |
| bind | 9.20.30 | tests pass | fails in buildPhase | 190 | other syntax or typing gaps | `nanofil: async.c:60: cannot assign ptr(struct(98)) to union(100)` |
| binutils-unwrapped | 2.43.1 | built | fails in buildPhase | 619 | other syntax or typing gaps | `nanofil: /build/binutils-2.43.1/libiberty/hashtab.c:238: expected an expression, at typedef` |
| bison | 3.8.2 | built | fails in buildPhase | 330 | incompatible redeclarations accepted | `nanofil: lib/perror.c:41: cannot assign ptr(char) to int` |
| bluez | 5.86 | fails in buildPhase | not tried |  |  |  |
| btrfs-progs | 6.19.1 | tests pass | fails in buildPhase | 112 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: ./kernel-shared/misc.h:74: __builtin_types_compatible_p is not supported, at (` |
| busybox | 1.37.0 | built | fails in configurePhase | 6 | constant expressions not folded | `nanofil: scripts/kconfig/zconf.hash.c:161: initializer is not a constant` |
| cairo | 1.18.4 | built | fails in buildPhase | 268 | generic __atomic builtins | `nanofil: ../util/cairo-gobject/cairo-gobject-enums.c:12: undeclared identifier __atomic_load` |
| capstone | 5.0.7 | tests pass | tests pass | 128 |  |  |
| cmocka | 2.0.1 | built | built | 82 |  |  |
| cogl | 1.22.8 | built | fails in buildPhase | 95 | other builtins | `nanofil: driver/gl/cogl-framebuffer-gl.c:418: undeclared identifier __builtin_ffsl` |
| coreutils | 9.11 | built | fails in buildPhase | 1228 | incompatible redeclarations accepted | `nanofil: perror.c:40: cannot assign ptr(char) to int` |
| cryptsetup | 2.8.6 | tests pass | fails in configurePhase | 51 | constructor on a declaration | `configure: error: You need the device-mapper library.` |
| cups | 2.4.19 | built | built | 244 |  |  |
| curl | 8.22.0 | built | fails in configurePhase | 39 | incompatible redeclarations accepted | `configure: error: compiler does not halt on function prototype mismatch.` |
| cyrus_sasl | 2.1.28 | built | fails in buildPhase | 194 | K&R definitions | `nanofil: md5.c:433: K&R-style parameter lists are not supported, at ,` |
| dash | 0.5.12 | built | fails in buildPhase | 68 | K&R definitions | `nanofil: exec.c:773: K&R-style parameter lists are not supported, at ,` |
| dav1d | 1.5.3 | tests pass | fails in buildPhase | 27 | alignment attributes | `nanofil: ../src/fg_apply_tmpl.c:231: alignment attributes is not supported` |
| db53 | 5.3.28 | tests pass | fails in buildPhase | 205 | K&R definitions | `nanofil: ../lang/db185/db185.c:42: K&R-style parameter lists are not supported, at ,` |
| dbus | 1.16.2 | tests pass | fails in buildPhase | 191 | alignment attributes | `nanofil: ../dbus/dbus-mempool.c:310: sizeof: alignment attributes` |
| dbus-glib | 0.114 | built | fails in buildPhase | 42 | constant expressions not folded | `nanofil: dbus-binding-tool-glib.c:1067: case label is not a constant` |
| dconf | 0.49.0 | tests pass | fails in buildPhase | 18 | generic __atomic builtins | `nanofil: ../shm/dconf-shm.c:36: undeclared identifier __atomic_load` |
| diffutils | 3.12 | built | fails in buildPhase | 541 | incompatible redeclarations accepted | `nanofil: perror.c:41: cannot assign ptr(char) to int` |
| duktape | 2.7.0 | built | built | 8 |  |  |
| e2fsprogs | 1.47.4 | built | built | 555 |  |  |
| elfutils | 0.194 | built | fails in buildPhase | 187 | aliases beyond one prototyped function | `nanofil: elf_getshdrnum.c:87: alias is supported only for one prototyped, non-variadic function` |
| ell | 0.83 | built | fails in buildPhase | 50 | inline or top-level asm | `nanofil: ell/util.c:794: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| emacs30 | 30.1 | built | fails in buildPhase | 442 | other syntax or typing gaps | `nanofil: ./dynlib.h:33: expected a declaration, at typedef` |
| expat | 2.7.1 | tests pass | tests pass | 89 |  |  |
| ffmpeg-headless | 8.1.2 | dependency fails | not tried |  |  |  |
| fftw | 3.3.11 | tests pass | fails in configurePhase | 138 | alignment attributes | `configure: error: couldn't find threads library for --enable-threads` |
| file | 5.47 | built | built | 141 |  |  |
| finit | 4.17 | built | fails in buildPhase | 56 | other syntax or typing gaps | `nanofil: getty.c:407: bad number 1i` |
| flac | 1.5.0 | tests pass | fails in buildPhase | 37 | inline or top-level asm | `nanofil: /build/flac-1.5.0/src/libFLAC/cpu.c:80: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| fontconfig | 2.17.1 | built | fails in buildPhase | 108 | aliases beyond one prototyped function | `nanofil: ./fcaliastail.h:268: alias is supported only for one prototyped, non-variadic function` |
| freetype | 2.14.3 | tests pass | tests pass | 135 |  |  |
| fstrm | 0.6.1 | tests pass | fails in buildPhase | 56 | inline or top-level asm | `nanofil: libmy/my_queue_mb.c:132: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| gawk | 5.4.1 | built | built | 277 |  |  |
| gd | 2.3.3 | built | fails in buildPhase | 77 | K&R definitions | `nanofil: gd_nnquant.c:115: K&R-style parameter lists are not supported, at ,` |
| gdk-pixbuf | 2.44.7 | built | fails in buildPhase | 61 | generic __atomic builtins | `nanofil: gdk-pixbuf/gdk-pixbuf-enum-types.c:13: undeclared identifier __atomic_load` |
| gettext | 1.0 | built | fails in buildPhase | 1580 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: string-buffer.c:166: undeclared identifier __builtin_choose_expr` |
| ghostscript | 10.07.1 | built | fails in buildPhase | 350 | other builtins | `nanofil: ./brotli/c/enc/hash_longest_match_inc.h:176: undeclared identifier __builtin_prefetch` |
| git | 2.46.0 | built | fails in buildPhase | 77 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: hex.c:114: __builtin_types_compatible_p is not supported, at (` |
| glib | 2.80.4 | built | fails in buildPhase | 389 | generic __atomic builtins | `nanofil: ../glib/deprecated/gthread-deprecated.c:512: undeclared identifier __atomic_load` |
| gmp | 6.3.0 | tests pass | fails in configurePhase | 30 | calls passing arguments to a () function | `configure: error: could not find a working compiler, see config.log for details` |
| gnu-shepherd | 1.0.9 | built | built | 240 |  |  |
| gnugrep | 3.12 | built | fails in buildPhase | 509 | incompatible redeclarations accepted | `nanofil: perror.c:41: cannot assign ptr(char) to int` |
| gnum4 | 1.4.21 | built | fails in buildPhase | 631 | incompatible redeclarations accepted | `nanofil: perror.c:40: cannot assign ptr(char) to int` |
| gnumake | 4.4.1 | tests pass | tests pass | 153 |  |  |
| gnupg | 2.4.9 | tests pass | fails in configurePhase | 20 | K&R definitions | `configure: error: No C-89 compiler found` |
| gnused | 4.10 | built | fails in buildPhase | 476 | incompatible redeclarations accepted | `nanofil: perror.c:40: cannot assign ptr(char) to int` |
| gnutar | 1.35 | tests pass | tests pass | 596 |  |  |
| gnutls | 3.8.13 | built | fails in buildPhase | 665 | other builtins | `nanofil: key_share.c:256: undeclared identifier __builtin_return_address` |
| gobject-introspection-unwrapped | 1.80.1 | tests pass | fails in buildPhase | 107 | constant expressions not folded | `nanofil: ../girepository/gdump.c:556: case label is not a constant` |
| graphene | 1.10.8 | tests pass | fails in buildPhase | 47 | alignment attributes | `nanofil: ../src/graphene-box.c:68: sizeof: alignment attributes` |
| gsl | 2.8 | tests pass | tests pass | 1060 |  |  |
| gssdp_1_6 | 1.6.6 | tests pass | fails in buildPhase | 19 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| gtk2 | 2.24.33 | built | fails in buildPhase | 95 | aliases beyond one prototyped function | `nanofil: ../../gdk/gdkaliasdef.c:722: alias is supported only for one prototyped, non-variadic function` |
| gtk3 | 3.24.52 | built | fails in buildPhase | 67 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| gtk4 | 4.14.5 | built | fails in buildPhase | 83 | generic __atomic builtins | `nanofil: gtk/css/gtkcssenumtypes.c:13: undeclared identifier __atomic_load` |
| gtksourceview3 | 3.24.11 | tests pass | fails in buildPhase | 85 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| gtksourceview4 | 4.8.4 | tests pass | fails in buildPhase | 67 | alignment attributes | `nanofil: gtksourceview/gtksourceview-gresources.c:9: alignment attributes is not supported` |
| guile-avahi | 0.4.1 | tests pass | fails in buildPhase | 43 | constant expressions not folded | `nanofil: src/errors.c:25: initializer is not a constant` |
| guile_3_0 | 3.0.11 | built | fails in buildPhase | 656 | constant expressions not folded | `nanofil: array-map.c:386: initializer is not a constant` |
| gupnp_1_6 | 1.6.10 | tests pass | fails in buildPhase | 15 | other syntax or typing gaps | `nanofil: ../tests/test-context.c:447: cannot type call(id(soup_message_new),[cast(type([qual(const),tspec(char)],ptr(base,[])),cond(stmtexpr(at(../tests/test-context.c:447,block([static_assert(../tests/test-context.c:447,bin(eq,sizeof_expr(un(deref,un(addr,id(_SOUP_METHOD_GET)))),sizeof_type(type([t` |
| imagemagick | 7.1.2-31 | built | fails in buildPhase | 313 | other builtins | `nanofil: MagickCore/cache.c:5214: undeclared identifier __builtin_prefetch` |
| imlib2 | 1.12.6 | built | built | 133 |  |  |
| isa-l | 2.32.0 | tests pass | fails in buildPhase | 51 | other builtins | `nanofil: /nix/store/asx904awk86a38cr62zyxqq1zf10603m-filc0-resource-dir/lib/clang/20/include/crc32intrin.h:73: undeclared identifier __builtin_ia32_crc32si` |
| jq | 1.8.2 | built | built | 149 |  |  |
| json-glib | 1.10.8 | tests pass | fails in buildPhase | 47 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| kbd | 2.9.0 | built | fails in buildPhase | 103 | alignment attributes | `nanofil: kbdfile-zlib.c:29: alignment attributes is not supported` |
| keyutils | 1.6.3 | built | fails in buildPhase | 8 | unresolved Fil-C symbol at link | `./libkeyutils.so: error: undefined reference to 'pizlonated_zargs'` |
| kittydoom | git | built | fails in buildPhase | 1 | other syntax or typing gaps | `nanofil: src/PureDOOM.h:16108: invalid operands to and: int and double` |
| krb5 | 1.22.2 | built | fails in configurePhase | 71 | alignment attributes | `configure: error: cannot determine options for enabling thread support; try --disable-thread-support` |
| kronosnet | 1.33 | built | fails in configurePhase | 38 | alignment attributes | `configure: error: POSIX threads support is required` |
| libaom | 3.12.1 | built | fails in buildPhase | 49 | alignment attributes | `nanofil: /build/source/av1/common/filter.h:111: alignment attributes is not supported` |
| libapparmor | 4.1.7 | built | fails in buildPhase | 47 | inline or top-level asm | `nanofil: kernel.c:832: top-level asm is not supported, at (` |
| libarchive | 3.7.4 | built | built | 425 |  |  |
| libblake3 | 1.8.5 | built | fails in buildPhase | 4 | inline or top-level asm | `nanofil: /build/source/c/blake3_dispatch.c:70: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| libcap | 2.70 | built | fails in buildPhase | 9 | alignment attributes | `nanofil: ../psx/psx.c:477: alignment attributes is not supported` |
| libcap_ng | 0.9.3 | tests pass | tests pass | 67 |  |  |
| libcbor | 0.13.0 | tests pass | tests pass | 134 |  |  |
| libcdio | 2.3.0 | tests pass | fails in buildPhase | 136 | alignment attributes | `nanofil: image/nrg.c:195: buf has a type nanofil does not support (alignment attributes)` |
| libdbusmenu | 16.04.0 | built | fails in buildPhase | 41 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| libdeflate | 1.25 | tests pass | fails in buildPhase | 20 | inline or top-level asm | `nanofil: /build/source/lib/x86/cpu_features.c:47: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| libedit | 20240808-3.1 | built | built | 115 |  |  |
| libepoxy | 1.5.10 | tests pass | tests pass | 71 |  |  |
| libev | 4.33 | built | built | 55 |  |  |
| libevdev | 1.11.0 | built | built | 59 |  |  |
| libevent | 2.1.13 | built | fails in buildPhase | 188 | other syntax or typing gaps | `nanofil: bufferevent_filter.c:619: expected an expression, at attribute` |
| libffi | 3.8.0 | tests pass | fails in buildPhase | 61 | alignment attributes | `nanofil: ../src/types.c:53: alignment attributes is not supported` |
| libgbm | 26.0.3 | built | fails in buildPhase | 148 | other builtins | `nanofil: ../src/util/cache_ops_x86.c:68: undeclared identifier __builtin_ia32_mfence` |
| libgcrypt | 1.12.2 | tests pass | fails in buildPhase | 104 | constructor on a declaration | `nanofil: the ctor gpg_err_init is not defined in this translation unit` |
| libgit2 | 1.9.7 | tests pass | fails in buildPhase | 63 | generic __atomic builtins | `nanofil: /build/source/src/util/thread.h:168: undeclared identifier __atomic_compare_exchange` |
| libglvnd | 1.7.0 | built | built | 81 |  |  |
| libgpg-error | 1.59 | tests pass | fails in buildPhase | 118 | constructor on a declaration | `nanofil: the ctor gpg_err_init is not defined in this translation unit` |
| libgsf | 1.14.58 | tests pass | fails in buildPhase | 84 | constant expressions not folded | `nanofil: gsf-libxml.c:216: case label is not a constant` |
| libgudev | 238 | built | fails in buildPhase | 11 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| libhandy | 1.8.3 | tests pass | fails in buildPhase | 49 | alignment attributes | `nanofil: examples/handy-demo-resources.c:9: alignment attributes is not supported` |
| libhighscore | 0-unstable-2026-04-01 | tests pass | fails in buildPhase | 62 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| libical | 3.0.20 | built | fails in buildPhase | 98 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| libiconv | 1.19 | built | fails in buildPhase | 234 | constant expressions not folded | `nanofil: lib/aliases.gperf:834: initializer is not a constant` |
| libidn2 | 2.3.8 | built | built | 227 |  |  |
| libinput | 1.29.1 | built | fails in buildPhase | 40 | GNU case ranges | `nanofil: ../src/evdev-frame.h:336: GNU case ranges are not supported, at EVDEV_BTN_DIGI` |
| libjpeg_turbo | 3.1.4 | built | fails in buildPhase | 22 | other syntax or typing gaps | `nanofil: /nix/store/10xdyb6i0ahryz4a85xp747zwkh7g7xw-simde-0.8.2/include/simde/arm/neon/movl.h:54: expected an expression, at typeof` |
| liblc3 | 1.1.3 | built | built | 15 |  |  |
| libmbim | 1.34.0 | tests pass | fails in buildPhase | 51 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| libmhash | 0.9.9.9 | tests pass | tests pass | 139 |  |  |
| libmicrohttpd | 1.0.2 | built | fails in configurePhase | 79 | alignment attributes | `checking for threading lib to use with libmicrohttpd (auto)... configure: error: No threading lib is available. Consider installing pthreads` |
| libmpdclient | 2.24 | tests pass | tests pass | 98 |  |  |
| libopus | 1.6.1 | tests pass | fails in buildPhase | 17 | vector types | `nanofil: ../celt/float_cast.h:68: calls returning bad(vector types) are not supported yet` |
| libpng | 1.6.43 | built | built | 71 |  |  |
| libpq | 18.6 | built | fails in buildPhase | 231 | other builtins | `nanofil: snprintf.c:1365: undeclared identifier __builtin_isinf` |
| libraqm | 0.10.5 | tests pass | tests pass | 14 |  |  |
| libressl | 4.2.1 | tests pass | fails in buildPhase | 43 | inline or top-level asm | `nanofil: /build/libressl-4.2.1/ssl/bio_ssl.c:106: top-level asm is not supported, at (` |
| libseccomp | 2.6.1 | tests pass | fails in buildPhase | 40 | other syntax or typing gaps | `nanofil: arch.c:267: bad offsetof` |
| libselinux | 3.10 | built | built | 151 |  |  |
| libsepol | 3.10 | built | built | 140 |  |  |
| libshout | 2.4.6 | built | built | 86 |  |  |
| libsodium | 1.0.22-unstable-2026-04-09 | tests pass | fails in buildPhase | 153 | alignment attributes | `nanofil: crypto_aead/aegis128l/aegis128l_common.h:201: alignment attributes is not supported` |
| libsoup_3 | 3.6.6 | built | fails in buildPhase | 33 | generic __atomic builtins | `nanofil: libsoup/soup-enum-types.c:24: undeclared identifier __atomic_load` |
| libssh2 | 1.11.1 | built | built | 88 |  |  |
| libtasn1 | 4.21.0 | built | built | 224 |  |  |
| libtiff | 4.7.2 | tests pass | fails in buildPhase | 61 | vector types | `nanofil: /build/source/libtiff/tif_predict.c:605: vector types is not supported` |
| libtirpc | 1.3.7 | tests pass | fails in buildPhase | 70 | K&R definitions | `nanofil: bindresvport.c:60: K&R-style parameter lists are not supported, at ,` |
| liburcu | 0.15.6 | tests pass | fails in configurePhase | 7 | K&R definitions | `configure: error: The compiler does not support C99` |
| libuv | 1.52.1 | built | fails in buildPhase | 72 | other builtins | `nanofil: src/unix/async.c:411: undeclared identifier __builtin_ia32_pause` |
| libvmaf | 3.0.0 | tests pass | tests pass | 129 |  |  |
| libvpx | 1.16.0 | built | fails in buildPhase | 55 | alignment attributes | `nanofil: vpx_dsp/quantize.c:124: member zbin of a type nanofil does not support (alignment attributes)` |
| libwebp | 1.6.0 | built | fails in buildPhase | 23 | vector types | `nanofil: /build/source/sharpyuv/sharpyuv_sse2.c:85: vector types is not supported` |
| libxcrypt | 4.5.2 | built | fails in buildPhase | 124 | constant expressions not folded | `nanofil: lib/crypt.c:40: static assertion is not a constant` |
| libxkbcommon | 1.13.1 | built | fails in buildPhase | 57 | other syntax or typing gaps | `nanofil: ../src/xkbcomp/keycodes.c:306: no member found` |
| libxml2 | 2.15.4 | built | built | 81 |  |  |
| lighttpd | 1.4.85 | built | fails in buildPhase | 209 | constant expressions not folded | `nanofil: server.c:2261: initializer is not a constant` |
| lttng-ust | 2.14.0 | tests fail | not tried |  |  |  |
| lzo | 2.10 | built | built | 288 |  |  |
| mailutils | 3.21 | tests pass | fails in buildPhase | 239 | alignment attributes | `nanofil: amd.c:2059: alignment attributes is not supported` |
| mariadb-connector-c_3_3 | 3.3.5 | built | fails in buildPhase | 97 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: /build/source/plugins/io/remote_io.c:293: __builtin_types_compatible_p is not supported, at (` |
| mbedtls | 3.6.6 | tests pass | fails in buildPhase | 27 | other builtins | `nanofil: /build/source/library/cmac.c:217: undeclared identifier __builtin_assume` |
| minizip | 1.3.2 | built | built | 35 |  |  |
| mpdecimal | 4.0.1 | built | built | 44 |  |  |
| mpfr | 4.2.2 | tests pass | tests pass | 540 |  |  |
| mpg123 | 1.33.7 | dependency fails | not tried |  |  |  |
| netcdf | 4.9.3 | tests pass | fails in buildPhase | 332 | other builtins | `nanofil: dcetab.c:1049: undeclared identifier __builtin_memcpy` |
| nettle | 3.10.2 | tests pass | fails in buildPhase | 444 | constant expressions not folded | `nanofil: ecc-secp224r1.c:212: initializer is not an address constant` |
| nghttp2 | 1.69.0 | built | built | 126 |  |  |
| nspr | 4.40 | tests pass | tests fail | 97 | unresolved Fil-C symbol at link | `../../dist/lib/libnspr4.so: error: undefined reference to 'pizlonated_fegetround'` |
| nss | 3.112.5 | tests pass | fails in buildPhase | 24 | inline or top-level asm | `nanofil: ../../lib/util/secport.c:870: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| oniguruma | 6.9.10 | built | built | 104 |  |  |
| openssh | 10.5p1 | built | fails in buildPhase | 660 | inline or top-level asm | `nanofil: sntrup761.c:62: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| openssl | 3.5.7 | built | fails in buildPhase | 25 | other syntax or typing gaps | `nanofil: crypto/aes/aes_ige.c:72: no member named data` |
| openssl-sarcasm | 3.6.4 | tests pass | fails in buildPhase | 24 | other syntax or typing gaps | `nanofil: crypto/aes/aes_ige.c:72: no member named data` |
| p11-kit | 0.26.2 | built | fails in buildPhase | 118 | constant expressions not folded | `nanofil: ../p11-kit/virtual.c:263: initializer is not a constant` |
| pam | 1.7.2 | built | fails in buildPhase | 87 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: ../libpam/include/pam_inline.h:143: __builtin_types_compatible_p is not supported, at (` |
| pango | 1.56.3 | built | fails in buildPhase | 57 | generic __atomic builtins | `nanofil: pango/pango-enum-types.c:13: undeclared identifier __atomic_load` |
| parted | 3.7 | tests pass | fails in buildPhase | 323 | other syntax or typing gaps | `nanofil: aix.c:211: expected }, at :` |
| pcre2 | 10.48 | built | fails in configurePhase | 56 | alignment attributes | `configure: error: JIT support requires pthreads` |
| perl5 | 5.40.0 | built | fails in buildPhase | 580 | other builtins | `nanofil: universal.c:1144: undeclared identifier __builtin_assume` |
| physfs | 3.2.0 | built | fails in buildPhase | 35 | inline or top-level asm | `nanofil: /build/source/src/physfs_lzmasdk.h:1495: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| pixman | 0.46.4 | built | built | 119 |  |  |
| polkit | 127 | tests pass | fails in buildPhase | 27 | generic __atomic builtins | `nanofil: /nix/store/w2xmld1hsq0ih4k43gjd3llbya9sr3rh-glib-2.80.4-x86_64-unknown-linux-gnufilc0-dev/include/glib-2.0/gobject/gtype.h:2272: undeclared identifier __atomic_load` |
| potrace | 1.16 | tests pass | fails in buildPhase | 61 | K&R definitions | `nanofil: getopt.c:287: K&R-style parameter lists are not supported, at )` |
| procps | 4.0.6 | built | fails in buildPhase | 148 | GNU case ranges | `nanofil: src/ps/parser.c:550: GNU case ranges are not supported, at chr(57)` |
| pth | 2.0.7 | tests pass | tests pass | 111 |  |  |
| pulseaudio | 17.0 | dependency fails | not tried |  |  |  |
| python312 | 3.12.5 | built | fails in buildPhase | 750 | other syntax or typing gaps | `nanofil: ./Modules/readline.c:448: expected an expression, at )` |
| quickjs | 2026-06-04 | tests pass | fails in buildPhase | 5 | alignment attributes | `nanofil: quickjs.c:1802: member malloc_ctx of a type nanofil does not support (alignment attributes)` |
| rdkafka | 2.13.0 | built | fails in buildPhase | 22 | inline or top-level asm | `nanofil: /build/source/src/queue.h:688: inline asm is not supported, except the empty barrier asm volatile("" ::: "memory")` |
| recode | 3.7.15 | tests pass | tests pass | 291 |  |  |
| redis | 8.8.2 | tests pass | fails in buildPhase | 54 | other builtins | `nanofil: ./xxhash.h:3236: undeclared identifier __builtin_assume` |
| rhash | 1.4.6 | tests pass | fails in buildPhase | 6 | alignment attributes | `nanofil: calc_sums.c:564: alignment attributes is not supported` |
| rpcbind | 1.2.6 | built | fails in buildPhase | 19 | K&R definitions | `nanofil: src/rpcinfo.c:358: K&R-style parameter lists are not supported, at ,` |
| rsync | 3.5.0 | tests fail | not tried |  |  |  |
| ruby_3_3 | 3.3.10 | built | fails in buildPhase | 573 | other syntax or typing gaps | `nanofil: ./include/ruby/assert.h:132: expected a declaration, at __declspec` |
| runit | 2.3.1 | tests pass | tests pass | 98 |  |  |
| scrypt | 1.3.3 | built | built | 106 |  |  |
| seatd | 0.9.3 | built | built | 62 |  |  |
| spandsp | 0.0.6 | built | built | 93 |  |  |
| sqlite | 3.51.2 | built | built | 64 |  |  |
| strace | 7.2 | fails in buildPhase | not tried |  |  |  |
| svt-av1 | 3.1.2 | built | fails in buildPhase | 25 | alignment attributes | `nanofil: /build/source/Source/Lib/Codec/inter_prediction.h:42: alignment attributes is not supported` |
| systemd | 256.4 | built | fails in buildPhase | 243 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: ../src/basic/af-list.c:20: __builtin_types_compatible_p is not supported, at (` |
| timidity | 2.15.0 | dependency fails | not tried |  |  |  |
| tinycc | 0.9.27-unstable-2025-01-06 | built | fails in buildPhase | 4 | constant expressions not folded | `nanofil: libtcc.c:1670: initializer is not a constant` |
| tor | 0.4.9.12 | built | fails in buildPhase | 474 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: src/app/main/shutdown.c:74: __builtin_types_compatible_p is not supported, at (` |
| torsocks | 2.5.0 | built | built | 116 |  |  |
| tpm2-abrmd | 3.0.0 | built | fails in configurePhase | 36 | alignment attributes | `configure: error: requires pthread` |
| tpm2-tss | 4.2.0 | built | fails in buildPhase | 91 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: src/tss2-fapi/ifapi_curl.c:423: __builtin_types_compatible_p is not supported, at (` |
| trealla | unstable-2026-09-05 | built | fails in buildPhase | 41 | nanofil internal failure | `nanofil: failed` |
| ttyd | 1.7.7 | built | built | 9 |  |  |
| unbound | 1.26.0 | tests pass | fails in buildPhase | 317 | other syntax or typing gaps | `nanofil: services/rpz.c:247: expected an expression, at attribute` |
| util-linux | 2.42.3 | built | fails in buildPhase | 308 | __builtin_types_compatible_p, __builtin_choose_expr | `nanofil: ./include/list.h:364: __builtin_types_compatible_p is not supported, at (` |
| uwimap | 2007f | built | built | 38 |  |  |
| vala | 0.56.19 | built | fails in buildPhase | 78 | generic __atomic builtins | `nanofil: arraylist.c:875: undeclared identifier __atomic_load` |
| wasm3 | 0.5.0 | built | built | 19 |  |  |
| wavpack | 5.9.0 | built | built | 87 |  |  |
| wayland | 1.25.0 | built | built | 73 |  |  |
| weston | 15.0.1 | built | fails in buildPhase | 104 | constant expressions not folded | `nanofil: ../libweston/renderer-gl/gl-renderer.c:1947: initializer is not a constant` |
| x264 | 0-unstable-2025-01-03 | built | built | 28 |  |  |
| xvidcore | 1.3.7 | built | built | 70 |  |  |
| xz | 5.8.4 | built | fails in buildPhase | 129 | inline or top-level asm | `nanofil: common/common.c:395: top-level asm is not supported, at (` |
| zix | 0.6.2 | tests pass | fails in buildPhase | 14 | other syntax or typing gaps | `nanofil: ../include/zix/allocator.h:36: expected a parameter declaration, at *` |
| zlib | 1.3.2 | tests pass | tests pass | 47 |  |  |
| zlib-ng | 2.2.4 | built | fails in buildPhase | 29 | alignment attributes | `nanofil: /build/zlib-ng-2.2.4/tools/makefixed.c:18: member lens of a type nanofil does not support (alignment attributes)` |
| zstd | 1.5.7 | built | fails in buildPhase | 20 | other builtins | `nanofil: /build/source/lib/common/xxhash.h:3116: undeclared identifier __builtin_assume` |

<!-- end survey table -->
